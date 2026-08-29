import os
import json
from datetime import datetime, timezone

from flask_sqlalchemy import SQLAlchemy
from sqlalchemy import inspect, text
from sqlalchemy.pool import NullPool
from werkzeug.security import generate_password_hash, check_password_hash

db = SQLAlchemy()


def init_db(app):
    url = os.environ.get("DATABASE_URL", "sqlite:///royalty.db")
    # Neon/Render hand out "postgres://" but SQLAlchemy requires "postgresql://".
    if url.startswith("postgres://"):
        url = url.replace("postgres://", "postgresql://", 1)
    app.config["SQLALCHEMY_DATABASE_URI"] = url
    app.config["SQLALCHEMY_TRACK_MODIFICATIONS"] = False
    # SQLAlchemy's QueuePool uses threading.Condition, which breaks under
    # eventlet ("cannot notify on un-acquired lock"). NullPool opens a fresh
    # connection per use — fine for this app's traffic and eventlet-safe.
    app.config["SQLALCHEMY_ENGINE_OPTIONS"] = {"poolclass": NullPool}
    db.init_app(app)
    with app.app_context():
        db.create_all()
        _migrate(app)


def _migrate(app):
    """Add columns to existing tables that create_all() leaves untouched."""
    inspector = inspect(db.engine)
    user_cols = {c["name"] for c in inspector.get_columns("user")}
    if "reveal_attacked_default" not in user_cols:
        with db.engine.begin() as conn:
            conn.execute(text(
                'ALTER TABLE "user" ADD COLUMN reveal_attacked_default '
                'BOOLEAN NOT NULL DEFAULT false'
            ))
    if "time_limit_default" not in user_cols:
        with db.engine.begin() as conn:
            conn.execute(text(
                'ALTER TABLE "user" ADD COLUMN time_limit_default '
                'INTEGER NOT NULL DEFAULT 0'
            ))


class User(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    username = db.Column(db.String(32), unique=True, nullable=False)  # lowercase, for lookup
    display_name = db.Column(db.String(32), nullable=False)           # original casing
    password_hash = db.Column(db.String(255), nullable=False)
    created_at = db.Column(db.DateTime, default=lambda: datetime.now(timezone.utc))
    # Per-user default for the "Reveal Attacked" room option. Off by default.
    reveal_attacked_default = db.Column(db.Boolean, nullable=False, default=False)
    # Per-user default for the per-turn time limit (seconds; 0 = no limit).
    time_limit_default = db.Column(db.Integer, nullable=False, default=0)

    def set_password(self, pw):
        self.password_hash = generate_password_hash(pw)

    def check_password(self, pw):
        return check_password_hash(self.password_hash, pw)


class GameRecord(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    finished_at = db.Column(db.DateTime, default=lambda: datetime.now(timezone.utc))
    p1_user_id = db.Column(db.Integer, db.ForeignKey("user.id"), nullable=True)
    p2_user_id = db.Column(db.Integer, db.ForeignKey("user.id"), nullable=True)
    p1_name = db.Column(db.String(32), nullable=False)
    p2_name = db.Column(db.String(32), nullable=False)
    p1_score = db.Column(db.Integer, nullable=False)
    p2_score = db.Column(db.Integer, nullable=False)
    winner = db.Column(db.Integer, nullable=True)  # 1, 2, or None for a tie
    vs_bot = db.Column(db.Boolean, default=False)
    boards_json = db.Column(db.Text, nullable=False)  # {"p1": [...units...], "p2": [...]}


class ChallengeContact(db.Model):
    """Records that one user has sent a direct challenge to another, for the quick-pick dropdown."""
    id = db.Column(db.Integer, primary_key=True)
    user_id = db.Column(db.Integer, db.ForeignKey("user.id"), nullable=False)
    opponent_id = db.Column(db.Integer, db.ForeignKey("user.id"), nullable=False)
    last_challenged_at = db.Column(db.DateTime, default=lambda: datetime.now(timezone.utc))


def create_user(username, password):
    """Returns (user, error). error is a user-facing string or None."""
    username = username.strip()
    if not (3 <= len(username) <= 20):
        return None, "Username must be 3-20 characters."
    if not username.replace("_", "").isalnum():
        return None, "Username may only contain letters, numbers, and underscores."
    if len(password) < 6:
        return None, "Password must be at least 6 characters."
    key = username.lower()
    if User.query.filter_by(username=key).first():
        return None, "That username is taken."
    user = User(username=key, display_name=username)
    user.set_password(password)
    db.session.add(user)
    db.session.commit()
    return user, None


def authenticate(username, password):
    user = User.query.filter_by(username=username.strip().lower()).first()
    if user and user.check_password(password):
        return user
    return None


def record_game(p1_user_id, p2_user_id, p1_name, p2_name, p1_score, p2_score, vs_bot, boards):
    if p1_score > p2_score:
        winner = 1
    elif p2_score > p1_score:
        winner = 2
    else:
        winner = None
    rec = GameRecord(
        p1_user_id=p1_user_id, p2_user_id=p2_user_id,
        p1_name=p1_name, p2_name=p2_name,
        p1_score=p1_score, p2_score=p2_score,
        winner=winner, vs_bot=vs_bot,
        boards_json=json.dumps(boards),
    )
    db.session.add(rec)
    db.session.commit()


def _records_for(user_id, since=None):
    q = GameRecord.query.filter(
        (GameRecord.p1_user_id == user_id) | (GameRecord.p2_user_id == user_id)
    )
    if since is not None:
        q = q.filter(GameRecord.finished_at >= since)
    return q.order_by(GameRecord.finished_at.desc())


def user_stats(user_id, since=None):
    wins = losses = ties = 0
    for r in _records_for(user_id, since=since).all():
        is_p1 = r.p1_user_id == user_id
        mine = r.p1_score if is_p1 else r.p2_score
        theirs = r.p2_score if is_p1 else r.p1_score
        if mine > theirs:
            wins += 1
        elif mine < theirs:
            losses += 1
        else:
            ties += 1
    total = wins + losses + ties
    return {"wins": wins, "losses": losses, "ties": ties, "total": total}


def leaderboard(min_games=15, limit=50, since=None):
    """Players ranked by win rate, highest first. Requires min_games played
    to filter out small-sample-size records (e.g. a 1-0 record ranking #1).
    Pass `since` to restrict to games finished on/after that datetime (monthly board)."""
    rows = []
    for u in User.query.all():
        stats = user_stats(u.id, since=since)
        if stats["total"] < min_games:
            continue
        winrate = (stats["wins"] + 0.5 * stats["ties"]) / stats["total"] * 100
        rows.append({
            "username": u.username, "display_name": u.display_name,
            "wins": stats["wins"], "losses": stats["losses"], "ties": stats["ties"],
            "total": stats["total"], "winrate": round(winrate, 1),
        })
    rows.sort(key=lambda p: (-p["winrate"], p["display_name"].lower()))
    return rows[:limit]


def head_to_head(user_id, opp_id):
    """My (user_id) record and games against a specific opponent, from my perspective."""
    games = GameRecord.query.filter(
        ((GameRecord.p1_user_id == user_id) & (GameRecord.p2_user_id == opp_id)) |
        ((GameRecord.p1_user_id == opp_id) & (GameRecord.p2_user_id == user_id))
    ).order_by(GameRecord.finished_at.desc()).all()
    wins = losses = ties = 0
    history = []
    for r in games:
        is_p1 = r.p1_user_id == user_id
        mine = r.p1_score if is_p1 else r.p2_score
        theirs = r.p2_score if is_p1 else r.p1_score
        if mine > theirs:
            wins += 1
        elif mine < theirs:
            losses += 1
        else:
            ties += 1
        boards = json.loads(r.boards_json)
        history.append({
            "finished_at": r.finished_at.isoformat(),
            "you_score": mine,
            "opp_score": theirs,
            "you_board": boards["p1"] if is_p1 else boards["p2"],
            "opp_board": boards["p2"] if is_p1 else boards["p1"],
        })
    stats = {"wins": wins, "losses": losses, "ties": ties, "total": len(games)}
    return stats, history


def opponents_played(user_id):
    """User ids of registered opponents this user has at least one recorded game against."""
    opp_ids = set()
    for r in _records_for(user_id).all():
        other = r.p2_user_id if r.p1_user_id == user_id else r.p1_user_id
        if other and other != user_id:
            opp_ids.add(other)
    return opp_ids


def record_challenge_contact(user_id, opponent_id):
    """Remember that user_id has challenged opponent_id, for the quick-pick dropdown."""
    row = ChallengeContact.query.filter_by(user_id=user_id, opponent_id=opponent_id).first()
    if row:
        row.last_challenged_at = datetime.now(timezone.utc)
    else:
        db.session.add(ChallengeContact(user_id=user_id, opponent_id=opponent_id))
    db.session.commit()


def challenge_contacts(user_id):
    """Users this user has challenged before, most recently challenged first."""
    rows = (ChallengeContact.query.filter_by(user_id=user_id)
            .order_by(ChallengeContact.last_challenged_at.desc()).all())
    out = []
    for row in rows:
        u = db.session.get(User, row.opponent_id)
        if u:
            out.append({"username": u.username, "display_name": u.display_name})
    return out


def all_player_game_counts():
    """Every registered player with their total recorded games, busiest first."""
    out = []
    for u in User.query.order_by(User.display_name).all():
        total = GameRecord.query.filter(
            (GameRecord.p1_user_id == u.id) | (GameRecord.p2_user_id == u.id)
        ).count()
        out.append({"username": u.username, "display_name": u.display_name, "games": total})
    out.sort(key=lambda p: (-p["games"], p["display_name"].lower()))
    return out


def search_players(query, exclude_user_id=None, limit=10):
    """Registered players whose username or display name contains query
    (min 3 chars), busiest (most games played) first."""
    q = (query or "").strip().lower()
    if len(q) < 3:
        return []
    out = []
    for u in User.query.all():
        if u.id == exclude_user_id:
            continue
        if q not in u.username.lower() and q not in u.display_name.lower():
            continue
        total = GameRecord.query.filter(
            (GameRecord.p1_user_id == u.id) | (GameRecord.p2_user_id == u.id)
        ).count()
        out.append({"username": u.username, "display_name": u.display_name, "games": total})
    out.sort(key=lambda p: (-p["games"], p["display_name"].lower()))
    return out[:limit]


def recent_games(limit=5):
    """Most recently finished games across all players, newest first."""
    out = []
    for r in GameRecord.query.order_by(GameRecord.finished_at.desc()).limit(limit).all():
        out.append({
            "finished_at": r.finished_at.isoformat(),
            "p1_name": r.p1_name,
            "p2_name": r.p2_name,
            "p1_score": r.p1_score,
            "p2_score": r.p2_score,
            "winner": r.winner,
            "vs_bot": r.vs_bot,
        })
    return out


def user_history(user_id, limit=10):
    out = []
    for r in _records_for(user_id).limit(limit).all():
        is_p1 = r.p1_user_id == user_id
        boards = json.loads(r.boards_json)
        out.append({
            "finished_at": r.finished_at.isoformat(),
            "opp_name": r.p2_name if is_p1 else r.p1_name,
            "you_score": r.p1_score if is_p1 else r.p2_score,
            "opp_score": r.p2_score if is_p1 else r.p1_score,
            "you_board": boards["p1"] if is_p1 else boards["p2"],
            "opp_board": boards["p2"] if is_p1 else boards["p1"],
            "vs_bot": r.vs_bot,
        })
    return out
