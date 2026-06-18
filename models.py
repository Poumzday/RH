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


class User(db.Model):
    id = db.Column(db.Integer, primary_key=True)
    username = db.Column(db.String(32), unique=True, nullable=False)  # lowercase, for lookup
    display_name = db.Column(db.String(32), nullable=False)           # original casing
    password_hash = db.Column(db.String(255), nullable=False)
    created_at = db.Column(db.DateTime, default=lambda: datetime.now(timezone.utc))
    # Per-user default for the "Reveal Attacked" room option. Off by default.
    reveal_attacked_default = db.Column(db.Boolean, nullable=False, default=False)

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


def _records_for(user_id):
    return GameRecord.query.filter(
        (GameRecord.p1_user_id == user_id) | (GameRecord.p2_user_id == user_id)
    ).order_by(GameRecord.finished_at.desc())


def user_stats(user_id):
    wins = losses = ties = 0
    for r in _records_for(user_id).all():
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
