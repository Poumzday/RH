import os
import random
import uuid
import threading
from flask import Flask, render_template, request
from flask_socketio import SocketIO, emit, join_room

app = Flask(__name__)
app.secret_key = os.environ.get("SECRET_KEY", "dev-secret-key")
socketio = SocketIO(app, async_mode="eventlet")

KNIGHT_RANKS = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10"]
BOT_SID = "__bot__"

# All valid (j, q, k) counts where j*1 + q*2 + k*3 = 12, total 4-12 royals
ROYAL_COMBOS = []
for _j in range(0, 13):
    for _q in range(0, 7):
        for _k in range(0, 5):
            if _j * 1 + _q * 2 + _k * 3 == 12 and 4 <= _j + _q + _k <= 12:
                ROYAL_COMBOS.append((_j, _q, _k))

# 12 unique royal visual styles
ROYAL_STYLES = [
    "crimson", "purple", "emerald", "sapphire",
    "obsidian", "rose", "teal", "midnight",
    "forest", "burgundy", "amber", "violet",
]


def card_value(rank):
    if rank == "A":
        return 1
    if rank in ("J", "Q", "K"):
        return 0
    return int(rank)


def is_royal(rank):
    return rank in ("J", "Q", "K")


def royal_points(rank):
    return {"J": 1, "Q": 2, "K": 3}.get(rank, 0)


def make_deck():
    deck = []
    # Knights: 4 copies of each rank, no suits
    for r in KNIGHT_RANKS:
        for _ in range(4):
            deck.append({"rank": r, "suit": "none"})
    # Royals: random combo summing to 12 points, each with unique style
    j_count, q_count, k_count = random.choice(ROYAL_COMBOS)
    styles = list(ROYAL_STYLES)
    random.shuffle(styles)
    style_idx = 0
    for _ in range(j_count):
        deck.append({"rank": "J", "suit": "none", "style": styles[style_idx % len(styles)]})
        style_idx += 1
    for _ in range(q_count):
        deck.append({"rank": "Q", "suit": "none", "style": styles[style_idx % len(styles)]})
        style_idx += 1
    for _ in range(k_count):
        deck.append({"rank": "K", "suit": "none", "style": styles[style_idx % len(styles)]})
        style_idx += 1
    random.shuffle(deck)
    return deck


def make_unit(cards):
    rank = cards[0]["rank"]
    return {
        "cards": list(cards),
        "rank": rank,
        "is_royal": is_royal(rank),
        "power": sum(card_value(c["rank"]) for c in cards),
    }


def unit_to_dict(unit):
    d = {
        "cards": unit["cards"],
        "rank": unit["rank"],
        "is_royal": unit["is_royal"],
        "power": unit["power"],
    }
    return d


def resolve_attack(attacker_unit, board, side):
    steps = []
    to_discard = []

    if side == "right":
        board = list(reversed(board))

    if attacker_unit["is_royal"]:
        if board and board[0]["rank"] == "A":
            # Ace traps the royal — royal replaces ace on board
            defender = board[0]
            to_discard.extend(defender["cards"])
            new_unit = make_unit(attacker_unit["cards"])
            board[0] = new_unit
            new_unit["absorbed"] = new_unit["power"]
            steps.append({
                "defender": unit_to_dict(defender),
                "outcome": "absorbed",
                "remaining_power": 0,
                "absorbed_power": 0,
            })
        elif board:
            victim = board.pop(0)
            to_discard.extend(attacker_unit["cards"])
            to_discard.extend(victim["cards"])
            steps.append({
                "defender": unit_to_dict(victim),
                "outcome": "destroyed",
                "remaining_power": 0,
            })
        else:
            to_discard.extend(attacker_unit["cards"])
            steps.append({"defender": None, "outcome": "no_target", "remaining_power": 0})
    else:
        remaining = attacker_unit["power"]
        attacker_alive = True
        while remaining > 0 and board and attacker_alive:
            defender = board[0]
            if defender["is_royal"]:
                board.pop(0)
                to_discard.extend(defender["cards"])
                to_discard.extend(attacker_unit["cards"])
                steps.append({
                    "defender": unit_to_dict(defender),
                    "outcome": "both_destroyed",
                    "remaining_power": 0,
                })
                attacker_alive = False
                remaining = 0
            elif defender["rank"] == "A":
                # Ace: attacker replaces the Ace on the board. Ace is destroyed.
                to_discard.extend(defender["cards"])  # Ace goes to discard
                new_unit = make_unit(attacker_unit["cards"])
                board[0] = new_unit  # Replace Ace with attacker's cards
                new_unit["absorbed"] = new_unit["power"]
                steps.append({
                    "defender": unit_to_dict(defender),
                    "outcome": "absorbed",
                    "remaining_power": 0,
                    "absorbed_power": new_unit["power"],
                })
                attacker_alive = False
                remaining = 0
            elif remaining > defender["power"]:
                board.pop(0)
                remaining -= defender["power"]
                to_discard.extend(defender["cards"])
                steps.append({
                    "defender": unit_to_dict(defender),
                    "outcome": "destroyed",
                    "remaining_power": remaining,
                })
            elif remaining < defender["power"]:
                to_discard.extend(attacker_unit["cards"])
                steps.append({
                    "defender": unit_to_dict(defender),
                    "outcome": "blocked",
                    "remaining_power": 0,
                })
                attacker_alive = False
                remaining = 0
            else:
                board.pop(0)
                to_discard.extend(defender["cards"])
                to_discard.extend(attacker_unit["cards"])
                steps.append({
                    "defender": unit_to_dict(defender),
                    "outcome": "both_destroyed",
                    "remaining_power": 0,
                })
                attacker_alive = False
                remaining = 0

        if attacker_alive:
            to_discard.extend(attacker_unit["cards"])

    if side == "right":
        board = list(reversed(board))

    return board, to_discard, steps


class Game:
    def __init__(self, game_id):
        self.id = game_id
        self.deck = make_deck()
        self.discard = []
        self.players = []
        self.hands = {}
        self.boards = {}
        self.current_turn_idx = 0
        self.phase = "waiting"
        self.actions_remaining = 0
        self.path = None
        self.deploy_placed_this_action = 0
        self.pending_anim = None
        self.pending_deploy = None
        self.pending_logs = []
        self.mulligan_decisions = {}
        self.turns_taken = {}
        self.has_bot = False

    def add_player(self, sid):
        self.players.append(sid)
        self.hands[sid] = []
        self.boards[sid] = []
        if len(self.players) == 2:
            self.start_game()

    def start_game(self):
        for sid in self.players:
            self.hands[sid] = [self.deck.pop() for _ in range(5)]
        self.phase = "mulligan"

    def mulligan(self, sid, do_mulligan):
        if self.phase != "mulligan":
            return
        if sid in self.mulligan_decisions:
            return
        if do_mulligan:
            old_hand = self.hands[sid]
            self.deck.extend(old_hand)
            random.shuffle(self.deck)
            self.hands[sid] = [self.deck.pop() for _ in range(5)]
        self.mulligan_decisions[sid] = True
        if len(self.mulligan_decisions) == 2:
            self.current_turn_idx = 0
            self.begin_turn()

    def current_player(self):
        return self.players[self.current_turn_idx]

    def opponent_of(self, sid):
        return self.players[1 - self.players.index(sid)]

    def player_number(self, sid):
        return self.players.index(sid) + 1

    def begin_turn(self):
        sid = self.current_player()
        self.turns_taken[sid] = self.turns_taken.get(sid, 0) + 1

        if not self.deck:
            if not self.hands[sid]:
                opp = self.opponent_of(sid)
                if not self.hands[opp]:
                    self.end_game()
                    return
                self.current_turn_idx = 1 - self.current_turn_idx
                self.begin_turn()
                return
            self.phase = "forced_attack"
        else:
            if self.turns_taken[sid] > 1:
                card = self.deck.pop()
                self.hands[sid].append(card)
            self.path = "A"
            self.actions_remaining = 1
            self.phase = "action"

    def switch_to_path_b(self, sid):
        if sid != self.current_player() or self.phase != "action":
            return
        if self.path != "A":
            return
        if len(self.hands[sid]) < 2:
            return
        self.path = "B"
        self.phase = "discard_for_b"

    def discard_cards(self, sid, indices):
        if sid != self.current_player() or self.phase != "discard_for_b":
            return
        if len(indices) != 2:
            return
        indices = sorted(set(indices), reverse=True)
        if len(indices) != 2:
            return
        if any(i < 0 or i >= len(self.hands[sid]) for i in indices):
            return
        for i in indices:
            card = self.hands[sid].pop(i)
            self.discard.append(card)
        self.actions_remaining = 2
        self.phase = "action"

    def deploy(self, sid, card_indices, side):
        if sid != self.current_player():
            return
        if self.phase not in ("action", "deploy"):
            return
        hand = self.hands[sid]
        card_indices = list(set(card_indices))
        if any(i < 0 or i >= len(hand) for i in card_indices):
            return
        if not card_indices:
            return
        cards = [hand[i] for i in card_indices]
        if len(set(c["rank"] for c in cards)) != 1:
            return
        unit = make_unit(cards)
        board = self.boards[sid]
        if side == "left":
            board.insert(0, unit)
        else:
            board.append(unit)
        pn = self.player_number(sid)
        self.pending_deploy = {
            "side": side,
            "player": pn,
            "card_count": len(cards),
        }
        self.pending_logs.append(f"Player {pn} deployed on {side}")
        for i in sorted(card_indices, reverse=True):
            hand.pop(i)
        if self.phase == "action":
            self.deploy_placed_this_action = 1
            units_before = len(board) - 1
            if units_before < 3 and len(board) < 3 and hand:
                self.phase = "deploy"
                return
            self.actions_remaining -= 1
            self.deploy_placed_this_action = 0
            self.check_end_actions()
        elif self.phase == "deploy":
            self.deploy_placed_this_action += 1
            if len(board) < 3 and hand:
                return
            self.actions_remaining -= 1
            self.deploy_placed_this_action = 0
            self.check_end_actions()

    def finish_deploy(self, sid):
        if sid != self.current_player() or self.phase != "deploy":
            return
        self.actions_remaining -= 1
        self.deploy_placed_this_action = 0
        self.phase = "action"
        self.check_end_actions()

    def attack(self, sid, card_indices, side):
        if sid != self.current_player():
            return
        if self.phase not in ("action", "forced_attack"):
            return
        hand = self.hands[sid]
        card_indices = list(set(card_indices))
        if any(i < 0 or i >= len(hand) for i in card_indices):
            return
        if not card_indices:
            return
        cards = [hand[i] for i in card_indices]
        if len(set(c["rank"] for c in cards)) != 1:
            return
        unit = make_unit(cards)
        opp = self.opponent_of(sid)
        new_board, to_discard, steps = resolve_attack(unit, self.boards[opp], side)
        self.boards[opp] = new_board
        self.discard.extend(to_discard)
        for i in sorted(card_indices, reverse=True):
            hand.pop(i)
        self.pending_anim = {
            "attacker": unit_to_dict(unit),
            "side": side,
            "attacker_player": self.player_number(sid),
            "steps": steps,
        }
        # Wait for player to click "End Turn"
        self.actions_remaining = 0
        self.phase = "turn_over"

    def pick_discard(self, sid):
        if sid != self.current_player() or self.phase != "action":
            return
        if self.actions_remaining < 2:
            return
        if not self.discard:
            return
        card = self.discard.pop()
        self.hands[sid].append(card)
        self.actions_remaining = 0
        self.check_end_actions()

    def pass_action(self, sid):
        if sid != self.current_player() or self.phase != "action":
            return
        self.pending_logs.append(f"Player {self.player_number(sid)} passed")
        self.actions_remaining = 0
        self.check_end_actions()

    def check_end_actions(self):
        if self.actions_remaining <= 0:
            self.phase = "turn_over"
        else:
            self.phase = "action"

    def confirm_end_turn(self, sid):
        if sid != self.current_player():
            return
        if self.phase == "turn_over":
            # Check hand size limit
            if len(self.hands[sid]) > 10:
                self.phase = "discard_excess"
                return
            self.end_turn()
        elif self.phase == "discard_excess":
            # Only end turn if hand is at 10 or less
            if len(self.hands[sid]) <= 10:
                self.end_turn()

    def discard_excess_cards(self, sid, indices):
        if sid != self.current_player() or self.phase != "discard_excess":
            return
        if not indices:
            return
        indices = sorted(set(indices), reverse=True)
        if any(i < 0 or i >= len(self.hands[sid]) for i in indices):
            return
        for i in indices:
            card = self.hands[sid].pop(i)
            self.discard.append(card)
        if len(self.hands[sid]) <= 10:
            self.end_turn()

    def end_turn(self):
        self.current_turn_idx = 1 - self.current_turn_idx
        self.path = None
        self.deploy_placed_this_action = 0
        self.begin_turn()

    def end_game(self):
        self.phase = "game_over"
        self.scores = {}
        self.board_reveals = {}
        for sid in self.players:
            total = 0
            reveal = []
            for unit in self.boards[sid]:
                pts = 0
                if unit["is_royal"]:
                    for c in unit["cards"]:
                        pts += royal_points(c["rank"])
                total += pts
                reveal.append({
                    "cards": unit["cards"],
                    "rank": unit["rank"],
                    "is_royal": unit["is_royal"],
                    "power": unit["power"],
                    "points": pts,
                })
            self.scores[sid] = total
            self.board_reveals[sid] = reveal

    def get_state_for(self, sid):
        opp = self.opponent_of(sid) if len(self.players) == 2 else None
        your_turn = len(self.players) == 2 and self.current_player() == sid

        available = []
        if self.phase == "mulligan":
            if sid not in self.mulligan_decisions:
                available.append("mulligan")
        elif your_turn and self.phase == "action":
            available.append("deploy")
            if opp and self.boards[opp]:
                available.append("attack")
            if self.actions_remaining >= 2 and self.discard:
                available.append("pick_discard")
            available.append("pass")
            if self.path == "A":
                available.append("switch_path_b")
        elif your_turn and self.phase == "deploy":
            available.append("deploy")
            available.append("finish_deploy")
        elif your_turn and self.phase == "forced_attack":
            available.append("attack")
        elif your_turn and self.phase == "discard_for_b":
            available.append("discard")
        elif your_turn and self.phase == "turn_over":
            available.append("end_turn")
        elif your_turn and self.phase == "discard_excess":
            available.append("discard_excess")

        opp_board_visible = []
        if opp:
            for unit in self.boards[opp]:
                if self.phase == "game_over":
                    opp_board_visible.append({
                        "cards": unit["cards"], "rank": unit["rank"],
                        "is_royal": unit["is_royal"], "power": unit["power"],
                        "revealed": True,
                    })
                else:
                    opp_board_visible.append({"card_count": len(unit["cards"]), "revealed": False})

        state = {
            "phase": self.phase,
            "your_turn": your_turn,
            "player_number": self.player_number(sid),
            "hand": self.hands.get(sid, []),
            "board": self.boards.get(sid, []),
            "opponent_board": opp_board_visible,
            "opponent_hand_count": len(self.hands[opp]) if opp else 0,
            "deck_count": len(self.deck),
            "discard_top": self.discard[-1] if self.discard else None,
            "discard_count": len(self.discard),
            "actions_remaining": self.actions_remaining,
            "path": self.path,
            "available_actions": available,
            "can_path_b": len(self.hands.get(sid, [])) >= 2,
            "mulligan_waiting": self.phase == "mulligan" and sid in self.mulligan_decisions,
        }

        if self.phase == "game_over":
            state["scores"] = {
                "you": self.scores.get(sid, 0),
                "opponent": self.scores.get(opp, 0) if opp else 0,
            }
            state["your_board_reveal"] = self.board_reveals.get(sid, [])
            state["opp_board_reveal"] = self.board_reveals.get(opp, []) if opp else []

        return state


# --- Bot logic ---

def _bot_hand_groups(hand):
    """Group hand cards by rank, return dict of rank -> list of indices."""
    groups = {}
    for i, c in enumerate(hand):
        groups.setdefault(c["rank"], []).append(i)
    return groups


def _sim_attack(attacker_unit, board, side):
    """Simulate an attack and return (units_destroyed, royals_killed, attacker_survives)."""
    test_board = [dict(u) for u in (reversed(board) if side == "right" else board)]
    destroyed = 0
    royals_killed = 0
    attacker_survives = False

    if attacker_unit["is_royal"]:
        if test_board:
            victim = test_board[0]
            destroyed = 1
            if victim["is_royal"]:
                royals_killed = 1
        return destroyed, royals_killed, False

    remaining = attacker_unit["power"]
    alive = True
    for defender in test_board:
        if not alive or remaining <= 0:
            break
        if defender["is_royal"]:
            destroyed += 1
            royals_killed += 1
            alive = False
        elif defender["rank"] == "A":
            # Attacker replaces ace — attacker ends up on board (good!)
            destroyed += 1
            attacker_survives = True
            alive = False
        elif remaining > defender["power"]:
            remaining -= defender["power"]
            destroyed += 1
        elif remaining == defender["power"]:
            destroyed += 1
            alive = False
        else:
            alive = False

    if alive:
        attacker_survives = False  # carried through but no more targets
    return destroyed, royals_killed, attacker_survives


def _board_value(board):
    """Score a board: royals are very valuable, non-royals have defensive value."""
    val = 0
    for u in board:
        if u["is_royal"]:
            val += royal_points(u["rank"]) * 10  # royals are the scoring pieces
        else:
            val += u["power"]  # defenders have utility value
    return val


def bot_act(game):
    """Smart bot that tries to win."""
    sid = BOT_SID
    if sid not in game.players:
        return

    hand = game.hands.get(sid, [])

    if game.phase == "mulligan" and sid not in game.mulligan_decisions:
        # Mulligan if no royals in hand
        has_royal = any(is_royal(c["rank"]) for c in hand)
        game.mulligan(sid, not has_royal)
        broadcast_state(game)
        return

    if game.current_player() != sid:
        return

    if game.phase == "action":
        _bot_action(game, sid, hand)
        broadcast_state(game)

    elif game.phase == "deploy":
        _bot_deploy_more(game, sid, hand)
        broadcast_state(game)

    elif game.phase == "forced_attack":
        if hand:
            _bot_smart_attack(game, sid, hand)
        broadcast_state(game)

    elif game.phase == "turn_over":
        game.confirm_end_turn(sid)
        broadcast_state(game)

    elif game.phase == "discard_excess":
        _bot_smart_discard_excess(game, sid, hand)
        broadcast_state(game)


def _bot_action(game, sid, hand):
    """Decide the best action to take."""
    if not hand:
        game.pass_action(sid)
        return

    opp = game.opponent_of(sid)
    opp_board = game.boards.get(opp, [])
    my_board = game.boards.get(sid, [])
    groups = _bot_hand_groups(hand)

    # Priority 1: Deploy royals for protection (put them behind defenders)
    royals_in_hand = [r for r in groups if is_royal(r)]
    non_royals_on_board = [u for u in my_board if not u["is_royal"]]

    if royals_in_hand and len(my_board) >= 1:
        # Deploy a royal, protected in the middle of the board
        rank = max(royals_in_hand, key=lambda r: royal_points(r))
        indices = groups[rank]
        # Put royals on the side with more defenders
        left_defenders = sum(1 for u in my_board[:len(my_board)//2+1] if not u["is_royal"])
        right_defenders = sum(1 for u in my_board[len(my_board)//2:] if not u["is_royal"])
        side = "left" if right_defenders >= left_defenders else "right"
        game.deploy(sid, indices, side)
        return

    # Priority 2: Attack if we can destroy opponent's royals or clear their board
    best_attack = None
    best_score = -999

    if opp_board:
        for rank, idxs in groups.items():
            unit = make_unit([hand[i] for i in idxs])
            for side in ["left", "right"]:
                destroyed, royals_killed, survives = _sim_attack(unit, opp_board, side)
                # Score: heavily reward killing royals, reward destroying units
                score = royals_killed * 20 + destroyed * 3
                if survives:
                    score += 5  # ace replacement is great
                # Penalize attacking with royals (they die)
                if unit["is_royal"]:
                    score -= royal_points(rank) * 8
                # Penalize using high-value knights to kill low-value targets
                if not unit["is_royal"] and destroyed == 0:
                    score -= 10  # blocked, wasted cards
                if score > best_score:
                    best_score = score
                    best_attack = (idxs, side)

    # Priority 3: Deploy non-royal units as defenders
    knights_in_hand = [r for r in groups if not is_royal(r) and r != "A"]

    # Decide: attack or deploy?
    should_attack = best_attack and best_score > 2
    should_deploy = knights_in_hand and len(my_board) < 4

    # If no royals on board yet, prioritize deploying defenders first
    royals_on_board = [u for u in my_board if u["is_royal"]]
    if royals_in_hand and not non_royals_on_board:
        # Need defenders before deploying royals — deploy a knight
        if knights_in_hand:
            rank = max(knights_in_hand, key=lambda r: card_value(r) * len(groups[r]))
            indices = groups[rank]
            side = random.choice(["left", "right"])
            game.deploy(sid, indices, side)
            return

    if should_attack and (best_score > 5 or not should_deploy):
        game.attack(sid, best_attack[0], best_attack[1])
        return

    if should_deploy:
        # Deploy highest combined-power knight group as defender
        rank = max(knights_in_hand, key=lambda r: card_value(r) * len(groups[r]))
        indices = groups[rank]
        side = random.choice(["left", "right"])
        game.deploy(sid, indices, side)
        return

    # Deploy aces as cheap defenders if nothing better
    if "A" in groups and len(my_board) < 5:
        game.deploy(sid, groups["A"], random.choice(["left", "right"]))
        return

    # If we have a decent attack, take it
    if best_attack and best_score > -5:
        game.attack(sid, best_attack[0], best_attack[1])
        return

    game.pass_action(sid)


def _bot_deploy_more(game, sid, hand):
    """During deploy phase, decide whether to deploy more or finish."""
    groups = _bot_hand_groups(hand)
    my_board = game.boards.get(sid, [])

    # Deploy royals if we have defenders already
    royals_in_hand = [r for r in groups if is_royal(r)]
    non_royals_on_board = [u for u in my_board if not u["is_royal"]]

    if royals_in_hand and non_royals_on_board:
        rank = max(royals_in_hand, key=lambda r: royal_points(r))
        # Place between defenders
        side = "left" if len(my_board) > 1 else "right"
        game.deploy(sid, groups[rank], side)
        return

    # Deploy knights if board is small
    knights = [r for r in groups if not is_royal(r) and r != "A"]
    if knights and len(my_board) < 3:
        rank = max(knights, key=lambda r: card_value(r) * len(groups[r]))
        game.deploy(sid, groups[rank], random.choice(["left", "right"]))
        return

    game.finish_deploy(sid)


def _bot_smart_attack(game, sid, hand):
    """Choose the best attack during forced_attack phase."""
    opp = game.opponent_of(sid)
    opp_board = game.boards.get(opp, [])
    groups = _bot_hand_groups(hand)

    best_attack = None
    best_score = -9999

    for rank, idxs in groups.items():
        unit = make_unit([hand[i] for i in idxs])
        for side in ["left", "right"]:
            if opp_board:
                destroyed, royals_killed, survives = _sim_attack(unit, opp_board, side)
                score = royals_killed * 20 + destroyed * 3
                if survives:
                    score += 5
                if unit["is_royal"]:
                    score -= royal_points(rank) * 8
                if destroyed == 0:
                    score -= 5
            else:
                score = 0
                # Prefer attacking with lowest value cards when no board
                if unit["is_royal"]:
                    score -= royal_points(rank) * 10
                else:
                    score -= unit["power"]

            if score > best_score:
                best_score = score
                best_attack = (idxs, side)

    if best_attack:
        game.attack(sid, best_attack[0], best_attack[1])
    else:
        # Fallback: attack with first available
        rank = list(groups.keys())[0]
        game.attack(sid, groups[rank], "left")


def _bot_smart_discard_excess(game, sid, hand):
    """Discard least valuable cards when over hand limit."""
    excess = len(hand) - 10
    if excess <= 0:
        return
    # Score each card: royals are most valuable, then high knights, aces least
    def card_keep_value(i):
        c = hand[i]
        if is_royal(c["rank"]):
            return 100 + royal_points(c["rank"])
        return card_value(c["rank"])

    scored = sorted(range(len(hand)), key=card_keep_value)
    # Discard the lowest-scored cards
    indices = scored[:excess]
    game.discard_excess_cards(sid, indices)


def schedule_bot(game):
    """Schedule a bot move after a short delay."""
    if not game.has_bot or BOT_SID not in game.players:
        return
    needs_move = False
    if game.phase == "mulligan" and BOT_SID not in game.mulligan_decisions:
        needs_move = True
    elif game.phase != "game_over" and game.current_player() == BOT_SID:
        needs_move = True
    if needs_move:
        def _do():
            socketio.sleep(1)
            bot_act(game)
        socketio.start_background_task(_do)


# --- Server state ---
games = {}
player_game = {}
rooms = {}  # room_code -> game_id


def generate_room_code():
    chars = "ABCDEFGHJKLMNPQRSTUVWXYZ23456789"
    return "".join(random.choice(chars) for _ in range(4))


def broadcast_state(game):
    anim = game.pending_anim
    game.pending_anim = None
    deploy = game.pending_deploy
    game.pending_deploy = None
    logs = game.pending_logs
    game.pending_logs = []
    for sid in game.players:
        if sid == BOT_SID:
            continue
        st = game.get_state_for(sid)
        if anim:
            st["attack_anim"] = anim
        if deploy:
            st["deploy_anim"] = deploy
        if logs:
            st["event_logs"] = logs
        socketio.emit("game_state", st, to=sid)
    # Schedule bot move if needed
    schedule_bot(game)


@app.route("/")
def index():
    return render_template("index.html")


@socketio.on("create_room")
def on_create_room():
    sid = request.sid
    code = generate_room_code()
    while code in rooms:
        code = generate_room_code()
    game_id = str(uuid.uuid4())[:8]
    game = Game(game_id)
    game.add_player(sid)
    games[game_id] = game
    rooms[code] = game_id
    join_room(game.id)
    player_game[sid] = game_id
    socketio.emit("room_created", {"room_code": code}, to=sid)


@socketio.on("join_room_code")
def on_join_room(data):
    sid = request.sid
    code = (data.get("code") or "").strip().upper()
    if code not in rooms:
        socketio.emit("join_error", {"msg": "Room not found"}, to=sid)
        return
    game_id = rooms[code]
    if game_id not in games:
        del rooms[code]
        socketio.emit("join_error", {"msg": "Room expired"}, to=sid)
        return
    game = games[game_id]
    if len(game.players) >= 2:
        socketio.emit("join_error", {"msg": "Room is full"}, to=sid)
        return
    game.add_player(sid)
    join_room(game.id)
    player_game[sid] = game_id
    del rooms[code]
    broadcast_state(game)


@socketio.on("join_bot")
def on_join_bot():
    sid = request.sid
    game_id = str(uuid.uuid4())[:8]
    game = Game(game_id)
    game.has_bot = True
    game.add_player(sid)  # Human is player 1
    game.add_player(BOT_SID)  # Bot is player 2
    games[game_id] = game
    join_room(game.id)
    player_game[sid] = game_id
    broadcast_state(game)


@socketio.on("mulligan")
def on_mulligan(data):
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.mulligan(sid, data.get("do_mulligan", False))
    broadcast_state(game)


@socketio.on("switch_to_path_b")
def on_switch_path_b():
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.switch_to_path_b(sid)
    broadcast_state(game)


@socketio.on("discard_cards")
def on_discard(data):
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.discard_cards(sid, data.get("indices", []))
    broadcast_state(game)


@socketio.on("deploy")
def on_deploy(data):
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.deploy(sid, data.get("card_indices", []), data.get("side", "right"))
    broadcast_state(game)


@socketio.on("finish_deploy")
def on_finish_deploy():
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.finish_deploy(sid)
    broadcast_state(game)


@socketio.on("attack")
def on_attack(data):
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.attack(sid, data.get("card_indices", []), data.get("side", "left"))
    broadcast_state(game)


@socketio.on("pick_discard")
def on_pick_discard():
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.pick_discard(sid)
    broadcast_state(game)


@socketio.on("pass_action")
def on_pass():
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.pass_action(sid)
    broadcast_state(game)


@socketio.on("end_turn")
def on_end_turn():
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.confirm_end_turn(sid)
    broadcast_state(game)


@socketio.on("discard_excess")
def on_discard_excess(data):
    sid = request.sid
    game = games.get(player_game.get(sid))
    if not game:
        return
    game.discard_excess_cards(sid, data.get("indices", []))
    broadcast_state(game)


@socketio.on("disconnect")
def on_disconnect():
    sid = request.sid
    game_id = player_game.pop(sid, None)
    if not game_id or game_id not in games:
        return
    game = games[game_id]
    if sid in game.players:
        for p in game.players:
            if p != sid and p != BOT_SID:
                socketio.emit("opponent_left", to=p)
        to_del = [c for c, gid in rooms.items() if gid == game_id]
        for c in to_del:
            del rooms[c]
        del games[game_id]


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8080))
    debug = os.environ.get("RENDER") is None  # debug only when local
    socketio.run(app, host="0.0.0.0", port=port, debug=debug, allow_unsafe_werkzeug=True)
