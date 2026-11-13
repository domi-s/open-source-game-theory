"""Where does each (stated bot, opponent) cell's result come from?

Each cell is resolved by the first of these that applies, and records which one:

``theorem``  the stated bot IS a library bot (same program: ``canonical.program_key``),
             and the library has a theorem for that bot against this opponent. The cell
             is that theorem's value, from ``app/generated/outcome_theorems.json``.
``eval``     Lean evaluated it (``lean_worker.py``): certified, but only where the
             evaluator commits. A verdict of ``stable`` is one answer over the budget
             sweep; ``phase_dependent`` is certified but changes with the budget.
``open``     neither: a blind spot. The cell has no proved value, and is listed in
             ``open_cells.json`` for the app's proof pipeline.

Budgets: every free budget parameter is instantiated with the same ``k`` (the rule the
library's own cells use). A two-parameter bot is therefore the one-parameter family
``k ↦ B k k``, which is how ``PrudentBot2`` lands on the proved ``PrudentBot`` cells. A
budget EXPRESSION written in the program (``2 * k + 64``) belongs to the program: it is
evaluated, never matched to a theorem unless a library bot has the same text.

Identity is STRICT equality of canonical programs, not the tree edit distance in
``app/.../tau/syntax.py``. That distance is deliberately lossy (it erases budgets, so
``.search k`` and ``.search (2*k+64)`` are 0 apart, and it drops the ``.C``/``.D`` action
shorthand, so ``.const .C`` and ``.const .D`` are 0 apart), which is right for a
"how confusable are these two sources" metric and wrong for "may I reuse this bot's
proved outcomes". Distance 0 on a LOSSLESS tree is exactly canonical equality.
"""

from __future__ import annotations

import json
import re
from pathlib import Path

from .canonical import _HEADER_RE, program_key, strip_comments

REPO = Path(__file__).resolve().parents[3]
DEFAULT_BOTS_DIR = REPO / "engine/PrisonersDilemma/Bots"
DEFAULT_THEOREMS = REPO / "app/generated/outcome_theorems.json"

THEOREM, EVAL, OPEN = "theorem", "eval", "open"

_STAGED_RE = re.compile(r"StatedBot\d*")
"""Names the pipeline stages for profiling. Never library bots: a staged copy left behind by an interrupted run would otherwise be 'identical' to itself."""


_SHARED_RE = re.compile(r"[A-Z]\w*(?: k)*")
"""A bot applied to the shared budget: ``B``, ``B k``, ``B k k``. Not ``B (2 * k + 64)``."""


def load_library_programs(bots_dir: Path = DEFAULT_BOTS_DIR) -> dict[str, list[str]]:
    """Library bots by program: canonical key -> the (sorted) names that have it."""
    programs: dict[str, set[str]] = {}
    for path in sorted(bots_dir.rglob("*.lean")):
        text = path.read_text(encoding="utf-8")
        for m in _HEADER_RE.finditer(strip_comments(text)):
            name = m.group("name")
            key = None if _STAGED_RE.fullmatch(name) else program_key(text, name)
            if key is not None:
                programs.setdefault(key, set()).add(name)
    return {key: sorted(names) for key, names in programs.items()}


def load_theorems(path: Path = DEFAULT_THEOREMS) -> dict[tuple[str, str], dict]:
    """The matrix cells by (left bot, right bot), at the SHARED budget.

    A cell's value is for the bots as the theorem instantiates them, so only cells that
    apply every parameter to the same ``k`` can stand for a stated bot (the budget rule,
    ``canonical._rename_budgets``). Budget-staggered companions (``† `` cells) are
    excluded: their value is for a different pair of budgets.
    """
    data = json.loads(path.read_text(encoding="utf-8"))
    return {(t["left_bot"], t["right_bot"]): t for t in data["theorems"]
            if not t["staggered"] and _SHARED_RE.fullmatch(t["left"])
            and _SHARED_RE.fullmatch(t["right"])}


def theorem_cells(twins: list[str], opponents, theorems: dict) -> dict[str, dict]:
    """Cells the library already proves for a bot identical to one of ``twins``.

    The library states each pair in ONE orientation, so a cell may be read off the
    reversed theorem (``outcome opp twin``) with its actions swapped, as the app's own
    matrix does (``tau/matrix.py``: ``outcome A B = (a, b)`` iff ``outcome B A = (b, a)``).
    Such cells say ``swapped`` so they can be audited.
    """
    cells: dict[str, dict] = {}
    for opponent in opponents:
        for twin in twins:
            for left, right, swapped in ((twin, opponent, False), (opponent, twin, True)):
                t = theorems.get((left, right))
                if t is None or not (t["pair"] and all(a in "CD" for a in t["pair"])):
                    continue  # no theorem, or a proven `none` (no actions to take)
                mine, theirs = t["pair"][::-1] if swapped else t["pair"]
                cells[opponent] = {
                    "opponent": opponent, "verdict": "stable", "source": THEOREM,
                    "my_action": mine, "opponent_action": theirs, "by_budget": {},
                    "library_bot": twin, "theorem": t["name"], "regime": t["budget_regime"],
                    "swapped": swapped, "note": f"{t['name']} ({t['budget_regime']})"}
                break
            if opponent in cells:
                break
    return cells


def tag_eval_cell(cell: dict) -> dict:
    """Label a ``lean_worker.py`` cell: ``eval`` if Lean committed (one answer or a
    budget-dependent one), ``open`` if not (undetermined, timed out, over the memory
    cap, or skipped as infeasible)."""
    cell = dict(cell)
    cell["source"] = EVAL if cell["verdict"] in ("stable", "phase_dependent") else OPEN
    return cell
