"""Profile a parsed program against the library -- a SOUND but PARTIAL evaluator.

Python cannot run Lean's proof oracle (``proofSearch`` is ``noncomputable``), so
this evaluator answers a cell only when it can justify the answer, and otherwise
says ``undetermined``. It mirrors ``Dynamics.eval`` (fuel = recursion depth,
``subst`` at every ``.sim`` frame and before every oracle call) and decides
``.search`` guards with three rules, all under the outcome matrix's reading
(same budget ``k`` on both sides, ``k`` sufficiently large):

1. **Soundness (any k).** If the guard formula's TRUTH can be computed and it is
   false, ``S`` cannot prove it, so the search fails. (``proofSearch_sound``.)
2. **Search-free completeness (large k).** A true ``.plays`` atom (or its
   negation, or an ``.eq``) whose programs are search-free has a structural
   certificate, so the search succeeds once ``k`` exceeds its cost
   (``atom_complete_searchfree``, ``eqRefl``/``eqNeg``, ``atomNeg``).
3. **Matrix frames.** When a simulation frame is *player = library bot*,
   *opponent = library bot* (each possibly ``.bot``-wrapped, both at budget ``k``)
   and the direct evaluation is undetermined, the frame's action is read from the
   reference matrix. Truth only -- it is used for frames and for rule 1, never as
   evidence of PROVABILITY (that would fake the floor: DupocBot cannot prove
   DBot cooperates, although DBot does).

Anything else that reaches the oracle -- a true formula about a searching
program, an implication, a ``.box`` -- is undetermined. Self-referential Löbian
cooperation (DupocBot-style guards about ``.self``) is therefore NOT derivable
here; the one exception is a sample that is syntactically a library bot, whose
row is read from the matrix directly ("zoo identity").

Non-termination is detected exactly: a repeated ``(me, opponent, body)`` state on
one evaluation path loops forever at every fuel (``eval`` is deterministic), so
the cell is ``N``. Fuel exhaustion WITHOUT a detected loop is ``undetermined``.
"""

from __future__ import annotations

import sys
from dataclasses import dataclass, field

from .prog import (
    C, D, Bot, Box, Const, Eq, Formula, Impl, Ite, Neg, Opp, Plays, Prog, Search,
    Self, Sim, has_search, rename_budgets, subst, subst_formula,
)
from .zoo import K, instance

NONTERMINATING = "N"


class Undetermined(Exception):
    pass


class _Loop(Exception):
    pass


class _FuelOut(Exception):
    pass


@dataclass(frozen=True)
class Cell:
    """One profile cell: ``value`` in {"C", "D", "N"} or None (undetermined)."""

    value: str | None
    provenance: tuple[str, ...] = ()
    reason: str = ""


@dataclass
class MatrixOracle:
    """Library bots (instantiated at budget ``k``) and their row actions."""

    bots: tuple[str, ...]
    actions: dict[tuple[str, str], str]  # (row bot, opponent) -> row action
    _by_term: dict[Prog, str] = field(init=False)

    def __post_init__(self) -> None:
        self._by_term = {instance(b): b for b in self.bots}

    @classmethod
    def from_library(cls, bots, R) -> "MatrixOracle":
        acts = {(a, b): (C if R[i, j] >= 0.5 else D)
                for i, a in enumerate(bots) for j, b in enumerate(bots)}
        return cls(tuple(bots), acts)

    def name_of(self, p: Prog, unwrap: bool = False) -> str | None:
        """Library name of ``p`` by exact syntax (``unwrap``: ignore outer ``.bot``s)."""
        while unwrap and isinstance(p, Bot):
            p = p.body
        return self._by_term.get(p)

    def frame(self, me: Prog, opp: Prog) -> str | None:
        # `.bot X` probes are behaviourally X (`.bot` just unwraps): the one
        # approximation in this module, used only after direct evaluation failed.
        a, b = self.name_of(me, unwrap=True), self.name_of(opp, unwrap=True)
        return self.actions.get((a, b)) if a and b else None


class Evaluator:
    def __init__(self, oracle: MatrixOracle, fuel: int = 300):
        self.matrix = oracle
        self.fuel = fuel
        self.flags: set[str] = set()
        self._active_guards: set[Formula] = set()
        sys.setrecursionlimit(max(sys.getrecursionlimit(), 20 * fuel + 1000))

    # ---------------------------------------------------------------- core eval
    def _eval(self, n: int, me: Prog, opp: Prog, body: Prog, path: frozenset) -> str:
        if n == 0:
            raise _FuelOut()
        state = (me, opp, body)
        if state in path:
            raise _Loop()
        path = path | {state}
        if isinstance(body, Const):
            return body.action
        if isinstance(body, Self):
            return self._eval(n - 1, me, opp, me, path)
        if isinstance(body, Opp):
            return self._eval(n - 1, me, opp, opp, path)
        if isinstance(body, Bot):
            return self._eval(n - 1, me, opp, body.body, path)
        if isinstance(body, Sim):
            p2, q2 = subst(body.player, me, opp), subst(body.opponent, me, opp)
            return self._frame(n - 1, p2, q2, path)
        if isinstance(body, Ite):
            r = self._eval(n - 1, me, opp, body.guard, path)
            branch = body.then if r == body.action else body.els
            return self._eval(n - 1, me, opp, branch, path)
        if isinstance(body, Search):
            phi = subst_formula(body.formula, me, opp)
            branch = body.then if self._provable(phi) else body.els
            return self._eval(n - 1, me, opp, branch, path)
        raise TypeError(body)

    def _frame(self, n: int, me: Prog, opp: Prog, path: frozenset) -> str:
        """A new player frame; falls back to the matrix when undetermined."""
        try:
            return self._eval(n, me, opp, me, path)
        except Undetermined:
            a = self.matrix.frame(me, opp)
            if a is None:
                raise
            self.flags.add("matrix-frame")
            return a

    # ------------------------------------------------------------------ oracle
    def _provable(self, phi: Formula) -> bool:
        if phi in self._active_guards:  # the guard is about its own outcome
            raise Undetermined("self-referential guard (Löb territory)")
        self._active_guards.add(phi)
        try:
            truth = self._truth(phi)
            if truth is False:
                self.flags.add("sound-refutation")
                return False
            if truth is True and self._complete(phi):
                self.flags.add("large-k-certificate")
                return True
            raise Undetermined(f"cannot decide provability of a true formula "
                               f"({type(phi).__name__})")
        finally:
            self._active_guards.discard(phi)

    def _truth(self, phi: Formula) -> bool | None:
        """Truth of a closed formula, or None when it cannot be computed."""
        if isinstance(phi, Eq):
            return phi.probe == phi.target
        if isinstance(phi, Plays):
            try:
                return self.play(phi.player, phi.opponent) == phi.action
            except Undetermined:
                return None
        if isinstance(phi, Neg):
            t = self._truth(phi.body)
            return None if t is None else not t
        if isinstance(phi, Impl):
            a = self._truth(phi.lhs)
            if a is False:
                return True
            b = self._truth(phi.rhs)
            if b is True:
                return True
            return None if a is None or b is None else (not a) or b
        return None  # .box: truth IS provability

    @staticmethod
    def _complete(phi: Formula) -> bool:
        """Formulas S provably proves whenever true (at large k)."""
        if isinstance(phi, Eq):
            return True
        if isinstance(phi, Neg):
            phi = phi.body
        return (isinstance(phi, Plays)
                and not has_search(phi.player) and not has_search(phi.opponent))

    # ------------------------------------------------------------- entry points
    def play(self, me: Prog, opp: Prog) -> str:
        """``play`` with an action, ``"N"`` for a loop; raises Undetermined."""
        try:
            return self._frame(self.fuel, me, opp, frozenset())
        except _Loop:
            return NONTERMINATING
        except _FuelOut:
            raise Undetermined("fuel exhausted without a detected loop")


def same_k(program: Prog, params: tuple[str, ...]) -> Prog:
    """Instantiate every budget parameter with the shared symbol ``k``."""
    return rename_budgets(program, {p: K for p in params})


def profile(program: Prog, params: tuple[str, ...], oracle: MatrixOracle,
            fuel: int = 300) -> dict[str, Cell]:
    """The program's own action against every library bot (same-k convention)."""
    me = same_k(program, params)
    zoo_name = oracle.name_of(me)
    cells: dict[str, Cell] = {}
    for opp_name in oracle.bots:
        if zoo_name is not None:
            cells[opp_name] = Cell(oracle.actions[(zoo_name, opp_name)],
                                   ("zoo-identity",), f"syntactically {zoo_name}")
            continue
        ev = Evaluator(oracle, fuel)
        try:
            value = ev.play(me, instance(opp_name))
            cells[opp_name] = Cell(value, tuple(sorted(ev.flags)))
        except Undetermined as exc:
            cells[opp_name] = Cell(None, tuple(sorted(ev.flags)), str(exc))
    return cells
