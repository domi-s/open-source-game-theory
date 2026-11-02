"""Python mirror of the Lean ``Prog`` / ``Formula`` syntax (v0 fragment).

Mirrors ``engine/PrisonersDilemma/Program.lean`` for the constructors an
ordinary bot uses: ``const self opp bot sim ite search`` and the formulas
``plays impl neg box eq``. The TauBots-only constructors (``tvote``, ``sys``,
``selfIdx``) and the meta-only ``diag`` are deliberately NOT represented: the
parser rejects them, so a program that reaches this module is in the fragment.

Budgets are kept SYMBOLIC: a budget is the source text of a Nat expression
(normally the bot's parameter, e.g. ``"k"``). Evaluation never needs a concrete
number -- it works under the large-``k`` reading the outcome matrix uses.

Nodes are frozen dataclasses, so ``==`` is structural syntactic identity: exactly
what Lean's ``.eq`` tests and what zoo-identity detection needs.
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Union

C, D = "C", "D"


# --------------------------------------------------------------------------- Prog
@dataclass(frozen=True)
class Const:
    action: str


@dataclass(frozen=True)
class Self:
    pass


@dataclass(frozen=True)
class Opp:
    pass


@dataclass(frozen=True)
class Bot:
    body: "Prog"


@dataclass(frozen=True)
class Sim:
    player: "Prog"
    opponent: "Prog"


@dataclass(frozen=True)
class Ite:
    guard: "Prog"
    action: str
    then: "Prog"
    els: "Prog"


@dataclass(frozen=True)
class Search:
    budget: str
    formula: "Formula"
    then: "Prog"
    els: "Prog"


Prog = Union[Const, Self, Opp, Bot, Sim, Ite, Search]


# ------------------------------------------------------------------------ Formula
@dataclass(frozen=True)
class Plays:
    player: Prog
    opponent: Prog
    action: str


@dataclass(frozen=True)
class Impl:
    lhs: "Formula"
    rhs: "Formula"


@dataclass(frozen=True)
class Neg:
    body: "Formula"


@dataclass(frozen=True)
class Box:
    budget: str
    body: "Formula"


@dataclass(frozen=True)
class Eq:
    probe: Prog
    target: Prog  # frozen literal: subst never descends here


Formula = Union[Plays, Impl, Neg, Box, Eq]


# ------------------------------------------------------------------- substitution
def subst(p: Prog, me: Prog, opp: Prog) -> Prog:
    """``Prog.subst`` -- one-shot; ``.bot`` is a barrier."""
    if isinstance(p, Self):
        return me
    if isinstance(p, Opp):
        return opp
    if isinstance(p, (Const, Bot)):
        return p
    if isinstance(p, Sim):
        return Sim(subst(p.player, me, opp), subst(p.opponent, me, opp))
    if isinstance(p, Ite):
        return Ite(subst(p.guard, me, opp), p.action,
                   subst(p.then, me, opp), subst(p.els, me, opp))
    if isinstance(p, Search):
        return Search(p.budget, subst_formula(p.formula, me, opp),
                      subst(p.then, me, opp), subst(p.els, me, opp))
    raise TypeError(f"not a Prog: {p!r}")


def subst_formula(f: Formula, me: Prog, opp: Prog) -> Formula:
    """``Formula.subst`` -- the RHS of ``.eq`` is frozen."""
    if isinstance(f, Plays):
        return Plays(subst(f.player, me, opp), subst(f.opponent, me, opp), f.action)
    if isinstance(f, Impl):
        return Impl(subst_formula(f.lhs, me, opp), subst_formula(f.rhs, me, opp))
    if isinstance(f, Neg):
        return Neg(subst_formula(f.body, me, opp))
    if isinstance(f, Box):
        return Box(f.budget, subst_formula(f.body, me, opp))
    if isinstance(f, Eq):
        return Eq(subst(f.probe, me, opp), f.target)
    raise TypeError(f"not a Formula: {f!r}")


# ------------------------------------------------------------ syntactic utilities
def has_search(p: Prog) -> bool:
    """``Prog.hasSearch``: does the program contain a proof-search node?"""
    if isinstance(p, Search):
        return True
    if isinstance(p, Bot):
        return has_search(p.body)
    if isinstance(p, Sim):
        return has_search(p.player) or has_search(p.opponent)
    if isinstance(p, Ite):
        return has_search(p.guard) or has_search(p.then) or has_search(p.els)
    return False


def rename_budgets(p: Prog, mapping: dict[str, str]) -> Prog:
    """Rename identifiers inside budget expressions, everywhere (incl. under ``.bot``).

    Token-level: ``{"k": "kOut"}`` turns ``"2 * k + 64"`` into ``"2 * kOut + 64"``.
    Used to instantiate a definition's parameters with the caller's arguments.
    """
    def b(s: str) -> str:
        return " ".join(
            _wrap(mapping[t]) if t in mapping else t for t in s.split(" ")
        ) if len(s.split(" ")) > 1 else mapping.get(s, s)

    def rp(q: Prog) -> Prog:
        if isinstance(q, (Const, Self, Opp)):
            return q
        if isinstance(q, Bot):
            return Bot(rp(q.body))
        if isinstance(q, Sim):
            return Sim(rp(q.player), rp(q.opponent))
        if isinstance(q, Ite):
            return Ite(rp(q.guard), q.action, rp(q.then), rp(q.els))
        if isinstance(q, Search):
            return Search(b(q.budget), rf(q.formula), rp(q.then), rp(q.els))
        raise TypeError(q)

    def rf(f: Formula) -> Formula:
        if isinstance(f, Plays):
            return Plays(rp(f.player), rp(f.opponent), f.action)
        if isinstance(f, Impl):
            return Impl(rf(f.lhs), rf(f.rhs))
        if isinstance(f, Neg):
            return Neg(rf(f.body))
        if isinstance(f, Box):
            return Box(b(f.budget), rf(f.body))
        if isinstance(f, Eq):
            return Eq(rp(f.probe), rp(f.target))
        raise TypeError(f)

    return rp(p)


def _wrap(expr: str) -> str:
    return expr if " " not in expr else f"( {expr} )"


def budgets(p: Prog) -> set[str]:
    """Every budget expression occurring in ``p`` (incl. under ``.bot``)."""
    out: set[str] = set()

    def wp(q: Prog) -> None:
        if isinstance(q, Bot):
            wp(q.body)
        elif isinstance(q, Sim):
            wp(q.player), wp(q.opponent)
        elif isinstance(q, Ite):
            wp(q.guard), wp(q.then), wp(q.els)
        elif isinstance(q, Search):
            out.add(q.budget)
            wf(q.formula), wp(q.then), wp(q.els)

    def wf(f: Formula) -> None:
        if isinstance(f, Plays):
            wp(f.player), wp(f.opponent)
        elif isinstance(f, Impl):
            wf(f.lhs), wf(f.rhs)
        elif isinstance(f, Neg):
            wf(f.body)
        elif isinstance(f, Box):
            out.add(f.budget)
            wf(f.body)
        elif isinstance(f, Eq):
            wp(f.probe), wp(f.target)

    wp(p)
    return out


def size(p: Prog) -> int:
    """Node count (``Prog.size`` without the numeral costs -- a readability metric)."""
    if isinstance(p, (Const, Self, Opp)):
        return 1
    if isinstance(p, Bot):
        return size(p.body) + 1
    if isinstance(p, Sim):
        return size(p.player) + size(p.opponent) + 1
    if isinstance(p, Ite):
        return size(p.guard) + size(p.then) + size(p.els) + 1
    if isinstance(p, Search):
        return _fsize(p.formula) + size(p.then) + size(p.els) + 2
    raise TypeError(p)


def _fsize(f: Formula) -> int:
    if isinstance(f, (Plays, Eq)):
        a, b = (f.player, f.opponent) if isinstance(f, Plays) else (f.probe, f.target)
        return size(a) + size(b) + 1
    if isinstance(f, Impl):
        return _fsize(f.lhs) + _fsize(f.rhs) + 1
    if isinstance(f, (Neg, Box)):
        return _fsize(f.body) + 1 + (1 if isinstance(f, Box) else 0)
    raise TypeError(f)


# ------------------------------------------------------------------- pretty print
def show(p: Prog, names: dict | None = None) -> str:
    """Single-line Lean rendering.

    ``names`` maps known terms (e.g. zoo instances) to their names, so an inlined
    ``.bot (.const Action.D)`` prints back as ``.bot DefectBot``.
    """
    names = names or {}

    def arg(q: Prog) -> str:
        r = sp(q)
        return r if " " not in r else f"({r})"

    def sp(q: Prog) -> str:
        # fold named terms back, except bare constants (`.const C` reads better
        # than `CooperateBot` in a leaf; under `.bot` the name is used, below)
        if q in names and not isinstance(q, Const):
            return names[q]
        if isinstance(q, Const):
            return f".const Action.{q.action}"
        if isinstance(q, Self):
            return ".self"
        if isinstance(q, Opp):
            return ".opp"
        if isinstance(q, Bot):
            inner = names.get(q.body)
            if inner is None:
                return f".bot {arg(q.body)}"
            return f".bot {inner if ' ' not in inner else f'({inner})'}"
        if isinstance(q, Sim):
            return f".sim {arg(q.player)} {arg(q.opponent)}"
        if isinstance(q, Ite):
            return f".ite {arg(q.guard)} Action.{q.action} {arg(q.then)} {arg(q.els)}"
        if isinstance(q, Search):
            return f".search {_paren(q.budget)} {farg(q.formula)} {arg(q.then)} {arg(q.els)}"
        raise TypeError(q)

    def farg(f: Formula) -> str:
        return f"({sf(f)})"

    def sf(f: Formula) -> str:
        if isinstance(f, Plays):
            return f".plays {arg(f.player)} {arg(f.opponent)} Action.{f.action}"
        if isinstance(f, Impl):
            return f".impl {farg(f.lhs)} {farg(f.rhs)}"
        if isinstance(f, Neg):
            return f".neg {farg(f.body)}"
        if isinstance(f, Box):
            return f".box {_paren(f.budget)} {farg(f.body)}"
        if isinstance(f, Eq):
            return f".eq {arg(f.probe)} {arg(f.target)}"
        raise TypeError(f)

    return sp(p)


def _paren(budget: str) -> str:
    return budget if budget.isidentifier() or budget.isdigit() else f"({budget})"
