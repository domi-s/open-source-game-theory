"""The bot zoo as Lean source, parsed by the same parser the samples go through.

The definitions are SNAPSHOTS of ``engine/PrisonersDilemma/Bots/**/*.lean``
(comments dropped). ``tests/test_stated.py`` re-parses the engine files when the
engine checkout is present and asserts they produce identical ASTs, so a drift
between this snapshot and the engine fails the tests rather than silently
changing what "is DupocBot" means.

These are the names an LLM-written program may reference (``.bot DupocBot k``,
``CupodBot k`` …). Order matters only in that a def may use earlier ones.
"""

from __future__ import annotations

from functools import lru_cache

from .parse import Definition, parse_file
from .prog import Prog, rename_budgets

ZOO_SOURCE = """
def CooperateBot : Prog := .const Action.C
def DefectBot : Prog := .const Action.D
def MirrorBot : Prog := .sim .opp .self
def TitForTatBot : Prog :=
  .ite (.sim .opp (.bot CooperateBot)) Action.C (.const Action.C) (.const Action.D)
def DBot : Prog :=
  .ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.D) (.const Action.C)
def OBot : Prog :=
  .ite (.sim .opp (.bot CooperateBot)) Action.C
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D)
def EBot : Prog :=
  .ite (.sim .opp (.bot DefectBot)) Action.C
    (.const Action.D)
    (.ite (.sim .opp (.bot CooperateBot)) Action.C
      (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C (.const Action.C) (.const Action.D)))
def DupocBot (k : Nat) : Prog :=
  .search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)
def CupodBot (k : Nat) : Prog :=
  .search k (.plays .opp .self Action.D) (.const Action.D) (.const Action.C)
def CupodTrollBot (k : Nat) : Prog :=
  .search k (.eq .opp (CupodBot k)) (.const Action.D) (.const Action.C)
def PrudentBot (k : Nat) : Prog :=
  .search k (.plays .opp .self Action.C)
    (.search k (.plays .opp (.bot DefectBot) Action.D) (.const Action.C) (.const Action.D))
    (.const Action.D)
def PrudentBot2 (kOut kIn : Nat) : Prog :=
  .search kOut (.plays .opp .self Action.C)
    (.search kIn (.plays .opp (.bot DefectBot) Action.D) (.const Action.C) (.const Action.D))
    (.const Action.D)
def JustBot (k : Nat) : Prog :=
  .search k (.plays .opp (.bot (DupocBot k)) Action.C) (.const Action.C) (.const Action.D)
def JustBot2 (K k : Nat) : Prog :=
  .search K (.plays .opp (.bot (DupocBot k)) Action.C) (.const Action.C) (.const Action.D)
def CIMCIC (k : Nat) : Prog :=
  .search k (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C))
    (.const Action.C) (.const Action.D)
def DIMCID (k : Nat) : Prog :=
  .search k (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.D))
    (.const Action.D) (.const Action.C)
def GuardianBot (k : Nat) : Prog :=
  .search k (.plays .opp (.bot CooperateBot) Action.D) (.const Action.D) (.const Action.C)
def WaryBot (k : Nat) : Prog :=
  .search k (.neg (.plays .opp .self Action.C)) (.const Action.D) (.const Action.C)
def LegibleBot (kOut kIn : Nat) : Prog :=
  .search kOut (.box kIn (.plays .self .opp Action.C)) (.const Action.C) (.const Action.D)
def OptimBot (kOpp kSelf : Nat) : Prog :=
  let rung3 : Prog :=
    .search kOpp (.plays .opp .self Action.D)
      (.search kSelf (.plays .self .opp Action.D) (.const Action.D) (.const Action.C))
      (.const Action.C)
  let rung2 : Prog :=
    .search kOpp (.plays .opp .self Action.C)
      (.search kSelf (.plays .self .opp Action.C) (.const Action.C) rung3)
      rung3
  .search kOpp (.plays .opp .self Action.C)
    (.search kSelf (.plays .self .opp Action.D) (.const Action.D) rung2)
    rung2
"""

# The budget symbol every same-k instance uses (the outcome matrix's convention).
K = "k"


@lru_cache(maxsize=1)
def zoo_scope() -> dict[str, Definition]:
    """Name → parsed definition, for resolving references in samples."""
    return parse_file(ZOO_SOURCE).defs


def instance(name: str, budget: str = K) -> Prog:
    """The zoo bot ``name`` with EVERY budget parameter set to ``budget`` (same-k)."""
    d = zoo_scope()[name]
    return rename_budgets(d.body, {p: budget for p in d.params})


@lru_cache(maxsize=1)
def zoo_names() -> dict[Prog, str]:
    """Same-k zoo instance → display name (``DupocBot k``), for pretty-printing."""
    out = {}
    for name, d in zoo_scope().items():
        if len(d.params) <= 1:
            out[instance(name)] = name if not d.params else f"{name} {K}"
    return out
