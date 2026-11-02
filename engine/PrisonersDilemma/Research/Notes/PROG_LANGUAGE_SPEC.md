# `Prog` — Language Specification

*Status: reference spec, written 2026-11-02 against `Program.lean` and `Dynamics.lean`.
Audience: an LLM (or a human) that must WRITE a `Prog` program — a bot for the
open-source one-shot Prisoner's Dilemma — that compiles and behaves as intended.*

**Authority.** The Lean sources are the ground truth: `engine/PrisonersDilemma/Program.lean`
(syntax, substitution, size) and `engine/PrisonersDilemma/Dynamics.lean` (evaluation,
formula meaning). The proof system behind `.search` is `ProofSystem.lean` (`Pf`). If this
document and the Lean disagree, the Lean wins — and this document has a bug.

---

## 0. The task in one paragraph

You are writing the **source code of an agent** in a one-shot, simultaneous-move
Prisoner's Dilemma under **full transparency**: each player's program receives the other
player's *source code* as input and must return an action, `C` (cooperate) or `D`
(defect). A program can inspect its opponent in exactly three ways:

1. **simulate** it (run its code against some probe program and see what it plays),
2. **compare** its source to a literal program (syntactic identity), and
3. **prove** things about it (ask a sound, budget-bounded proof oracle whether a statement
   about plays is derivable within `k` characters of proof).

Everything else — branching, constants, delegation — is plumbing around those three.

---

## 1. The game

| | opponent `C` | opponent `D` |
|---|---|---|
| **me `C`** | (3, 3) | (0, 5) |
| **me `D`** | (5, 0) | (1, 1) |

- **Actions:** `Action.C`, `Action.D` (Lean: `inductive Action | C | D`).
- **Outcome:** an ordered pair `(my action, opponent action)` (`Outcome := Action × Action`).
- **One shot, simultaneous, deterministic.** There is no history, no randomness, no mixed
  strategy. A program is a *function from opponent source to action*.
- **Non-termination is a value:** evaluation can fail to produce an action (fuel exhausted /
  infinite regress / dangling reference). Such a match has outcome `none`.

---

## 2. Syntax

`Prog` and `Formula` are mutually recursive (programs appear inside formulas; formulas
guard programs). Two auxiliary list types live in the same block.

### 2.1 Grammar

```
Action   a ::= C | D
Nat      k, n, θ, w, i, j ::= 0 | 1 | 2 | …

Prog     p, q, b ::=
           .const a              -- play a, ignore everything
         | .self                 -- placeholder: MY OWN source
         | .opp                  -- placeholder: the OPPONENT's source
         | .bot p                -- closed reference to program p (substitution barrier)
         | .sim p q              -- "the action p plays when run against q"
         | .ite b a p q          -- if (evaluating b yields a) then p else q
         | .search k φ p q       -- if S proves φ within budget k then p else q
         | .tvote V θ p q        -- weighted-threshold vote over closed instances (advanced, §8)
         | .sys D i              -- component i of a mutually-recursive system (advanced, §8)
         | .selfIdx j            -- reference to system component j (only inside .sys, §8)

Formula  φ, ψ ::=
           .plays p q a          -- "p, run against q, plays a"
         | .impl φ ψ             -- φ → ψ
         | .neg φ                -- ¬φ
         | .box n φ              -- "S derives φ within budget n"
         | .eq p q               -- "p is syntactically identical to the literal q"
         | .diag g φ             -- Löb fixpoint sentence — NEVER write this in a bot (§5.6)

VoteList V ::= .nil | .cons w p V     -- weight w, closed instance p
ProgList D ::= .nil | .cons p D
```

Lean spelling: constructors are written with a leading dot when the expected type is known
(`.const Action.C`, `.sim .opp .self`). Actions inside `.const`/`.ite`/`.plays` may be
written `Action.C` or `.C`; the zoo uses `Action.C` for readability.

### 2.2 Conventions for writing it down

- Every `.ite` takes **four** arguments: guard, test action, then-branch, else-branch.
  The test is **equality with the given action**: `.ite b Action.C p q` runs `p` iff `b`
  evaluates to `C`, and `q` iff it evaluates to `D`.
- Every `.search` takes **four** arguments: budget, formula, then-branch, else-branch.
- `Formula` has **no** conjunction, disjunction, truth constants, or quantifiers. See §5.4
  for encodings.

---

## 3. Substitution — how `.self` and `.opp` get their meaning

`.self` and `.opp` are free placeholders. They are closed by **`subst me opponent`**, which
the evaluator calls at every frame boundary (`.sim`) and before every oracle call
(`.search`). `subst` is **one-shot** (not a fixpoint): placeholders inside the inserted
`me`/`opponent` programs are not substituted again.

| Construct | `subst me opp` does | Why |
|---|---|---|
| `.self` | → `me` | |
| `.opp` | → `opp` | |
| `.const a` | unchanged | |
| `.sim p q`, `.ite b a p q` | recurse into every child | |
| `.search k φ p q` | recurse into `φ`, `p`, `q` | |
| **`.bot p`** | **unchanged — barrier** | a literal bot reference must not be captured |
| `.tvote V θ p q` | recurse into `p`, `q` only; **`V` frozen** | entries are closed instances |
| `.sys D i`, `.selfIdx j` | unchanged (binder / system-level) | closed by `sysClose`, not `subst` |
| `.plays p q a`, `.impl`, `.neg`, `.box` | recurse | |
| **`.eq p q`** | **LHS `p` substituted, RHS `q` frozen** | `q` is a literal target |
| `.diag g φ` | unchanged (frozen) | meta-construction |

**The `.bot` rule is the single most important rule for writers.** Whenever your source
mentions another bot *by name* — as a probe in `.sim`, as an argument inside `.plays`, or as
a delegate — wrap it: `.bot DefectBot`, `.bot (DupocBot k)`. Without the wrapper, the outer
frame's `subst` rewrites the named bot's own `.self`/`.opp`, turning it into a different
program. (Historical bug: `EBot` probing an unwrapped `MirrorBot = .sim .opp .self` got
`.sim opp me` instead — a self-simulation, which broke `EBot` vs `EBot`.)

Exception: the RHS of `.eq` is already frozen, so `.eq .opp (CupodBot k)` needs no `.bot`
(and must NOT get one unless you mean to match the wrapped program — see §4.3).

---

## 4. Evaluation semantics

### 4.1 The evaluator

```
eval : (fuel : Nat) → (me opponent body : Prog) → Option Action
```

`me` and `opponent` are the two **closed** programs in the current frame; `body` is the
subterm being reduced. Every step consumes one unit of fuel; `eval 0 … = none`.

| `body` | `eval (n+1) me opp body` |
|---|---|
| `.const a` | `some a` |
| `.self` | `eval n me opp me` — re-run my own code in the SAME frame (⇒ a bare `.self` body loops until fuel runs out: `none`) |
| `.opp` | `eval n me opp opp` — run the opponent's code **in MY frame** (its `.self` means *me*, its `.opp` means *my opponent*). This is NOT "what the opponent plays against me"; for that use `.sim .opp .self`. Avoid bare `.opp` in body position. |
| `.bot p` | `eval n me opp p` — unwrap; run `p`'s code in the current frame (so `p`'s `.self` = `me`, `p`'s `.opp` = `opp`) |
| `.sim p q` | let `p' := p.subst me opp`, `q' := q.subst me opp`; `eval n p' q' p'` — open a NEW frame where `p'` is the player and `q'` its opponent |
| `.ite b a p q` | evaluate `b` in the current frame; if it is `some a` → run `p`; if `some (other action)` → run `q`; if `none` → `none` |
| `.search k φ p q` | if `proofSearch k (φ.subst me opp)` then run `p` else run `q` (one fuel step for the node, like every node; the oracle's own work is not fuel-metered — it is paid in budget `k`) |
| `.tvote …` | §8.1 |
| `.sys D i` | §8.2 |
| `.selfIdx j` | `none` (a dangling reference — only meaningful once `.sys` has closed it) |

### 4.2 Entry points

```
play    fuel me opp := eval fuel me opp me          -- what `me` plays against `opp`
outcome fuel p q    := do a ← play fuel p q; b ← play fuel q p; some (a, b)
```

A match is two **independent** plays: `p`'s run against `q` and `q`'s run against `p`.
Neither run sees the other's result. Fuel is a technical device; theorems state results
for all sufficiently large fuel (`fuel + pad`), and results are fuel-stable once reached.

### 4.3 What the simulated opponent *sees*

In `.sim .opp (.bot X)` the opponent runs in a frame whose `opponent` is **the literal
term `.bot X`**, not `X`. Behaviorally these are identical (`.bot` just unwraps), but
**syntactically they differ**. An opponent that tests identity — e.g.
`CupodTrollBot k := .search k (.eq .opp (CupodBot k)) …` — will NOT recognize
`.bot (CupodBot k)` as `CupodBot k`. Likewise `.sim .opp .self` shows the opponent your
real source. Keep this in mind whenever you predict a syntax-sensitive opponent's reply
to a probe.

### 4.4 Common shapes and their meaning

| Source | Meaning |
|---|---|
| `.sim .opp .self` | what the opponent plays against **me** (MirrorBot) |
| `.sim .opp (.bot X)` | what the opponent plays against bot `X` (a **probe**) |
| `.sim (.bot X) .opp` | what bot `X` plays against my opponent (ask a third party) |
| `.sim (.bot X) (.bot Y)` | what `X` plays against `Y` (a constant, opponent-independent) |
| `.bot X` as the whole body | delegate: behave like `X`, with `X`'s `.self` meaning **me** |
| `.ite (.sim .opp (.bot X)) Action.C p q` | if the opponent cooperates with `X`, do `p`, else `q` |

### 4.5 Termination

Simulation can regress forever: `MirrorBot` vs `MirrorBot` simulates itself simulating
itself … and the proven outcome is `none`. Any pair of programs that unconditionally
simulate each other against themselves has this problem. Ways out:

- probe with **fixed** bots (`.sim .opp (.bot CooperateBot)`) instead of `.self`;
- use **proof search** instead of simulation for self-referential questions — the oracle
  call is a single step and can succeed via Löb's theorem where simulation regresses (§6).

---

## 5. Formulas and their meaning

### 5.1 Truth (`⊨ φ`, Lean `Formula.interp`)

| Formula | True iff |
|---|---|
| `.plays p q a` | ∃ fuel, `play fuel p q = some a` — `p` run against `q` plays `a` |
| `.impl φ ψ` | `φ` true → `ψ` true |
| `.neg φ` | `φ` is not true |
| `.box n φ` | `Pf n φ` — the proof system `S` derives `φ` within budget `n` |
| `.eq p q` | `p = q` as syntax trees |
| `.diag g φ` | the Löb fixpoint: `Pf g (.diag g φ) → φ` (meta use only) |

### 5.2 Argument order of `.plays`

`.plays X Y a` = "**X** plays `a` **against Y**". Read the first argument as the subject.

| Inside a bot, after `subst` | Reads |
|---|---|
| `.plays .opp .self Action.C` | the opponent cooperates with me |
| `.plays .self .opp Action.C` | I cooperate with the opponent |
| `.plays .opp (.bot DefectBot) Action.D` | the opponent defects against DefectBot |
| `.plays .opp (.bot CooperateBot) Action.D` | the opponent bullies CooperateBot |

### 5.3 `.eq` — syntactic identity

`.eq .opp T` is true iff the opponent's source is literally `T`. The RHS is frozen (never
substituted). Use `.eq` only for "is the opponent exactly program `T`?" strategies; it is
intensional and brittle (any renaming, re-nesting, or `.bot` wrapper defeats it). It is
consumed by the oracle, so it always sits inside `.search`:
`.search k (.eq .opp (CupodBot k)) (.const Action.D) (.const Action.C)`.

### 5.4 Encoding missing connectives

`Formula` has `→` and `¬` only. Semantically, `φ ∧ ψ ≡ ¬(φ → ¬ψ)` and
`φ ∨ ψ ≡ ¬φ → ψ`. **But** in the zoo, conjunctions of guards are written as **nested
`.search`es**, not as encoded formulas — it keeps each proof obligation an atom the proof
system handles directly, and keeps self-referential searches at the root (where Löb
works, §6.3):

```lean
-- "cooperate iff I can prove A AND I can prove B"
.search k A
  (.search k B (.const Action.C) (.const Action.D))
  (.const Action.D)
```

A disjunction is a fall-through chain: `.search k A p (.search k B p q)`.

### 5.5 Negation in guards

`.neg (.plays .opp .self Action.C)` and `.plays .opp .self Action.D` have the same truth
value (actions are binary, assuming the play terminates) but are **different formulas**,
proved by different machinery (refutation vs. assertion). Prefer the positive form unless
the refutation is the point (cf. `WaryBot`).

### 5.6 `.diag`

`.diag` exists so the engine can *prove* bounded Löb internally. It never appears in bot
source. Do not write it.

---

## 6. The proof oracle `.search k φ p q`

### 6.1 What it means

`proofSearch k φ := decide (Pf k φ)`: true iff the fixed proof system `S` has a derivation
of `φ` whose **transcript costs at most `k` characters**. Facts you can rely on:

- **Sound.** If the search succeeds, `φ` is true (`proofSearch_sound`). A bot never acts on
  a false proof.
- **Not complete.** Failure means only "no proof within `k`", never "`φ` is false".
- **Monotone in `k`.** A proof within `k` is a proof within any `k' ≥ k` (`Pf_mono`).
- **Costs are cumulative transcript length** (Critch's literal model): every formula a
  derivation mentions is paid for, measured by `Prog.size`/`Formula.size` (§7). A proof
  about a big program needs a big budget.
- **Not executable in general.** `proofSearch` is `noncomputable` in the core; results
  about search bots are *theorems*, not `#eval` runs (a separate verified evaluator,
  `evalG` in `Decidability/`, can run many of them).

### 6.2 Budgets are parameters

Write searching bots as functions of their budget(s):
`def MyBot (k : Nat) : Prog := .search k …`. Never hard-code a literal budget — every
downstream theorem quantifies over `k` ("for all `k`" or "for all sufficiently large
`k`"). Bots with no `.search` take no parameter.

### 6.3 What tends to be provable (practical guidance)

These are observed regularities of `S`, backed by theorems in the library — not axioms.

1. **Plays of simulation-only programs are cheap to prove.** If the opponent is search-free
   (`.const`/`.sim`/`.ite`/`.bot` only), the fact "opponent plays `a` against `X`" has a
   structural certificate whose cost grows with the programs' sizes. Large enough `k`
   proves it.
2. **Self-referential cooperation is reachable by Löb.** `DupocBot k` (cooperate iff I can
   prove you cooperate with me) cooperates with itself for all large `k`: the proof system
   derives `⊢_k φ → φ` for the cooperation sentence and bounded Löb closes the loop. This
   works best when the self-referential `.search` is at the **root** of the program and
   the then-branch plays exactly the action the guard is about. Wrapping it under an
   `.ite`, or putting a prudence check *before* it, can block the Löb step (that is why
   `PrudentBot` puts its second check inside the then-branch).
3. **Else-branches are expensive to prove — the floor.** Proving "bot `B` takes its
   else-branch" requires *refuting* `B`'s guard, and a refutation costs at least `B`'s full
   failed budget `k`. Consequence: if your proof about the opponent needs the opponent's
   else-branch, and the opponent searches at the **same** budget as you, the proof does not
   fit, and you take your own else-branch. Proven examples:
   `DupocBot k` vs `DBot` = (D, C); `PrudentBot k` vs `PrudentBot k` = (D, D).
4. **Staggering budgets fixes the floor.** Give the checker a larger budget than the thing
   it checks. Two-tier bots separate the dials: `PrudentBot2 kOut kIn` (prudence at
   `kIn > kOut`), `JustBot2 K k` (`K ≥ k + log₂ k + 26` for its probe), and cross-bot
   cooperation like `PrudentBot (2k+64)` vs `DupocBot k`.
5. **Bistability.** A self-referential pair can have two consistent outcomes (both
   cooperate / both defect); then no sound proof decides it, and the outcome may be open.
   Prefer designs where the intended behavior is forced (Löb-friendly polarity, item 2).

---

## 7. Size (the budget's unit)

`Prog.size` counts characters of source. Numerals cost `numCost k = ⌊log₂ k⌋ + 1`.

| Node | Size |
|---|---|
| `.const`, `.self`, `.opp` | 1 |
| `.bot p` | `p.size + 1` |
| `.sim p q` | `p.size + q.size + 1` |
| `.ite b a p q` | `b.size + p.size + q.size + 1` |
| `.search k φ p q` | `numCost k + φ.size + p.size + q.size + 1` |
| `.plays p q a`, `.eq p q`, `.impl φ ψ` | children + 1 |
| `.neg φ` | `φ.size + 1` |
| `.box k φ`, `.diag k φ` | `numCost k + φ.size + 1` |
| `.tvote V θ p q` | `numCost θ + V.vsize + p.size + q.size + 1` |
| `.sys D i` | `D.psize + numCost i + 1` (the WHOLE system's source) |

Examples: `CooperateBot` = 1; `TitForTatBot` = 7; `DupocBot k` = `numCost k + 6`.
Smaller programs are cheaper for *everyone* to reason about — including opponents who need
a proof about you before they cooperate.

---

## 8. Advanced constructors (rarely needed by hand)

These exist for the TauBots layer (`Research/Notes/TAUBOTS.md`). Ordinary strategies do not
need them; do not use them unless the task is specifically about weighted votes or
mutually-recursive systems.

### 8.1 `.tvote V θ p q` — weighted threshold vote

`V` is a list of `(weight w, closed instance I)`. Entries are peeled **in order**: if the
residual threshold is `0`, commit to `p` immediately; otherwise run `I` **against itself**
(`eval n (.bot I) (.bot I) I`): if it plays `C`, subtract `w` (truncated at 0) and
continue; if `D`, continue unchanged; if `none`, the whole vote is `none`. List exhausted
with residual > 0 ⇒ `q`. Entries are frozen by `subst` and `sysClose`, so they must be
**closed** (`.opp`-free); the vote reads true plays, never the oracle.

### 8.2 `.sys D i` and `.selfIdx j` — mutual recursion

`.sys D i` is the `i`-th member of the system `D`; members refer to each other with
`.selfIdx j`. Evaluation unfolds lazily: `.sys D i` ⇒ run `(D.get? i).sysClose D` in the
same frame (one fuel per unfold), where `sysClose` rewrites `.selfIdx j ↦ .sys D j`
(transparent through `.bot`, stops at an inner `.sys`). Out-of-range `i` or a bare
`.selfIdx` evaluates to `none`. `subst` does not enter a `.sys`, so members should not rely
on an enclosing frame's `.self`/`.opp`.

---

## 9. Pattern cookbook

Each pattern is valid Lean inside `namespace PD.Bots`.

**Unconditional.**
```lean
def CooperateBot : Prog := .const Action.C
def DefectBot    : Prog := .const Action.D
```

**Mirror** (play what the opponent plays against me; loops against itself).
```lean
def MirrorBot : Prog := .sim .opp .self
```

**Single probe** (TitForTat: cooperate iff the opponent cooperates with CooperateBot).
```lean
def TitForTatBot : Prog :=
  .ite (.sim .opp (.bot CooperateBot)) Action.C
    (.const Action.C)
    (.const Action.D)
```

**Behavioral decision tree** (each node = one probe; leaves = constants). EBot:
```lean
def EBot : Prog :=
  .ite (.sim .opp (.bot DefectBot)) Action.C
    (.const Action.D)                              -- naive vs DefectBot → exploit
    (.ite (.sim .opp (.bot CooperateBot)) Action.C
      (.const Action.C)
      (.ite (.sim .opp (.bot MirrorBot)) Action.C
        (.const Action.C)
        (.const Action.D)))
```
General recipe for "cooperate iff the opponent's actions against probes P₁…Pₘ match a
target signature": one `.ite (.sim .opp (.bot Pⱼ)) …` per node; a branch that needs no
further question ends in `.const`. Branches may ask different probes.

**Löbian cooperator** (DupocBot: cooperate iff provably the opponent cooperates with me).
```lean
def DupocBot (k : Nat) : Prog :=
  .search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)
```

**Defect on proof of defection** (CupodBot).
```lean
def CupodBot (k : Nat) : Prog :=
  .search k (.plays .opp .self Action.D) (.const Action.D) (.const Action.C)
```

**Conjunction via nested search** (PrudentBot: cooperate iff the opponent provably
cooperates with me AND provably defects against DefectBot).
```lean
def PrudentBot (k : Nat) : Prog :=
  .search k (.plays .opp .self Action.C)
    (.search k (.plays .opp (.bot DefectBot) Action.D)
      (.const Action.C)
      (.const Action.D))
    (.const Action.D)
```

**Two-tier budgets** (separate dials for separate questions).
```lean
def PrudentBot2 (kOut kIn : Nat) : Prog :=
  .search kOut (.plays .opp .self Action.C)
    (.search kIn (.plays .opp (.bot DefectBot) Action.D)
      (.const Action.C) (.const Action.D))
    (.const Action.D)
```

**Proof about a third party** (JustBot: cooperate iff provably the opponent cooperates
with DupocBot).
```lean
def JustBot (k : Nat) : Prog :=
  .search k (.plays .opp (.bot (DupocBot k)) Action.C) (.const Action.C) (.const Action.D)
```

**Implication guard** (CIMCIC: cooperate iff provably "my cooperation implies yours").
```lean
def CIMCIC (k : Nat) : Prog :=
  .search k (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C))
    (.const Action.C) (.const Action.D)
```

**Syntactic identity** (CupodTrollBot: defect iff the opponent is literally CupodBot).
```lean
def CupodTrollBot (k : Nat) : Prog :=
  .search k (.eq .opp (CupodBot k)) (.const Action.D) (.const Action.C)
```

**Reflection guard** (LegibleBot: cooperate iff provably my cooperation is provable).
```lean
def LegibleBot (kOut kIn : Nat) : Prog :=
  .search kOut (.box kIn (.plays .self .opp Action.C)) (.const Action.C) (.const Action.D)
```

**Lookup table** (exact on a finite set of known opponents, default elsewhere):
```lean
def Lookup (k : Nat) : Prog :=
  .search k (.eq .opp (CupodBot k)) (.const Action.C)
    (.search k (.eq .opp (DupocBot k)) (.const Action.C)
      (.const Action.D))
```
Memorizes syntax; generalizes to nothing (a renamed or `.bot`-wrapped copy gets the
default). Use a behavioral tree when you mean behavior.

---

## 10. Correspondence with the Python pseudocode

The distillation prompts (`llm-distillation/src/distillation/bot_descriptions.py`) and
Critch 2022 use Python-like pseudocode. The mapping:

| Pseudocode | `Prog` |
|---|---|
| `return C` | `.const Action.C` |
| `simulate(opp, X)` | `.sim .opp (.bot X)` |
| `simulate(opp, me)` / mirror | `.sim .opp .self` |
| `if simulate(opp, X) == C: A else: B` | `.ite (.sim .opp (.bot X)) Action.C A B` |
| `elif …` | nest another `.ite` in the else slot |
| `if proof_search(k, opp, "opp(Me(k)) == C"): A else: B` | `.search k (.plays .opp .self Action.C) A B` |
| `"opp(X) == D"` | `.plays .opp (.bot X) Action.D` |
| `"me(opp) == C → opp(me) == C"` | `.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)` |
| `opp is literally X` | `.eq .opp X` (inside `.search`) |
| `A and B` (guards) | nested `.search` / `.ite` (§5.4) |

---

## 11. Writer's checklist

Before submitting a program, check every item:

1. **Every literal bot reference is wrapped in `.bot`** — in `.sim` probes, inside
   `.plays`, and as delegates. (Not needed on the RHS of `.eq`.)
2. **`.ite` has four arguments and tests equality with its action.** Double-check the
   polarity: then-branch runs when the guard returns the stated action.
3. **`.plays X Y a` means "X plays a against Y".** For "the opponent cooperates with me"
   write `.plays .opp .self Action.C`, not the reverse.
4. **No bare `.self` or `.opp` in body position** (a loop / a frame-confused run). Use
   `.sim .opp .self` to mean "the opponent's play against me".
5. **Budgets are parameters.** `def B (k : Nat)`; no literal `.search 1000 …`.
6. **No `.diag`, no `.selfIdx` outside a `.sys`, no `.tvote`/`.sys` unless the task is
   about them.**
7. **Self-referential searches sit at the root** with the then-branch playing the action
   the guard is about, if you want Löbian cooperation to be provable.
8. **Think about the floor.** If your intended outcome needs a proof about the opponent's
   *else*-branch, give yourself a larger budget than the opponent's (two-tier bot), or
   expect the same-budget proof to fail.
9. **Think about termination.** Mutual unconditional simulation of `.self` regresses;
   probe fixed bots or use proof search.
10. **Keep it small.** Size is what everyone's proofs pay for.

---

## 12. Output contract (file format)

A bot is one Lean file at `engine/PrisonersDilemma/Bots/LlmGenerations/<BotName>.lean`:

```lean
import PrisonersDilemma.Program
import PrisonersDilemma.Bots.CooperateBot   -- one import per bot referenced via .bot / .eq
import PrisonersDilemma.Bots.DefectBot

open PD
namespace PD.Bots

/-- <BotName>: one-sentence statement of the strategy.
    Why it is interesting / what it should do against the canonical opponents. -/
def <BotName> (k : Nat) : Prog :=      -- omit `(k : Nat)` if there is no `.search`
  …

end PD.Bots
```

Rules: namespace `PD.Bots`; import only `PrisonersDilemma.Program` plus the files of bots
you reference (`Bots/<Name>.lean` for the base zoo, `Bots/LlmGenerations/<Name>.lean` for
generated ones); no `sorry`, no `axiom`, no new definitions other than the bot (helper
`let`s inside the body are fine, as in `OptimBot`). The file must compile
(`lake env lean <file>` from `engine/`). Compilation checks syntax and types only — it
says nothing about behavior; behavior is established by outcome theorems.

---

## 13. Reference: the zoo and proven outcomes

Base zoo (`Bots/*.lean`):

| Bot | Source | Strategy |
|---|---|---|
| CooperateBot | `.const C` | always C |
| DefectBot | `.const D` | always D |
| MirrorBot | `.sim .opp .self` | play what the opponent plays against me |
| TitForTatBot | `.ite (.sim .opp (.bot CooperateBot)) C (C) (D)` | C iff opp cooperates with CooperateBot |
| DBot | `.ite (.sim .opp (.bot DefectBot)) C (D) (C)` | D iff opp cooperates with DefectBot (punish/exploit the naive) |
| OBot | `ite(sim opp CB) C (ite(sim opp DB) C (C) (D)) (D)` | C iff opp cooperates with both CooperateBot and DefectBot |
| EBot | see §9 | exploit the naive; reward cooperators and mirror-cooperators |
| DupocBot k | `.search k (plays opp self C) (C) (D)` | Defect Unless Proof Of Cooperation |
| CupodBot k | `.search k (plays opp self D) (D) (C)` | Cooperate Unless Proof Of Defection |
| CupodTrollBot k | `.search k (eq opp (CupodBot k)) (D) (C)` | D iff opp is literally CupodBot |

Generated zoo (`Bots/LlmGenerations/*.lean`): PrudentBot/PrudentBot2, JustBot/JustBot2,
CIMCIC, DIMCID, GuardianBot, WaryBot, LegibleBot, OptimBot (all in §9 or their files).

Selected **proven** outcomes `(left, right)` from `app/generated/outcome_theorems.json`
(the kernel-checked export; `universal` = every `k`, `eventual` = all large `k`, same `k`
on both sides):

| Left vs Right | Outcome | Regime |
|---|---|---|
| CooperateBot vs DefectBot | (C, D) | nobudget |
| MirrorBot vs MirrorBot | `none` (regress) | nobudget |
| MirrorBot vs TitForTatBot | (C, C) | nobudget |
| TitForTatBot vs DBot | (D, C) | nobudget |
| OBot vs OBot | (D, D) | nobudget |
| EBot vs EBot | (C, C) | nobudget |
| EBot vs TitForTatBot | (C, D) | nobudget |
| DupocBot vs DupocBot | (C, C) | eventual |
| DupocBot vs DefectBot | (D, D) | universal |
| DupocBot vs DBot | (D, C) | universal (the floor) |
| DupocBot vs CupodBot | (D, C) | universal |
| CupodBot vs CupodBot | (D, D) | eventual |
| CupodBot vs OBot | (C, D) | eventual |
| PrudentBot vs PrudentBot | (D, D) | universal (the floor; PrudentBot2 escapes) |
| PrudentBot vs MirrorBot | (C, C) | eventual |
| PrudentBot vs CooperateBot | (D, C) | universal |
| JustBot vs JustBot | (C, C) | eventual |
| CIMCIC vs CIMCIC | (C, C) | eventual |
| DIMCID vs DIMCID | (D, D) | eventual |
| GuardianBot vs DefectBot | (D, D) | eventual |
| WaryBot vs WaryBot | (C, C) | universal |

Use these to sanity-check your mental model of the semantics before predicting a new
bot's behavior.
