# `Prog` Language Specification

Derived from the reference specification on 09 November 2026. Drafted by Claude. Not yet verified.

**Use.** Writing a `Prog` program: a bot for the open-source one-shot Prisoner's Dilemma.

**Authority.** The Lean sources are the ground truth: `engine/PrisonersDilemma/Program.lean`
(syntax, substitution, size) and `engine/PrisonersDilemma/Dynamics.lean` (evaluation,
formula meaning). The proof system behind `.search` is `ProofSystem.lean` (`Pf`). If this
document and the Lean disagree, the Lean wins — and this document has a bug.

Throughout, `p`, `q`, `b`, `X`, `Y` stand for arbitrary programs, `a` for an arbitrary
action, `φ`, `ψ` for arbitrary formulas, and `k`, `n` for arbitrary numbers.

---

## 0. The task in one paragraph

You are writing the **source code of an agent** in a one-shot, simultaneous-move
Prisoner's Dilemma under **full transparency**: each player's program receives the other
player's *source code* as input and must return an action, `C` (cooperate) or `D`
(defect). A program can inspect another program in exactly three ways:

1. **simulate** it (run its code against some program and see what it plays),
2. **compare** its source to a literal program (syntactic identity), and
3. **prove** things about it (ask a sound, budget-bounded proof oracle whether a statement
   about plays is derivable within `k` characters of proof).

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
         | .diag g φ             -- Löb fixpoint sentence (§5.6)

VoteList V ::= .nil | .cons w p V     -- weight w, closed instance p
ProgList D ::= .nil | .cons p D
```

Lean spelling: constructors are written with a leading dot when the expected type is known.
Actions inside `.const`/`.ite`/`.plays` may be written `Action.C`, `Action.D`, `.C` or `.D`.

### 2.2 Conventions for writing it down

- Every `.ite` takes **four** arguments: guard, test action, then-branch, else-branch.
  The test is **equality with the given action**: `.ite b a p q` runs `p` iff `b`
  evaluates to `a`, and `q` iff it evaluates to the other action.
- Every `.search` takes **four** arguments: budget, formula, then-branch, else-branch.
- `Formula` has **no** conjunction, disjunction, truth constants, or quantifiers. See §5.4.

---

## 3. Substitution — how `.self` and `.opp` get their meaning

`.self` and `.opp` are free placeholders and may appear anywhere a program may appear,
including as arguments of `.sim` and of `.plays`. They are closed by **`subst me opponent`**,
which the evaluator calls at every frame boundary (`.sim`) and before every oracle call
(`.search`). `subst` is **one-shot** (not a fixpoint): placeholders inside the inserted
`me`/`opponent` programs are not substituted again.

| Construct | `subst me opp` does | Why |
|---|---|---|
| `.self` | → `me` | |
| `.opp` | → `opp` | |
| `.const a` | unchanged | |
| `.sim p q`, `.ite b a p q` | recurse into every child | |
| `.search k φ p q` | recurse into `φ`, `p`, `q` | |
| **`.bot p`** | **unchanged — barrier** | a literal program reference must not be captured |
| `.tvote V θ p q` | recurse into `p`, `q` only; **`V` frozen** | entries are closed instances |
| `.sys D i`, `.selfIdx j` | unchanged (binder / system-level) | closed by `sysClose`, not `subst` |
| `.plays p q a`, `.impl`, `.neg`, `.box` | recurse | |
| **`.eq p q`** | **LHS `p` substituted, RHS `q` frozen** | `q` is a literal target |
| `.diag g φ` | unchanged (frozen) | meta-construction |

**The `.bot` rule.** Whenever a program mentions another *literal* program — as an argument
of `.sim`, as an argument inside `.plays`, or as a branch — and that literal program should
keep its own meaning, wrap it in `.bot`. Without the wrapper, the outer frame's `subst`
rewrites the literal program's own `.self`/`.opp`, turning it into a different program.

Exception: the RHS of `.eq` is already frozen, so it needs no `.bot` (and must not get one
unless you mean to match the wrapped program — see §4.3).

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
| `.opp` | `eval n me opp opp` — run the opponent's code **in MY frame** (its `.self` means *me*, its `.opp` means *my opponent*). This is NOT "what the opponent plays against me"; only `.sim` opens a frame in which the opponent is the player. |
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
Neither run sees the other's result. Results are fuel-stable once reached.

### 4.3 What a simulated program *sees*

In `.sim X (.bot Y)` the program `X` runs in a frame whose `opponent` is **the literal
term `.bot Y`**, not `Y`. Behaviorally these are identical (`.bot` just unwraps), but
**syntactically they differ**: a program that tests syntactic identity against `Y` does not
recognize `.bot Y` as `Y`.

### 4.4 Termination

Simulation can regress forever: if two programs each unconditionally simulate the other
against itself, every simulation opens another one, fuel runs out, and the result is `none`.

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

### 5.3 `.eq` — syntactic identity

`.eq X T` is true iff `X` is, after substitution, literally the program `T`; any difference
in the syntax tree, including a `.bot` wrapper, makes it false. The RHS is never
substituted. Formulas are consumed by the oracle, so `.eq` always sits inside a `.search`
guard.

### 5.4 Missing connectives

`Formula` has `→` and `¬` only. Semantically, `φ ∧ ψ ≡ ¬(φ → ¬ψ)` and `φ ∨ ψ ≡ ¬φ → ψ`.
Combinations of conditions can also be expressed by nesting `.search` and `.ite` nodes in
branch positions. The two forms are different programs and can differ in proof cost.

### 5.5 Negation in guards

For a terminating play, `.neg (.plays p q a)` and `.plays p q (other action)` have the same
truth value but are **different formulas**, proved by different machinery (refutation vs.
assertion).

### 5.6 `.diag`

`.diag` exists so the engine can *prove* bounded Löb internally. It never appears in bot
source.

---

## 6. The proof oracle `.search k φ p q`

### 6.1 What it means

`proofSearch k φ := decide (Pf k φ)`: true iff the fixed proof system `S` has a derivation
of `φ` whose **transcript costs at most `k` characters**. Facts you can rely on:

- **Sound.** If the search succeeds, `φ` is true (`proofSearch_sound`). A bot never acts on
  a false proof.
- **Not complete.** Failure means only "no proof within `k`", never "`φ` is false".
- **Monotone in `k`.** A proof within `k` is a proof within any `k' ≥ k` (`Pf_mono`).
- **Costs are cumulative transcript length:** every formula a derivation mentions is paid
  for, measured by `Prog.size`/`Formula.size` (§7). A proof about a big program needs a big
  budget.

### 6.2 Budgets are parameters

A program containing `.search` is written as a function of its budget(s), one or more `Nat`
parameters, and uses those parameters rather than literal budgets. A program with no
`.search` takes no parameter.

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

---

## 8. Advanced constructors

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

## 9. Properties of the proof system `S`

These are properties of `S` as it stands. They are not recommendations.

1. **Plays of search-free programs.** If a program is built only from `.const`, `.sim`,
   `.ite` and `.bot`, the fact that it plays `a` against some program has a structural
   certificate whose cost grows with the programs' sizes.
2. **Reasoning about provability.** `S` can reason about its own bounded provability through
   `.box`, and bounded Löb's theorem is derivable in it: a derivation of "`φ` follows from a
   bounded proof of `φ`" yields, at a suitable budget, a derivation of `φ`.
3. **Dependence on program shape.** `S` reads program source through rules specific to the
   node at hand, so two programs with the same behavior can differ in which statements about
   them are derivable and at what cost.
4. **Else-branches.** Certifying that a program takes the else-branch of `.search k φ p q`
   requires a derivation refuting `φ`, and that derivation pays at least the failed budget
   `k`.
5. **Undecided statements.** A true statement can lack a derivation within a given budget.
   A self-referential pair of programs can have more than one assignment of actions
   consistent with the rules, in which case no sound derivation need decide between them.

---

## 10. Restrictions in this task

- No `.diag`.
- No `.tvote`, `.sys` or `.selfIdx`.
- There is no library of named programs to import or reference. Any program you want to
  mention literally is written out inline, or bound with a `let` inside the body.

---

## 11. Writer's checklist

Before submitting a program, check every item:

1. **Every literal program that should keep its own meaning is wrapped in `.bot`** (not
   needed on the RHS of `.eq`).
2. **`.ite` has four arguments and tests equality with its action.** The then-branch runs
   when the guard returns the stated action.
3. **`.plays X Y a` means "X plays a against Y".**
4. **`.self` and `.opp` in body position** behave as in §4.1. Check that this is what you
   mean.
5. **`.search` budgets are parameters** (§6.2).
6. **The restrictions in §10 hold.**

---

## 12. Output contract (file format)

A bot is one Lean file:

```lean
import PrisonersDilemma.Program

open PD
namespace PD.Bots

/-- <BotName>: one-sentence statement of the strategy. -/
def <BotName> (k : Nat) : Prog :=      -- omit `(k : Nat)` if there is no `.search`
  …

end PD.Bots
```

Rules: namespace `PD.Bots`; the only import is `PrisonersDilemma.Program`; no `sorry`, no
`axiom`, no new definitions other than the bot (helper `let`s inside the body are fine). The
file must compile. Compilation checks syntax and types only — it says nothing about
behavior.
