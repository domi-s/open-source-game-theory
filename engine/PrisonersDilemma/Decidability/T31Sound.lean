import PrisonersDilemma.BaseTheorems

/-!
# T31Sound — the SOUNDNESS half of `T31EngineDecider`, kept building.

`T31EngineDecider` (and the whole T31–T54 chain) has no arms for the tau constructors
(`tvote`, `sys`, `selfIdx`) or the `botSys*` rules — debt M2 (`lakefile.toml`,
`TAUBOTS.md` §4). The app's certified evaluator (`outcomeG ∘ guardFastN`, used by
`outcome_prepass` / `bot_profile`) needs only the soundness side, so this module is
`T31EngineDecider` with every completeness / monotonicity / semidecidability result and
the demos removed, and the remaining matches extended so the tau constructors are
never decided (the evaluator returns `none` on them — sound, merely incomplete).
Same namespace and names, so callers switch by changing the import. Delete once M2 lands.
-/

namespace PD.T31
open PD PD.BaseTheorems

/-! ## 1. Numeral bound + size positivity. -/

theorem lt_two_pow_of_log2_lt {g s : Nat} (h : Nat.log2 g + 1 ≤ s) : g < 2 ^ s := by
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · exact Nat.two_pow_pos s
  · have h1 : g < 2 ^ (Nat.log2 g + 1) := by
      rw [Nat.log2_eq_log_two]
      exact Nat.lt_pow_succ_log_self Nat.one_lt_two g
    exact lt_of_lt_of_le h1 (Nat.pow_le_pow_right (by decide) h)

theorem Prog.size_pos : ∀ p : Prog, 1 ≤ p.size := by
  intro p; cases p <;> simp [numCost, Prog.size]

theorem Formula.size_pos : ∀ φ : Formula, 1 ≤ φ.size := by
  intro φ; cases φ <;> simp [numCost, Formula.size]

/-! ## 2. Enumeration — programs/formulas of size ≤ n form a computably finite set
(numerals pay `log2`, actions are finite). A SUPERSET is all the search needs. -/

mutual
  def enumProg : Nat → List Prog
    | 0 => []
    | n+1 =>
        [Prog.const .C, Prog.const .D, Prog.self, Prog.opp]
        ++ ((enumProg n).map Prog.bot)
        ++ ((enumProg n).flatMap fun p => (enumProg n).map fun q => Prog.sim p q)
        ++ ((enumProg n).flatMap fun b => [Action.C, Action.D].flatMap fun a =>
             (enumProg n).flatMap fun p => (enumProg n).map fun q => Prog.ite b a p q)
        ++ ((List.range (2 ^ (n+1))).flatMap fun k => (enumFormula n).flatMap fun φ =>
             (enumProg n).flatMap fun p => (enumProg n).map fun q => Prog.search k φ p q)

  def enumFormula : Nat → List Formula
    | 0 => []
    | n+1 =>
        ((enumProg n).flatMap fun p => (enumProg n).flatMap fun q =>
          [Action.C, Action.D].map fun a => Formula.plays p q a)
        ++ ((enumFormula n).flatMap fun φ => (enumFormula n).map fun ψ => Formula.impl φ ψ)
        ++ ((enumFormula n).map Formula.neg)
        ++ ((List.range (2 ^ (n+1))).flatMap fun k =>
             (enumFormula n).map fun φ => Formula.box k φ)
        ++ ((enumProg n).flatMap fun p => (enumProg n).map fun q => Formula.eq p q)
        ++ ((List.range (2 ^ (n+1))).flatMap fun g =>
             (enumFormula n).map fun φ => Formula.diag g φ)
end

theorem mem_action_pair (a : Action) : a ∈ [Action.C, Action.D] := by cases a <;> simp

/-! ## 3. Paid conclusions, atom-refined. -/

/-- Every `Pf` proof either pays its conclusion's size or IS an atom certificate
    (whose budget bounds eval-steps, not characters). -/
theorem pf_size_or_atom : ∀ {k φ}, Pf k φ → φ.size ≤ k ∨ AtomProvable k φ := by
  intro k φ h
  cases h with
  | atom hatom => exact Or.inr hatom
  -- the seven leaves pay exactly their conclusion (their side-condition IS the size gate)
  | searchBranch g ψ a b me opnt hme hle => exact Or.inl hle
  | simStep me p q opnt a hme hle => exact Or.inl hle
  | botSimStep me p q opnt a hme hle => exact Or.inl hle
  | botSearchStep g ψ a b me opnt hme hle => exact Or.inl hle
  | botSysSearchStep defs i g ψ a b me opnt hme hget hle => exact Or.inl hle
  | botSysSimStep defs i j a me opnt hme hget hle => exact Or.inl hle
  | botSysSearchThenSearch defs i k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme hget hprud hmk hle =>
      exact Or.inl (by omega)
  | iteBranchSearch_t g z a' c0 c1 ψ q me opnt hme hle => exact Or.inl hle
  | eqRefl p hle => exact Or.inl hle
  | eqNeg p q hne hle => exact Or.inl hle
  | implRefl φ' hle => exact Or.inl hle
  | implK φ' ψ' hle => exact Or.inl hle
  | implS φ' ψ' χ' hle => exact Or.inl hle
  | contrapose φ' ψ' m h hle => exact Or.inl (by omega)
  | negElim =>
      rename_i φ' m₁ m₂ h1 h2 hle
      exact Or.inl (by omega)
  | weakenImpl φ' ψ' m hψ hle => exact Or.inl (by omega)
  | searchThenSearch_t k₁ k₂ m ψ₁ ψ₂ c0 c1 q me opnt hme hprud hmk hle => exact Or.inl (by omega)
  | searchChain g₁ ψ₁ e₁ L a me opnt hme hle => exact Or.inl hle
  | searchElseChain hd L a me opnt hme hle => exact Or.inl (by omega)
  | ctxChain hd L a me opnt hme hle => exact Or.inl hle
  | implTrans φ' ψ' χ' a b h1 h2 hle => exact Or.inl (by omega)
  | atomBoxImpl kBox p q a hatom hle => exact Or.inl (by omega)
  | boxIntro kIn K φ' hprem hle => exact Or.inl (by omega)
  | mp =>
      rename_i m₁ m₂ φ' h2 h1 hle
      exact Or.inl (by omega)
  | axK a b c m K φ' α hprem hgate hle => exact Or.inl (by omega)
  | box4 a b K φ' hgate hle => exact Or.inl (by omega)
  | diagF pm fb g K tgt hgate hle => exact Or.inl (by omega)
  | diagB pm fb g K tgt hgate hle => exact Or.inl (by omega)
  | axKf a b c K φ' α hgate hle => exact Or.inl (by omega)
  | impS2 φ' ψ' χ' m₁ m₂ K h1 h2 hle => exact Or.inl (by omega)
  | boxMono a b K φ' hab hle => exact Or.inl (by omega)
  | atomNeg p q b aN m hatom hne hle => exact Or.inl (by omega)

/-- Non-`.plays` conclusions ARE size-paid: `AtomProvable` only ever holds at a `.plays`. -/
theorem pf_impl_size {k : Nat} {A B : Formula}
    (h : Pf k (.impl A B)) : (Formula.impl A B).size ≤ k := by
  rcases pf_size_or_atom h with hsz | hatom
  · exact hsz
  · cases hatom

/-! ## 4. The source-transparency LEAVES — decided by syntactic shape-matching.

**Pf-only** (`PF_ONLY_ROADMAP.md` Phase 4.2): this replaces the former `decDeriv` backward
search over the `Type`-valued `Derivation`. The leaf checkers survive unchanged (they were
always pure shape+size matchers, `DecidableEq` on `Prog`/`Formula`); the `modusPonens`/
`hypSyll` recursion `decDeriv` carried is SUBSUMED by `chkAppE`/`chkITrans` below, which
enumerate cut formulas through the decider's own fuel. `chkLeaf` bundles the seven leaves
into the single disjunct that occupies `decDeriv`'s old slot in `decProv` — so the decider's
shape (and every fuel-monotonicity proof) is unchanged. -/

-- leaf checkers (shape + size gate; leaf transcript = conclusion size)
def chkEqRefl (k : Nat) : Formula → Bool
  | .eq p q => p == q && decide ((Formula.eq p q).size ≤ k)
  | _ => false

def chkEqNeg (k : Nat) : Formula → Bool
  | .neg (.eq p q) => decide (p ≠ q) && decide ((Formula.neg (.eq p q)).size ≤ k)
  | _ => false

def chkSearchBranch (k : Nat) : Formula → Bool
  | .impl (.box k₁ ψ') (.plays (.search k₁' ψg (.const aT) (.const aE)) opnt a) =>
      decide (k₁ = k₁') && decide (a = aT) &&
      ψ' == ψg.subst (.search k₁' ψg (.const aT) (.const aE)) opnt &&
      decide ((Formula.impl (.box k₁ ψ')
        (.plays (.search k₁' ψg (.const aT) (.const aE)) opnt a)).size ≤ k)
  | _ => false

def chkSimStep (k : Nat) : Formula → Bool
  | .impl (.plays pp qq a₁) (.plays (.sim p q) opnt a₂) =>
      decide (a₁ = a₂) && pp == p.subst (.sim p q) opnt && qq == q.subst (.sim p q) opnt &&
      decide ((Formula.impl (.plays pp qq a₁) (.plays (.sim p q) opnt a₂)).size ≤ k)
  | _ => false

def chkBotSimStep (k : Nat) : Formula → Bool
  | .impl (.plays pp qq a₁) (.plays (.bot (.sim p q)) opnt a₂) =>
      decide (a₁ = a₂) && pp == p.subst (.bot (.sim p q)) opnt &&
      qq == q.subst (.bot (.sim p q)) opnt &&
      decide ((Formula.impl (.plays pp qq a₁) (.plays (.bot (.sim p q)) opnt a₂)).size ≤ k)
  | _ => false

def chkBotSearchStep (k : Nat) : Formula → Bool
  | .impl (.box k₁ ψ') (.plays (.bot (.search k₁' ψg (.const aT) (.const aE))) opnt a) =>
      decide (k₁ = k₁') && decide (a = aT) &&
      ψ' == ψg.subst (.bot (.search k₁' ψg (.const aT) (.const aE))) opnt &&
      decide ((Formula.impl (.box k₁ ψ')
        (.plays (.bot (.search k₁' ψg (.const aT) (.const aE))) opnt a)).size ≤ k)
  | _ => false

def chkIteBranchSearch (k : Nat) : Formula → Bool
  | .impl (.plays opnt1 (.bot z) a') (.impl (.box kg ψ')
      (.plays (.ite (.sim .opp (.bot z')) a'' (.search kg' ψg (.const c0) (.const c1)) q)
        opnt2 c)) =>
      z == z' && decide (a' = a'') && decide (kg = kg') && decide (c = c0) &&
      opnt1 == opnt2 &&
      ψ' == ψg.subst
        (.ite (.sim .opp (.bot z')) a'' (.search kg' ψg (.const c0) (.const c1)) q) opnt2 &&
      decide ((Formula.impl (.plays opnt1 (.bot z) a') (.impl (.box kg ψ')
        (.plays (.ite (.sim .opp (.bot z')) a'' (.search kg' ψg (.const c0) (.const c1)) q)
          opnt2 c))).size ≤ k)
  | _ => false

def chkImplRefl (k : Nat) : Formula → Bool
  | .impl A B => A == B && decide ((Formula.impl A B).size ≤ k)
  | _ => false

def chkImplK (k : Nat) : Formula → Bool
  | .impl A (.impl C B) => A == B && decide ((Formula.impl A (.impl C B)).size ≤ k)
  | _ => false

def chkImplS (k : Nat) : Formula → Bool
  | .impl (.impl A (.impl B C)) (.impl (.impl A' B') (.impl A'' C')) =>
      A == A' && A == A'' && B == B' && C == C' &&
      decide ((Formula.impl (.impl A (.impl B C))
        (.impl (.impl A' B') (.impl A'' C'))).size ≤ k)
  | _ => false

/-! ### The search-telescope parser (`searchChain`, 2026-07-28)

Walk the candidate guard chain and the tail player's own source in lockstep: each
`□ g ψ'` layer must match a `.search g ψ body e` layer of `me` (with the guard
instance `ψ' = ψ.subst me opp`), ending at the chain's plays-atom over the remaining
`.const` branch. Sound and complete against `Pf.searchChain` (below). -/

def chkChainGo (me opp : Prog) : Formula → Prog → Bool
  | .impl (.box g ψ') rest, .search g' ψ body _e =>
      decide (g = g') && ψ' == ψ.subst me opp && chkChainGo me opp rest body
  | .plays me' opp' a, .const a' =>
      me' == me && opp' == opp && decide (a = a')
  | _, _ => false

def chainTail? : Formula → Option (Prog × Prog)
  | .plays me opp _ => some (me, opp)
  | .impl _ ψ => chainTail? ψ
  | _ => none

def chkSearchChain (k : Nat) : Formula → Bool
  | .impl (.box g ψ') rest =>
      decide ((Formula.impl (.box g ψ') rest).size ≤ k) &&
      (match chainTail? rest with
       | some (me, opp) => chkChainGo me opp (.impl (.box g ψ') rest) me
       | none => false)
  | _ => false

theorem chkChainGo_sound (me opp : Prog) : ∀ (n : Nat) (φ : Formula), φ.size ≤ n →
    ∀ (body : Prog), chkChainGo me opp φ body = true →
    ∃ (L : List (Nat × Formula × Prog)) (a : Action),
      body = searchPlug L (.const a) ∧
      φ = implChain (searchGuards me opp L) (.plays me opp a) := by
  intro n
  induction n with
  | zero =>
      intro φ hφ
      have := Formula.size_pos φ
      omega
  | succ n ih =>
      intro φ hφ body h
      cases φ with
      | impl A rest =>
          cases A with
          | box g ψ' =>
              cases body with
              | search g' ψ pbody e =>
                  simp only [chkChainGo, Bool.and_eq_true, decide_eq_true_eq,
                    beq_iff_eq] at h
                  obtain ⟨⟨rfl, rfl⟩, hr⟩ := h
                  have hrest : rest.size ≤ n := by
                    have h1 := Formula.size_pos (Formula.box g (ψ.subst me opp))
                    simp only [Formula.size] at hφ
                    omega
                  obtain ⟨L, a, hb, hφ'⟩ := ih rest hrest pbody hr
                  refine ⟨(g, ψ, e) :: L, a, ?_, ?_⟩
                  · rw [hb]; exact rfl
                  · rw [hφ']; exact rfl
              | const a => simp [chkChainGo] at h
              | self => simp [chkChainGo] at h
              | opp => simp [chkChainGo] at h
              | bot p => simp [chkChainGo] at h
              | sim p q => simp [chkChainGo] at h
              | ite b x p q => simp [chkChainGo] at h
              | tvote _ _ _ _ => simp [chkChainGo] at h
              | sys _ _ => simp [chkChainGo] at h
              | selfIdx _ => simp [chkChainGo] at h
          | plays p q c => cases body <;> simp [chkChainGo] at h
          | impl X Y => cases body <;> simp [chkChainGo] at h
          | neg X => cases body <;> simp [chkChainGo] at h
          | eq p q => cases body <;> simp [chkChainGo] at h
          | diag gg X => cases body <;> simp [chkChainGo] at h
      | plays p q c =>
          cases body with
          | const a' =>
              simp only [chkChainGo, Bool.and_eq_true, decide_eq_true_eq,
                beq_iff_eq] at h
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
              exact ⟨[], c, rfl, rfl⟩
          | self => simp [chkChainGo] at h
          | opp => simp [chkChainGo] at h
          | bot pp => simp [chkChainGo] at h
          | sim pp qq => simp [chkChainGo] at h
          | ite b x pp qq => simp [chkChainGo] at h
          | search g ψ pp qq => simp [chkChainGo] at h
          | tvote _ _ _ _ => simp [chkChainGo] at h
          | sys _ _ => simp [chkChainGo] at h
          | selfIdx _ => simp [chkChainGo] at h
      | neg A => cases body <;> simp [chkChainGo] at h
      | box m A => cases body <;> simp [chkChainGo] at h
      | eq p q => cases body <;> simp [chkChainGo] at h
      | diag g A => cases body <;> simp [chkChainGo] at h

theorem chainTail?_implChain (me opp : Prog) (a : Action) :
    ∀ (gs : List Formula),
      chainTail? (implChain gs (.plays me opp a)) = some (me, opp) := by
  intro gs
  induction gs with
  | nil => rfl
  | cons g gs ih => exact ih

/-! ### The MIXED-telescope parser (`ctxChain`, the ite frontier, 2026-07-28)

Like `chkChainGo`, but each formula layer may be a `□ g ψ'` matching a `.search`
layer of `me`, OR a probe `.plays opp (.bot z) aT` matching an
`.ite (.sim .opp (.bot z)) aT body other` layer (then-descent). Sound and complete
against `Pf.ctxChain`. -/

def chkCtxGo (me opp : Prog) : Formula → Prog → Bool
  | .impl (.box g ψ') rest, .search g' ψ body _e =>
      decide (g = g') && ψ' == ψ.subst me opp && chkCtxGo me opp rest body
  | .impl (.plays opp' (.bot z') aT') rest, .ite (.sim .opp (.bot z)) aT body _other =>
      opp' == opp && z' == z && decide (aT' = aT) && chkCtxGo me opp rest body
  | .plays me' opp' a, .const a' =>
      me' == me && opp' == opp && decide (a = a')
  | _, _ => false

def chkCtxChain (k : Nat) : Formula → Bool
  | .impl A rest =>
      decide ((Formula.impl A rest).size ≤ k) &&
      (match chainTail? rest with
       | some (me, opp) => chkCtxGo me opp (.impl A rest) me
       | none => false)
  | _ => false

theorem chkCtxGo_sound (me opp : Prog) : ∀ (n : Nat) (φ : Formula), φ.size ≤ n →
    ∀ (body : Prog), chkCtxGo me opp φ body = true →
    ∃ (L : List CtxLayer) (a : Action),
      body = ctxPlug L (.const a) ∧
      φ = implChain (ctxGuards me opp L) (.plays me opp a) := by
  intro n
  induction n with
  | zero =>
      intro φ hφ
      have := Formula.size_pos φ
      omega
  | succ n ih =>
      intro φ hφ body h
      cases φ with
      | impl A rest =>
          cases A with
          | box g ψ' =>
              cases body with
              | search g' ψ pbody e =>
                  simp only [chkCtxGo, Bool.and_eq_true, decide_eq_true_eq,
                    beq_iff_eq] at h
                  obtain ⟨⟨rfl, rfl⟩, hr⟩ := h
                  have hrest : rest.size ≤ n := by
                    have h1 := Formula.size_pos (Formula.box g (ψ.subst me opp))
                    simp only [Formula.size] at hφ
                    omega
                  obtain ⟨L, a, hb, hφ'⟩ := ih rest hrest pbody hr
                  refine ⟨.searchL g ψ e :: L, a, ?_, ?_⟩
                  · rw [hb]; exact rfl
                  · rw [hφ']; exact rfl
              | const a => simp [chkCtxGo] at h
              | self => simp [chkCtxGo] at h
              | opp => simp [chkCtxGo] at h
              | bot p => simp [chkCtxGo] at h
              | sim p q => simp [chkCtxGo] at h
              | ite b x p q => simp [chkCtxGo] at h
              | tvote _ _ _ _ => simp [chkCtxGo] at h
              | sys _ _ => simp [chkCtxGo] at h
              | selfIdx _ => simp [chkCtxGo] at h
          | plays op' bz aT' =>
              cases body with
              | ite b x pbody e =>
                  cases bz with
                  | bot z' =>
                      cases b with
                      | sim sp sq =>
                          cases sp with
                          | opp =>
                              cases sq with
                              | bot z =>
                                  simp only [chkCtxGo, Bool.and_eq_true,
                                    decide_eq_true_eq, beq_iff_eq] at h
                                  obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hr⟩ := h
                                  have hrest : rest.size ≤ n := by
                                    simp only [Formula.size] at hφ
                                    omega
                                  obtain ⟨L, a, hb, hφ'⟩ := ih rest hrest pbody hr
                                  refine ⟨.iteL z' aT' e :: L, a, ?_, ?_⟩
                                  · rw [hb]; exact rfl
                                  · rw [hφ']; exact rfl
                              | const a => simp [chkCtxGo] at h
                              | self => simp [chkCtxGo] at h
                              | opp => simp [chkCtxGo] at h
                              | sim p q => simp [chkCtxGo] at h
                              | ite b' x' p q => simp [chkCtxGo] at h
                              | search g ψ p q => simp [chkCtxGo] at h
                              | tvote _ _ _ _ => simp [chkCtxGo] at h
                              | sys _ _ => simp [chkCtxGo] at h
                              | selfIdx _ => simp [chkCtxGo] at h
                          | const a => simp [chkCtxGo] at h
                          | self => simp [chkCtxGo] at h
                          | bot p => simp [chkCtxGo] at h
                          | sim p q => simp [chkCtxGo] at h
                          | ite b' x' p q => simp [chkCtxGo] at h
                          | search g ψ p q => simp [chkCtxGo] at h
                          | tvote _ _ _ _ => simp [chkCtxGo] at h
                          | sys _ _ => simp [chkCtxGo] at h
                          | selfIdx _ => simp [chkCtxGo] at h
                      | const a => simp [chkCtxGo] at h
                      | self => simp [chkCtxGo] at h
                      | opp => simp [chkCtxGo] at h
                      | bot p => simp [chkCtxGo] at h
                      | ite b' x' p q => simp [chkCtxGo] at h
                      | search g ψ p q => simp [chkCtxGo] at h
                      | tvote _ _ _ _ => simp [chkCtxGo] at h
                      | sys _ _ => simp [chkCtxGo] at h
                      | selfIdx _ => simp [chkCtxGo] at h
                  | const a => cases b <;> simp [chkCtxGo] at h
                  | self => cases b <;> simp [chkCtxGo] at h
                  | opp => cases b <;> simp [chkCtxGo] at h
                  | sim p q => cases b <;> simp [chkCtxGo] at h
                  | ite b' x' p q => cases b <;> simp [chkCtxGo] at h
                  | search g ψ p q => cases b <;> simp [chkCtxGo] at h
                  | tvote _ _ _ _ => simp [chkCtxGo] at h
                  | sys _ _ => simp [chkCtxGo] at h
                  | selfIdx _ => simp [chkCtxGo] at h
              | const a => simp [chkCtxGo] at h
              | self => simp [chkCtxGo] at h
              | opp => simp [chkCtxGo] at h
              | bot p => simp [chkCtxGo] at h
              | sim p q => simp [chkCtxGo] at h
              | search g ψ p q => simp [chkCtxGo] at h
              | tvote _ _ _ _ => simp [chkCtxGo] at h
              | sys _ _ => simp [chkCtxGo] at h
              | selfIdx _ => simp [chkCtxGo] at h
          | impl X Y => cases body <;> simp [chkCtxGo] at h
          | neg X => cases body <;> simp [chkCtxGo] at h
          | eq p q => cases body <;> simp [chkCtxGo] at h
          | diag gg X => cases body <;> simp [chkCtxGo] at h
      | plays p q c =>
          cases body with
          | const a' =>
              simp only [chkCtxGo, Bool.and_eq_true, decide_eq_true_eq,
                beq_iff_eq] at h
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
              exact ⟨[], c, rfl, rfl⟩
          | self => simp [chkCtxGo] at h
          | opp => simp [chkCtxGo] at h
          | bot pp => simp [chkCtxGo] at h
          | sim pp qq => simp [chkCtxGo] at h
          | ite b x pp qq => simp [chkCtxGo] at h
          | search g ψ pp qq => simp [chkCtxGo] at h
          | tvote _ _ _ _ => simp [chkCtxGo] at h
          | sys _ _ => simp [chkCtxGo] at h
          | selfIdx _ => simp [chkCtxGo] at h
      | neg A => cases body <;> simp [chkCtxGo] at h
      | box m A => cases body <;> simp [chkCtxGo] at h
      | eq p q => cases body <;> simp [chkCtxGo] at h
      | diag g A => cases body <;> simp [chkCtxGo] at h

/-! ### The MIXED-POLARITY telescope parser (`searchElseChain`, 2026-08-04)

Like `chkChainGo`, but walks BOTH descent polarities of `me`'s search spine in
lockstep with the candidate guard chain: a `□ g ψ'` antecedent matches a
`.search g ψ body e` layer descending the THEN slot (`SearchLayer2.thenL`), and a
`.neg (.plays P' Q' c)` antecedent matches a `.search g (.plays P Q c) q body`
layer descending the ELSE slot (`SearchLayer2.elseL`; the guard is stored
STRUCTURALLY as a plays-atom, so the reconstruction from the substituted
antecedent is the syntactic `==` check on the substituted components). Returns
the parsed layer list so the checker can charge `layersCost` (the else floor).
Sound and complete against `Pf.searchElseChain`. -/

def elseChainGo (me opp : Prog) : Formula → Prog → Option (List SearchLayer2 × Action)
  | .impl (.box g ψ') rest, .search g' ψ body e =>
      if g == g' && ψ' == ψ.subst me opp then
        match elseChainGo me opp rest body with
        | some (L, a) => some (.thenL g' ψ e :: L, a)
        | none => none
      else none
  | .impl (.neg (.plays P' Q' c')) rest, .search g (.plays P Q c) q body =>
      if P' == P.subst me opp && Q' == Q.subst me opp && decide (c' = c) then
        match elseChainGo me opp rest body with
        | some (L, a) => some (.elseL g P Q c q :: L, a)
        | none => none
      else none
  | .plays me' opp' a, .const a' =>
      if me' == me && opp' == opp && decide (a = a') then some ([], a) else none
  | _, _ => none

def chkSearchElseChain (k : Nat) : Formula → Bool
  | .impl A rest =>
      (match chainTail? rest with
       | some (me, opp) =>
           (match elseChainGo me opp (.impl A rest) me with
            | some (L, _) => decide (layersCost L + (Formula.impl A rest).size ≤ k)
            | none => false)
       | none => false)
  | _ => false

theorem elseChainGo_sound (me opp : Prog) : ∀ (n : Nat) (φ : Formula), φ.size ≤ n →
    ∀ (body : Prog) (L : List SearchLayer2) (a : Action),
      elseChainGo me opp φ body = some (L, a) →
      body = plug2 L (.const a) ∧
      φ = implChain (guards2 me opp L) (.plays me opp a) := by
  intro n
  induction n with
  | zero =>
      intro φ hφ
      have := Formula.size_pos φ
      omega
  | succ n ih =>
      intro φ hφ body L a h
      cases φ with
      | impl A rest =>
          cases A with
          | box g ψ' =>
              cases body with
              | search g' ψ pbody e =>
                  simp only [elseChainGo] at h
                  split at h
                  · rename_i hcond
                    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
                    obtain ⟨rfl, rfl⟩ := hcond
                    split at h
                    · rename_i L' a' hrec
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      have hrest : rest.size ≤ n := by
                        simp only [Formula.size] at hφ
                        omega
                      obtain ⟨hb, hφ'⟩ := ih rest hrest pbody L' a' hrec
                      refine ⟨?_, ?_⟩
                      · rw [hb]; exact rfl
                      · rw [hφ']; exact rfl
                    · simp at h
                  · simp at h
              | const a' => simp [elseChainGo] at h
              | self => simp [elseChainGo] at h
              | opp => simp [elseChainGo] at h
              | bot p => simp [elseChainGo] at h
              | sim p q => simp [elseChainGo] at h
              | ite b x p q => simp [elseChainGo] at h
              | tvote _ _ _ _ => simp [elseChainGo] at h
              | sys _ _ => simp [elseChainGo] at h
              | selfIdx _ => simp [elseChainGo] at h
          | neg X =>
              cases X with
              | plays P' Q' c' =>
                  cases body with
                  | search g gφ q pbody =>
                      cases gφ with
                      | plays P Q c =>
                          simp only [elseChainGo] at h
                          split at h
                          · rename_i hcond
                            simp only [Bool.and_eq_true, beq_iff_eq,
                              decide_eq_true_eq] at hcond
                            obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hcond
                            split at h
                            · rename_i L' a' hrec
                              simp only [Option.some.injEq, Prod.mk.injEq] at h
                              obtain ⟨rfl, rfl⟩ := h
                              have hrest : rest.size ≤ n := by
                                simp only [Formula.size] at hφ
                                omega
                              obtain ⟨hb, hφ'⟩ := ih rest hrest pbody L' a' hrec
                              refine ⟨?_, ?_⟩
                              · rw [hb]; exact rfl
                              · rw [hφ']; exact rfl
                            · simp at h
                          · simp at h
                      | impl A B => simp [elseChainGo] at h
                      | neg A => simp [elseChainGo] at h
                      | box m A => simp [elseChainGo] at h
                      | eq p' q' => simp [elseChainGo] at h
                      | diag m A => simp [elseChainGo] at h
                  | const a' => simp [elseChainGo] at h
                  | self => simp [elseChainGo] at h
                  | opp => simp [elseChainGo] at h
                  | bot p => simp [elseChainGo] at h
                  | sim p q => simp [elseChainGo] at h
                  | ite b x p q => simp [elseChainGo] at h
                  | tvote _ _ _ _ => simp [elseChainGo] at h
                  | sys _ _ => simp [elseChainGo] at h
                  | selfIdx _ => simp [elseChainGo] at h
              | impl A B => cases body <;> simp [elseChainGo] at h
              | neg A => cases body <;> simp [elseChainGo] at h
              | box m A => cases body <;> simp [elseChainGo] at h
              | eq p' q' => cases body <;> simp [elseChainGo] at h
              | diag m A => cases body <;> simp [elseChainGo] at h
          | plays p q c => cases body <;> simp [elseChainGo] at h
          | impl X Y => cases body <;> simp [elseChainGo] at h
          | eq p q => cases body <;> simp [elseChainGo] at h
          | diag gg X => cases body <;> simp [elseChainGo] at h
      | plays p q c =>
          cases body with
          | const a' =>
              simp only [elseChainGo] at h
              split at h
              · rename_i hcond
                simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hcond
                obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hcond
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨rfl, rfl⟩
              · simp at h
          | self => simp [elseChainGo] at h
          | opp => simp [elseChainGo] at h
          | bot pp => simp [elseChainGo] at h
          | sim pp qq => simp [elseChainGo] at h
          | ite b x pp qq => simp [elseChainGo] at h
          | search g ψ pp qq => simp [elseChainGo] at h
          | tvote _ _ _ _ => simp [elseChainGo] at h
          | sys _ _ => simp [elseChainGo] at h
          | selfIdx _ => simp [elseChainGo] at h
      | neg A => cases body <;> simp [elseChainGo] at h
      | box m A => cases body <;> simp [elseChainGo] at h
      | eq p q => cases body <;> simp [elseChainGo] at h
      | diag g A => cases body <;> simp [elseChainGo] at h

def chkLeaf (k : Nat) (φ : Formula) : Bool :=
  chkEqRefl k φ || chkSearchBranch k φ || chkSimStep k φ || chkBotSimStep k φ ||
  chkBotSearchStep k φ || chkIteBranchSearch k φ || chkEqNeg k φ ||
  chkImplRefl k φ || chkImplK k φ || chkSearchChain k φ || chkCtxChain k φ ||
  chkImplS k φ || chkSearchElseChain k φ

/-! ### `chkLeaf` soundness — each hit is a `Pf` leaf. -/

theorem chkLeaf_sound : ∀ k φ, chkLeaf k φ = true → Pf k φ := by
  intro k φ h
  unfold chkLeaf at h
  simp only [Bool.or_eq_true] at h
  rcases h with ((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
  · -- eqRefl
    unfold chkEqRefl at h
    split at h
    · rename_i p q
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨rfl, hsz⟩ := h
      exact Pf.eqRefl p hsz
    · simp at h
  · -- searchBranch
    unfold chkSearchBranch at h
    split at h
    · rename_i k₁ ψ' k₁' ψg aT aE opnt a
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩ := h
      exact Pf.searchBranch k₁ ψg a aE _ opnt rfl hsz
    · simp at h
  · -- simStep
    unfold chkSimStep at h
    split at h
    · rename_i pp qq a₁ p q opnt a₂
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩ := h
      exact Pf.simStep _ p q opnt a₁ rfl hsz
    · simp at h
  · -- botSimStep
    unfold chkBotSimStep at h
    split at h
    · rename_i pp qq a₁ p q opnt a₂
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩ := h
      exact Pf.botSimStep _ p q opnt a₁ rfl hsz
    · simp at h
  · -- botSearchStep
    unfold chkBotSearchStep at h
    split at h
    · rename_i k₁ ψ' k₁' ψg aT aE opnt a
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩ := h
      exact Pf.botSearchStep k₁ ψg a aE _ opnt rfl hsz
    · simp at h
  · -- iteBranchSearch_t
    unfold chkIteBranchSearch at h
    split at h
    · rename_i opnt1 z a' kg ψ' z' a'' kg' ψg c0 c1 q opnt2 c
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩, rfl⟩, hsz⟩ := h
      exact Pf.iteBranchSearch_t kg z a' c c1 ψg q _ opnt1 rfl hsz
    · simp at h
  · -- eqNeg
    unfold chkEqNeg at h
    split at h
    · rename_i p q
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hne, hsz⟩ := h
      exact Pf.eqNeg p q hne hsz
    · simp at h
  · -- implRefl
    unfold chkImplRefl at h
    split at h
    · rename_i A B
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨rfl, hsz⟩ := h
      exact Pf.implRefl A hsz
    · simp at h
  · -- implK
    unfold chkImplK at h
    split at h
    · rename_i A C B
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨rfl, hsz⟩ := h
      exact Pf.implK A C hsz
    · simp at h
  · -- searchChain: parse the telescope
    unfold chkSearchChain at h
    split at h
    · rename_i g ψ' rest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hsz, h⟩ := h
      split at h
      · rename_i me opp heq
        obtain ⟨L, a, hb, hφ⟩ := chkChainGo_sound me opp _ _ (Nat.le_refl _) _ h
        cases L with
        | nil => exact Formula.noConfusion hφ
        | cons hd tl =>
            obtain ⟨g₀, ψ₀, e₀⟩ := hd
            rw [hφ]
            exact Pf.searchChain g₀ ψ₀ e₀ tl a me opp hb (congrArg Formula.size hφ ▸ hsz)
      · simp at h
    · simp at h
  · -- ctxChain: parse the mixed telescope
    unfold chkCtxChain at h
    split at h
    · rename_i A rest
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨hsz, h⟩ := h
      split at h
      · rename_i me opp heq
        obtain ⟨L, a, hb, hφ⟩ := chkCtxGo_sound me opp _ _ (Nat.le_refl _) _ h
        cases L with
        | nil => exact Formula.noConfusion hφ
        | cons hd tl =>
            rw [hφ]
            exact Pf.ctxChain hd tl a me opp hb (congrArg Formula.size hφ ▸ hsz)
      · simp at h
    · simp at h
  · -- implS
    unfold chkImplS at h
    split at h
    · simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩ := h
      exact Pf.implS _ _ _ hsz
    · simp at h
  · -- searchElseChain: parse the mixed-polarity telescope
    unfold chkSearchElseChain at h
    split at h
    · rename_i A rest
      split at h
      · rename_i me opp heq
        split at h
        · rename_i L a hgo
          simp only [decide_eq_true_eq] at h
          obtain ⟨hb, hφ⟩ := elseChainGo_sound me opp _ _ (Nat.le_refl _) _ _ _ hgo
          cases L with
          | nil => exact Formula.noConfusion hφ
          | cons hd tl =>
              rw [hφ]
              exact Pf.searchElseChain hd tl a me opp hb (congrArg Formula.size hφ ▸ h)
        · simp at h
      · simp at h
    · simp at h

/-! ## 5. The `Pf` decider — the leaves + 15 reflective rules, atom-oracle-relative. -/

/-- The stand-in for deciding `AtomProvable` (the `PlaysProof`/eval side — T3.2). -/
def OracleSound (O : Nat → Formula → Bool) : Prop :=
  ∀ k φ, O k φ = true → AtomProvable k φ
def OracleComplete (O : Nat → Formula → Bool) : Prop :=
  ∀ k φ, AtomProvable k φ → O k φ = true

def chkWeaken (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A B =>
      (decide ((Formula.impl A B).size ≤ k) && rec (k - (Formula.impl A B).size) B) ||
      -- the contrapose leg (2026-07-28): a neg-neg implication may also come from
      -- `Pf.contrapose` on the un-negated implication, at the same budget arithmetic
      (match A, B with
       | .neg B', .neg A' =>
           decide ((Formula.impl A B).size ≤ k) &&
           rec (k - (Formula.impl A B).size) (.impl A' B')
       | _, _ => false)
  | _ => false

def chkSTS (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.box k₁ ψ')
      (.plays (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt c0) =>
      -- CITE model (2026-07-03): the rule pays `c_guard k₂` and checks the inner premise at
      -- its literal `k₂` — the premise budget is NOT linked to `k` (this is why decider
      -- completeness is the ∃-fuel/semidecidability form).
      decide (k₁ = k₁') && decide (c0 = c0') &&
      ψ' == ψ₁.subst (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt &&
      decide (c_guard k₂ + (Formula.impl (.box k₁ ψ')
        (.plays (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt c0)).size ≤ k) &&
      rec k₂ (ψ₂.subst (.search k₁' ψ₁ (.search k₂ ψ₂ (.const c0') (.const c1)) q) opnt)
  | _ => false

def chkITrans (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumFormula k).any fun ψ' =>
        decide (m₁ + (Formula.impl A C).size ≤ k) && rec m₁ (.impl A ψ') &&
        rec (k - (Formula.impl A C).size - m₁) (.impl ψ' C)
  | _ => false

def chkAtomBox (O : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.plays p q a) (.box kB (.plays p' q' a')) =>
      p == p' && q == q' && decide (a = a') &&
      decide (kB + (Formula.impl (.plays p q a) (.box kB (.plays p q a))).size ≤ k) &&
      O kB (.plays p q a)
  | _ => false

def chkBoxIntroE (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .box kIn ψ => decide (kIn + (Formula.box kIn ψ).size ≤ k) && rec kIn ψ
  | _ => false

def chkAppE (rec : Nat → Formula → Bool) (k : Nat) (φ : Formula) : Bool :=
  (List.range k).any fun m₁ => (enumFormula k).any fun φ' =>
    decide (m₁ + φ.size ≤ k) && rec m₁ (.impl φ' φ) && rec (k - φ.size - m₁) φ'

def chkAxK (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.box b ψ) (.box c α) =>
      decide ((Formula.impl (.box b ψ) (.box c α)).size ≤ k) &&
      ((List.range (c+1)).any fun a =>
        decide (a + b + α.size ≤ c) &&
        rec (k - (Formula.impl (.box b ψ) (.box c α)).size) (.box a (.impl ψ α)))
  | _ => false

def chkBox4E (k : Nat) : Formula → Bool
  | .impl (.box a ψ) (.box b (.box a' ψ')) =>
      ψ == ψ' && decide (a = a') && decide (a + (Formula.box a ψ).size ≤ b) &&
      decide ((Formula.impl (.box a ψ) (.box b (.box a ψ))).size ≤ k)
  | _ => false

def chkDiagFE (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.diag g t) (.impl (.box g' (.diag g'' t')) t'') =>
      decide (g = g') && decide (g = g'') && t == t' && t == t'' &&
      decide ((Formula.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        rec (k - (Formula.impl (.diag g t) (.impl (.box g (.diag g t)) t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkDiagBE (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl (.impl (.box g (.diag g' t)) t') (.diag g'' t'') =>
      decide (g = g') && decide (g = g'') && t == t' && t == t'' &&
      decide ((Formula.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size ≤ k) &&
      ((List.range (2 ^ (k+2))).any fun fb =>
        rec (k - (Formula.impl (.impl (.box g (.diag g t)) t) (.diag g t)).size)
          (.impl (.box fb t) t))
  | _ => false

def chkAxKfE (k : Nat) : Formula → Bool
  | .impl (.box a (.impl ψ α)) (.impl (.box b ψ') (.box c α')) =>
      ψ == ψ' && α == α' && decide (a + b + α.size ≤ c) &&
      decide ((Formula.impl (.box a (.impl ψ α)) (.impl (.box b ψ) (.box c α))).size ≤ k)
  | _ => false

def chkImpS2E (rec : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .impl A C =>
      (List.range k).any fun m₁ => (enumFormula k).any fun ψ' =>
        decide (m₁ + (Formula.impl A C).size ≤ k) && rec m₁ (.impl A (.impl ψ' C)) &&
        rec (k - (Formula.impl A C).size - m₁) (.impl A ψ')
  | _ => false

def chkBoxMonoE (k : Nat) : Formula → Bool
  | .impl (.box a ψ) (.box b ψ') =>
      ψ == ψ' && decide (a ≤ b) &&
      decide ((Formula.impl (.box a ψ) (.box b ψ)).size ≤ k)
  | _ => false

def chkAtomNeg (O : Nat → Formula → Bool) (k : Nat) : Formula → Bool
  | .neg (.plays p q aN) =>
      decide ((Formula.neg (.plays p q aN)).size ≤ k) &&
      ((O (k - (Formula.neg (.plays p q aN)).size) (.plays p q .C) && decide (aN ≠ Action.C)) ||
       (O (k - (Formula.neg (.plays p q aN)).size) (.plays p q .D) && decide (aN ≠ Action.D)))
  | _ => false

def decProv (O : Nat → Formula → Bool) : Nat → Nat → Formula → Bool
  | 0, _, _ => false
  | fuel+1, k, φ =>
      chkLeaf k φ ||
      O k φ ||
      chkWeaken (fun m ψ => decProv O fuel m ψ) k φ ||
      chkSTS (fun m ψ => decProv O fuel m ψ) k φ ||
      chkITrans (fun m ψ => decProv O fuel m ψ) k φ ||
      chkAtomBox O k φ ||
      chkBoxIntroE (fun m ψ => decProv O fuel m ψ) k φ ||
      chkAppE (fun m ψ => decProv O fuel m ψ) k φ ||
      chkAxK (fun m ψ => decProv O fuel m ψ) k φ ||
      chkBox4E k φ ||
      chkDiagFE (fun m ψ => decProv O fuel m ψ) k φ ||
      chkDiagBE (fun m ψ => decProv O fuel m ψ) k φ ||
      chkAxKfE k φ ||
      chkImpS2E (fun m ψ => decProv O fuel m ψ) k φ ||
      chkBoxMonoE k φ ||
      chkAtomNeg O k φ

/-! ### `decProv` soundness -/

/-- Every play certificate costs at least one character (each `PlaysProof` step pays ≥ 1). -/
theorem atomProvable_pos {k : Nat} {φ : Formula} (h : AtomProvable k φ) : 1 ≤ k := by
  obtain ⟨cert, hle⟩ := h
  cases cert <;> (simp only [numCost, c_leaf, c_node, c_guard] at hle; omega)

theorem decProv_sound (O : Nat → Formula → Bool) (hO : OracleSound O) :
    ∀ fuel k φ, decProv O fuel k φ = true → Pf k φ := by
  intro fuel
  induction fuel with
  | zero => intro k φ h; simp [decProv] at h
  | succ f ih =>
    intro k φ h
    rw [decProv] at h
    simp only [Bool.or_eq_true] at h
    rcases h with ((((((((((((((h | h) | h) | h) | h) | h) | h) | h) | h) | h) | h) | h)
      | h) | h) | h) | h
    · -- the source-transparency leaves
      exact chkLeaf_sound k φ h
    · -- atom
      exact Pf.atom (hO k φ h)
    · -- weakenImpl / contrapose (the two legs of the shared checker)
      unfold chkWeaken at h
      split at h
      · rename_i A B
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
        rcases h with ⟨hsz, hr⟩ | h2
        · exact Pf.weakenImpl A B _ (ih _ _ hr) (by omega)
        · split at h2
          · rename_i B' A'
            simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
            obtain ⟨hsz, hr⟩ := h2
            exact Pf.contrapose A' B' _ (ih _ _ hr) (by omega)
          · simp at h2
      · simp at h
    · -- searchThenSearch_t
      unfold chkSTS at h
      split at h
      · rename_i k₁ ψ' k₁' ψ₁ k₂ ψ₂ c0' c1 q opnt c0
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hsz⟩, hr⟩ := h
        exact Pf.searchThenSearch_t k₁ k₂ k₂ ψ₁ ψ₂ c0 c1 q _ opnt rfl
          (ih _ _ hr) (Nat.le_refl _) hsz
      · simp at h
    · -- implTrans
      unfold chkITrans at h
      split at h
      · rename_i A C
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨m₁, hm₁, ψ', _, ⟨hguard, h1⟩, h2⟩ := h
        exact Pf.implTrans A ψ' C m₁ _ (ih _ _ h1) (ih _ _ h2) (by omega)
      · simp at h
    · -- atomBoxImpl
      unfold chkAtomBox at h
      split at h
      · rename_i p q a kB p' q' a'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, hgate⟩, hOr⟩ := h
        exact Pf.atomBoxImpl kB p q a (hO _ _ hOr) hgate
      · simp at h
    · -- boxIntro
      unfold chkBoxIntroE at h
      split at h
      · rename_i kIn ψ
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hgate, hr⟩ := h
        exact Pf.boxIntro kIn k ψ (ih _ _ hr) hgate
      · simp at h
    · -- app
      unfold chkAppE at h
      simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨m₁, hm₁, φ', _, ⟨hguard, h1⟩, h2⟩ := h
      exact Pf.mp m₁ _ φ' φ (ih _ _ h1) (ih _ _ h2) (by omega)
    · -- axK
      unfold chkAxK at h
      split at h
      · rename_i b ψ c α
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hsz, a, _, hgate, hr⟩ := h
        exact Pf.axK a b c _ k ψ α (ih _ _ hr) hgate (by omega)
      · simp at h
    · -- box4
      unfold chkBox4E at h
      split at h
      · rename_i a ψ b a' ψ'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, hgate⟩, hsz⟩ := h
        exact Pf.box4 a b k ψ hgate hsz
      · simp at h
    · -- diagF
      unfold chkDiagFE at h
      split at h
      · rename_i g t g' g'' t' t''
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, hr⟩ := h
        exact Pf.diagF _ fb g k t (ih _ _ hr) (by omega)
      · simp at h
    · -- diagB
      unfold chkDiagBE at h
      split at h
      · rename_i g g' t t' g'' t''
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq,
          decide_eq_true_eq] at h
        obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, hsz⟩, fb, _, hr⟩ := h
        exact Pf.diagB _ fb g k t (ih _ _ hr) (by omega)
      · simp at h
    · -- axKf
      unfold chkAxKfE at h
      split at h
      · rename_i a ψ α b ψ' c α'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨⟨rfl, rfl⟩, hgate⟩, hsz⟩ := h
        exact Pf.axKf a b c k ψ α hgate hsz
      · simp at h
    · -- impS2
      unfold chkImpS2E at h
      split at h
      · rename_i A C
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨m₁, hm₁, ψ', _, ⟨hguard, h1⟩, h2⟩ := h
        exact Pf.impS2 A ψ' C m₁ _ k (ih _ _ h1) (ih _ _ h2) (by omega)
      · simp at h
    · -- boxMono
      unfold chkBoxMonoE at h
      split at h
      · rename_i a ψ b ψ'
        simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
        obtain ⟨⟨rfl, hab⟩, hsz⟩ := h
        exact Pf.boxMono a b k ψ hab hsz
      · simp at h

    · -- atomNeg
      unfold chkAtomNeg at h
      split at h
      · rename_i p q aN
        simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
        obtain ⟨hsz, hcase⟩ := h
        have hs1 := Formula.size_pos (Formula.neg (.plays p q aN))
        rcases hcase with ⟨hOr, hne⟩ | ⟨hOr, hne⟩
        · exact Pf.atomNeg p q .C aN _ (hO _ _ hOr) (fun hh => hne hh.symm) (by omega)
        · exact Pf.atomNeg p q .D aN _ (hO _ _ hOr) (fun hh => hne hh.symm) (by omega)
      · simp at h

/-! ## 7. THE ATOM SIDE — closing the knot (T3.2c part 2, milestone A).

`decCertG D` searches for a play CERTIFICATE within a cost budget, parametrically in a guard
decider `D` (consulted at `search_t`'s cited literal and for `search_f`'s refutations); the
knot is tied by plain structural recursion — `decFull (f+1) = decProv (certOG (decFull f) f)
(f+1)` — so `decFull` is a genuinely computable enumerator for the WHOLE system, atoms
included, with NO oracle hypothesis. Soundness reuses `decProv_sound` wholesale. -/

def decCertG (D : Nat → Formula → Bool) : Nat → Nat → Prog → Prog → Prog → Action → Bool
  | 0, _, _, _, _, _ => false
  | fuel+1, b, me, oppo, body, a =>
    match body with
    | .const c => decide (a = c) && decide (c_leaf ≤ b)
    | .self => decide (c_node ≤ b) && decCertG D fuel (b - c_node) me oppo me a
    | .opp => decide (c_node ≤ b) && decCertG D fuel (b - c_node) me oppo oppo a
    | .bot p => decide (c_node ≤ b) && decCertG D fuel (b - c_node) me oppo p a
    | .sim p q =>
        decide (c_node ≤ b) &&
        decCertG D fuel (b - c_node) (p.subst me oppo) (q.subst me oppo) (p.subst me oppo) a
    | .ite g a' p q =>
        decide (c_node ≤ b) &&
        ((List.range (b+1)).any fun m =>
          [Action.C, Action.D].any fun r =>
            decide (m + c_node ≤ b) &&
            decCertG D fuel m me oppo g r &&
            (if r == a' then decCertG D fuel (b - m - c_node) me oppo p a
             else decCertG D fuel (b - m - c_node) me oppo q a))
    | .search kg g p q =>
        (D kg (g.subst me oppo) && decide (c_guard kg + c_node ≤ b) &&
           decCertG D fuel (b - c_guard kg - c_node) me oppo p a)
        ||
        ((List.range (b+1)).any fun m =>
           D m (.neg (g.subst me oppo)) && decide (m + kg + c_node ≤ b) &&
           decCertG D fuel (b - m - kg - c_node) me oppo q a)
    | _ => false  -- tau constructors (`tvote`/`sys`/`selfIdx`): never certified

/-- The atom oracle induced by a guard decider: certificate search on plays-atoms. -/
def certOG (D : Nat → Formula → Bool) (fuel : Nat) : Nat → Formula → Bool :=
  fun k φ => match φ with
    | .plays p q a => decCertG D fuel k p q p a
    | _ => false

/-- **The knot**: the full enumerator — logic via `decProv`, atoms via the certificate
    search, each layer consulting the other one fuel lower. Computable, total. -/
def decFull : Nat → Nat → Formula → Bool
  | 0 => fun _ _ => false
  | fuel+1 => decProv (certOG (decFull fuel) fuel) (fuel+1)

/-! ### Soundness — every hit of the full enumerator is a real derivation. -/

theorem decCertG_sound (D : Nat → Formula → Bool)
    (hD : ∀ m ψ, D m ψ = true → Pf m ψ) :
    ∀ fuel b me oppo body a, decCertG D fuel b me oppo body a = true →
      ∃ n, PlaysProof me oppo body a n ∧ n ≤ b := by
  intro fuel
  induction fuel with
  | zero => intro b me oppo body a h; simp [decCertG] at h
  | succ f ih =>
    intro b me oppo body a h
    rw [decCertG.eq_def] at h
    simp only [] at h
    cases body with
    | const c =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨rfl, hb⟩ := h
        exact ⟨c_leaf, .const, hb⟩
    | self =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hb, hr⟩ := h
        obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
        exact ⟨n + c_node, .self cert, by omega⟩
    | opp =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hb, hr⟩ := h
        obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
        exact ⟨n + c_node, .opp cert, by omega⟩
    | bot p =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hb, hr⟩ := h
        obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
        exact ⟨n + c_node, .bot cert, by omega⟩
    | sim p q =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨hb, hr⟩ := h
        obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
        exact ⟨n + c_node, .sim cert, by omega⟩
    | ite g a' p q =>
        simp only [Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
          List.mem_range] at h
        obtain ⟨hb, m, hm, r, _, ⟨hmb, hg⟩, hbr⟩ := h
        obtain ⟨n₁, cert₁, hn₁⟩ := ih _ _ _ _ _ hg
        by_cases hr : (r == a') = true
        · rw [if_pos hr] at hbr
          obtain ⟨n₂, cert₂, hn₂⟩ := ih _ _ _ _ _ hbr
          exact ⟨n₁ + n₂ + c_node, .ite_t cert₁ hr cert₂, by omega⟩
        · rw [if_neg hr] at hbr
          obtain ⟨n₂, cert₂, hn₂⟩ := ih _ _ _ _ _ hbr
          have hrf : (r == a') = false := by simpa using hr
          exact ⟨n₁ + n₂ + c_node, .ite_f cert₁ hrf cert₂, by omega⟩
    | search kg g p q =>
        simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true,
          List.mem_range] at h
        rcases h with ⟨⟨hGuard, hcost⟩, hr⟩ | ⟨m, hm, ⟨hNeg, hcost⟩, hr⟩
        · obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
          exact ⟨n + c_guard kg + c_node, .search_t (hD _ _ hGuard) cert, by omega⟩
        · obtain ⟨n, cert, hn⟩ := ih _ _ _ _ _ hr
          exact ⟨n + m + kg + c_node, .search_f (hD _ _ hNeg) cert, by omega⟩

    | tvote _ _ _ _ => simp at h
    | sys _ _ => simp at h
    | selfIdx _ => simp at h
theorem certOG_sound (D : Nat → Formula → Bool)
    (hD : ∀ m ψ, D m ψ = true → Pf m ψ) (fuel : Nat) :
    OracleSound (certOG D fuel) := by
  intro k φ h
  unfold certOG at h
  split at h
  · rename_i p q a
    obtain ⟨n, cert, hn⟩ := decCertG_sound D hD fuel k p q p a h
    exact ⟨cert, hn⟩
  · simp at h

/-- **Soundness of the full enumerator** — three lines, riding `decProv_sound`. -/
theorem decFull_sound : ∀ fuel k φ, decFull fuel k φ = true → Pf k φ := by
  intro fuel
  induction fuel with
  | zero => intro k φ h; simp [decFull] at h
  | succ f ih =>
    intro k φ h
    exact decProv_sound _ (certOG_sound _ (fun m ψ => ih m ψ) f) (f+1) k φ h

/-! ## 9. T4.0 — `evalG`: COMPUTABLE evaluation backed by the enumerator.

`eval` is noncomputable only through its guard oracle `proofSearch k φ := decide (Pf k φ)`.
`decFull` semidecides `Pf` (§7–8), and — the repair's dividend — a DERIVABLE refutation
`Pf m (.neg φ)` semantically excludes `Pf k φ` at EVERY budget (soundness +
consistency: the honest replacement for what the deleted axiom faked with below-floor
certificates). So a 3-valued computable guard is sound in BOTH polarities, and plugging it into
`eval`'s recursion gives a computable partial evaluator `evalG` every commit of which is a real
classical play. Two guard instances:

* `guardFull` — the conceptual one: `decFull` on the guard, `decFull` on its negation. Sound,
  and CONVERGES on the whole r.e. fragment (`guardFull_converges_pos/_neg`) — but backward
  `decProv` sweeps make a `false` verdict exponentially expensive in practice.
* `guardFast` — the goal-directed one for plays-atom guards (the zoo's dominant shape):
  certificate search for the atom itself (Σ₁ side) / for the OTHER action (`Pf.atomNeg`'s
  supplier) — no top-level sweeps, so `#eval` actually runs. Strictly weaker commits, same
  soundness.

Escaping `none` in general — a computable fuel bound — is T4's remaining open item
(DECIDABILITY_ROADMAP.md). -/

/-- A guard decider is SOUND when every commitment agrees with `eval`'s oracle. -/
def GuardSound (G : Nat → Formula → Option Bool) : Prop :=
  ∀ k φ b, G k φ = some b → proofSearch k φ = b

/-- The enumerator-backed guard. Note the else side consults the negation at ANY budget
    `m ≤ fuelD`: a derivable refutation `⊢_m ¬φ` rules out `⊢_k φ` at every budget `k`
    (soundness + consistency). -/
def guardFull (fuelD : Nat) : Nat → Formula → Option Bool := fun k φ =>
  if decFull fuelD k φ then some true
  else if (List.range (fuelD + 1)).any (fun m => decFull fuelD m (.neg φ)) then some false
  else none

theorem guardFull_sound (fuelD : Nat) : GuardSound (guardFull fuelD) := by
  intro k φ b h
  unfold guardFull at h
  split at h
  · rename_i ht
    injection h with h; subst h
    exact (proofSearch_spec _ _).2 (decFull_sound _ _ _ ht)
  · split at h
    · rename_i hf
      injection h with h; subst h
      simp only [List.any_eq_true, List.mem_range] at hf
      obtain ⟨m, _, hm⟩ := hf
      have hnegI : ¬ φ.interp := Pf_sound _ _ (decFull_sound _ _ _ hm)
      cases hps : proofSearch k φ with
      | false => rfl
      | true => exact absurd (proofSearch_sound _ _ hps) hnegI
    · simp at h

/-- Goal-directed guard for plays-atom guards: no `decProv` entry point, so no cut sweeps
    at the top level (guard hops inside `decCertG` still consult `decFull`). -/
def guardFast (fuelD : Nat) : Nat → Formula → Option Bool := fun k φ =>
  match φ with
  | .plays p q a =>
      if decCertG (decFull fuelD) fuelD k p q p a then some true
      else if (List.range (fuelD + 1)).any (fun m =>
          [Action.C, Action.D].any (fun r =>
            decide (r ≠ a) && decCertG (decFull fuelD) fuelD m p q p r)) then some false
      else none
  | _ => none

theorem guardFast_sound (fuelD : Nat) : GuardSound (guardFast fuelD) := by
  intro k φ b h
  unfold guardFast at h
  split at h
  · rename_i p q a
    split at h
    · rename_i ht
      injection h with h; subst h
      obtain ⟨n, cert, hn⟩ :=
        decCertG_sound (decFull fuelD) (fun m ψ => decFull_sound fuelD m ψ) fuelD k p q p a ht
      exact (proofSearch_spec _ _).2 (Pf.atom (AtomProvable.mk cert hn))
    · split at h
      · rename_i hf
        injection h with h; subst h
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true,
          decide_eq_true_eq] at hf
        obtain ⟨m, _, r, _, hne, hcert⟩ := hf
        obtain ⟨n, cert, _⟩ :=
          decCertG_sound (decFull fuelD) (fun m' ψ => decFull_sound fuelD m' ψ) fuelD m
            p q p r hcert
        have hneg : Pf (n + (Formula.neg (.plays p q a)).size) (.neg (.plays p q a)) :=
          Pf.atomNeg p q r a n (AtomProvable.mk cert le_rfl) hne le_rfl
        have hnegI : ¬ (Formula.plays p q a).interp := Pf_sound _ _ hneg
        cases hps : proofSearch k (.plays p q a) with
        | false => rfl
        | true => exact absurd (proofSearch_sound _ _ hps) hnegI
      · simp at h
  · simp at h

/-- Goal-directed guard EXTENDING `guardFast` beyond plays-atoms (2026-07-29):
    * `.neg (.plays p q a)` — the refutation twin, both polarities goal-directed:
      TRUE on a certificate of a DIFFERENT action `r ≠ a` whose `Pf.atomNeg`
      transcript fits `k`; FALSE on a certificate of `a` itself (soundness refutes
      the negation at EVERY budget — no floor to clear).
    * any other non-`.plays` guard — FALSE once `k < φ.size`: by `pf_size_or_atom`
      a proof either pays its conclusion's size or concludes a plays-atom, so an
      oversized non-atom guard is unprovable outright (the size floor). This arm
      decides the small-budget cells `guardFast` leaves `none` — e.g. a searcher
      whose substituted guard mentions a same-size partner.
    Plays-atoms delegate to `guardFast`. Strictly more commits, same soundness. -/
def guardFastN (fuelD : Nat) : Nat → Formula → Option Bool := fun k φ =>
  match φ with
  | .plays p q a => guardFast fuelD k (.plays p q a)
  | .neg (.plays p q a) =>
      -- size floor FIRST: sound unconditionally, and it short-circuits before any
      -- `decCertG` hop can reach a `.search` subject and trigger a `decFull` sweep
      -- (self-play at real budgets OOMs otherwise — that sweep is exponential).
      if k < (Formula.neg (.plays p q a)).size then some false
      else if (List.range (fuelD + 1)).any (fun m =>
          [Action.C, Action.D].any (fun r =>
            decide (r ≠ a) && decide (m + (Formula.neg (.plays p q a)).size ≤ k) &&
            decCertG (decFull fuelD) fuelD m p q p r)) then some true
      else if (List.range (fuelD + 1)).any (fun m =>
          decCertG (decFull fuelD) fuelD m p q p a) then some false
      else none
  | φ => if k < φ.size then some false else none

theorem guardFastN_sound (fuelD : Nat) : GuardSound (guardFastN fuelD) := by
  intro k φ b h
  unfold guardFastN at h
  split at h
  · exact guardFast_sound fuelD _ _ _ h
  · rename_i p q a
    split at h
    · rename_i hsz
      injection h with h; subst h
      cases hps : proofSearch k (.neg (.plays p q a)) with
      | false => rfl
      | true =>
          exfalso
          rcases pf_size_or_atom ((proofSearch_spec _ _).1 hps) with hle | hatom
          · omega
          · cases hatom
    · split at h
      · rename_i ht
        injection h with h; subst h
        simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true,
          decide_eq_true_eq] at ht
        obtain ⟨m, _, r, _, ⟨hne, hbud⟩, hcert⟩ := ht
        obtain ⟨n, cert, hn⟩ :=
          decCertG_sound (decFull fuelD) (fun m' ψ => decFull_sound fuelD m' ψ) fuelD m
            p q p r hcert
        exact (proofSearch_spec _ _).2
          (Pf.atomNeg p q r a n (AtomProvable.mk cert le_rfl) hne (by omega))
      · split at h
        · rename_i hf
          injection h with h; subst h
          simp only [List.any_eq_true, List.mem_range] at hf
          obtain ⟨m, _, hcert⟩ := hf
          obtain ⟨n, cert, hn⟩ :=
            decCertG_sound (decFull fuelD) (fun m' ψ => decFull_sound fuelD m' ψ) fuelD m
              p q p a hcert
          have hI : (Formula.plays p q a).interp :=
            Pf_sound _ _ (Pf.atom (AtomProvable.mk cert hn))
          cases hps : proofSearch k (.neg (.plays p q a)) with
          | false => rfl
          | true =>
              have hnI : ¬ (Formula.plays p q a).interp :=
                Pf_sound _ _ ((proofSearch_spec _ _).1 hps)
              exact absurd hI hnI
        · simp at h
  · rename_i hnp hnn
    split at h
    · rename_i hsz
      injection h with h; subst h
      cases hps : proofSearch k φ with
      | false => rfl
      | true =>
          exfalso
          rcases pf_size_or_atom ((proofSearch_spec _ _).1 hps) with hle | hatom
          · omega
          · cases hatom
            exact hnp _ _ _ rfl
    · simp at h

/-- The COMPUTABLE evaluator: `eval`'s recursion verbatim, with the `.search` guard consulting
    a 3-valued computable `G`; `none` guard ⇒ `none` result. Parametric in `G` so any sound
    guard (present or future) inherits the one soundness proof. -/
def evalG (G : Nat → Formula → Option Bool) : Nat → (me opponent body : Prog) → Option Action
  | 0, _, _, _ => none
  | n+1, me, opponent, body => match body with
    | .const a => some a
    | .self => evalG G n me opponent me
    | .opp => evalG G n me opponent opponent
    | .bot p => evalG G n me opponent p
    | .sim p q =>
        let p' := p.subst me opponent
        let q' := q.subst me opponent
        evalG G n p' q' p'
    | .ite b a p q =>
        match evalG G n me opponent b with
        | some r => if r == a then evalG G n me opponent p else evalG G n me opponent q
        | none => none
    | .search k φ p q =>
        match G k (φ.subst me opponent) with
        | some true => evalG G n me opponent p
        | some false => evalG G n me opponent q
        | none => none
    | _ => none  -- tau constructors: undetermined (sound, incomplete)

/-- **Faithfulness at the SAME fuel**: every `evalG` commit is `eval`'s answer. (Sharper than
    `evalC`'s `∃ N` form — a sound guard agrees with the oracle pointwise, so the two
    recursions run in lockstep.) -/
theorem evalG_sound (G : Nat → Formula → Option Bool) (hG : GuardSound G) :
    ∀ n me opponent body a, evalG G n me opponent body = some a →
      eval n me opponent body = some a := by
  intro n
  induction n with
  | zero => intro me opponent body a h; simp [evalG] at h
  | succ n ih =>
    intro me opponent body a h
    cases body with
    | const c => rw [evalG] at h; rw [eval]; exact h
    | self => rw [evalG] at h; rw [eval]; exact ih _ _ _ _ h
    | opp => rw [evalG] at h; rw [eval]; exact ih _ _ _ _ h
    | bot p => rw [evalG] at h; rw [eval]; exact ih _ _ _ _ h
    | sim p q => rw [evalG] at h; rw [eval]; exact ih _ _ _ _ h
    | ite g a' p q =>
        rw [evalG] at h
        cases hb : evalG G n me opponent g with
        | none => rw [hb] at h; simp at h
        | some r =>
            rw [hb] at h
            replace h : (if (r == a') = true then evalG G n me opponent p
                else evalG G n me opponent q) = some a := h
            rw [eval, ih _ _ _ _ hb]
            simp only [bind, Option.bind]
            by_cases hr : (r == a') = true
            · rw [if_pos hr] at h ⊢; exact ih _ _ _ _ h
            · rw [if_neg hr] at h ⊢; exact ih _ _ _ _ h
    | search kg φg p q =>
        rw [evalG] at h
        cases hg : G kg (φg.subst me opponent) with
        | none => rw [hg] at h; simp at h
        | some gb =>
            rw [hg] at h
            have hps := hG _ _ _ hg
            cases gb with
            | true =>
                replace h : evalG G n me opponent p = some a := h
                rw [eval, if_pos hps]
                exact ih _ _ _ _ h
            | false =>
                replace h : evalG G n me opponent q = some a := h
                rw [eval, if_neg (by simp [hps])]
                exact ih _ _ _ _ h

    | tvote _ _ _ _ => simp [evalG] at h
    | sys _ _ => simp [evalG] at h
    | selfIdx _ => simp [evalG] at h
def playG (G : Nat → Formula → Option Bool) (fuel : Nat) (me opponent : Prog) :
    Option Action :=
  evalG G fuel me opponent me

def outcomeG (G : Nat → Formula → Option Bool) (fuel : Nat) (p q : Prog) : Option Outcome := do
  let a ← playG G fuel p q
  let b ← playG G fuel q p
  some (a, b)

theorem playG_sound (G : Nat → Formula → Option Bool) (hG : GuardSound G)
    (fuel : Nat) (me opponent : Prog) (a : Action) :
    playG G fuel me opponent = some a → play fuel me opponent = some a :=
  fun h => evalG_sound G hG _ _ _ _ _ h

/-- **Every `#eval`'d outcome below is a machine-checked classical outcome.** -/
theorem outcomeG_sound (G : Nat → Formula → Option Bool) (hG : GuardSound G)
    (fuel : Nat) (p q : Prog) (o : Outcome) :
    outcomeG G fuel p q = some o → outcome fuel p q = some o := by
  intro h
  unfold outcomeG at h
  unfold outcome
  cases ha : playG G fuel p q with
  | none => rw [ha] at h; simp [bind, Option.bind] at h
  | some a =>
      rw [ha] at h
      simp only [bind, Option.bind] at h
      cases hb : playG G fuel q p with
      | none => rw [hb] at h; simp [] at h
      | some b =>
          rw [hb] at h
          simp only [] at h
          rw [playG_sound G hG _ _ _ _ ha]
          simp only [bind, Option.bind]
          rw [playG_sound G hG _ _ _ _ hb]
          simp only []
          exact h


end PD.T31
