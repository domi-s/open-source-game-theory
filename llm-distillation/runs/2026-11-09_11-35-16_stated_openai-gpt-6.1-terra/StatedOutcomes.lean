import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Outcome
import PrisonersDilemma.Bots.CooperateBot
import PrisonersDilemma.Bots.DefectBot
import PrisonersDilemma.Bots.DupocBot
import PrisonersDilemma.Bots.CupodBot
import PrisonersDilemma.Bots.CupodTrollBot
import PrisonersDilemma.Bots.DBot
import PrisonersDilemma.Bots.OBot
import PrisonersDilemma.Bots.TitForTatBot
import PrisonersDilemma.Bots.EBot
import PrisonersDilemma.Bots.MirrorBot
import PrisonersDilemma.Theorems.DupocBot.Helpers
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.Helpers

open PD PD.BaseTheorems PD.Bots PD.Theorems
namespace PD.Stated

def E (k : Nat) (g₁ g₂ : Formula) : Prog :=
  .search k g₁ (.const .D) (.search k g₂ (.const .C) (.const .D))

/-- Shape of terra S3: cooperation only behind the INNER else. -/
def T (k : Nat) (g₁ g₂ : Formula) : Prog :=
  .search k g₁ (.search k g₂ (.const .D) (.const .C)) (.const .D)

/-- **C floor, shape E**: no proof of ≤ k characters tails at "E plays C vs O". -/
theorem E_C_floor (k : Nat) (g₁ g₂ : Formula) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k → TailTo (.plays (E k g₁ g₂) O .C) φ → False := by
  refine no_provable_tailTo_floor k _ O .C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro K hK hA
    cases hA with
    | mk hpp hn =>
      cases hpp with
      | search_t _ hbr => cases hbr
      | search_f _ _ => simp only [c_node] at hn; omega
  · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, _, _, _, h⟩) <;> simp [E] at h
  · intro defs i h; simp [E] at h
  · intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp [E] at h
  · intro L h
    cases L with
    | nil => simp [searchPlug, E] at h
    | cons hd tl =>
        obtain ⟨g', ψ', e'⟩ := hd
        simp only [searchPlug, E, Prog.search.injEq] at h
        obtain ⟨-, -, h, -⟩ := h
        cases tl with
        | nil => simp [searchPlug] at h
        | cons hd' tl' => obtain ⟨_, _, _⟩ := hd'; simp [searchPlug] at h
  · intro hd L h
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, E, Prog.search.injEq] at h
        exact const_ne_ctxPlug (by decide) L h.2.2.1
    | iteL z aT other => simp [ctxPlug, E] at h
  · intro hd L hme
    cases hd with
    | thenL g ψ e =>
        exfalso
        simp only [plug2, E, Prog.search.injEq] at hme
        obtain ⟨-, -, h, -⟩ := hme
        cases L with
        | nil => simp [plug2] at h
        | cons hd2 tl2 => cases hd2 <;> simp [plug2] at h
    | elseL g P' Q' c' q =>
        simp only [plug2, E, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega

/-- **C floor, shape T** (S3): its only C is the inner else-play. -/
theorem T_C_floor (k : Nat) (g₁ g₂ : Formula) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k → TailTo (.plays (T k g₁ g₂) O .C) φ → False := by
  refine no_provable_tailTo_floor k _ O .C ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro K hK hA
    cases hA with
    | mk hpp hn =>
      cases hpp with
      | search_t _ hbr =>
          cases hbr with
          | search_t _ hc => cases hc
          | search_f _ _ => simp only [c_node] at hn; omega
      | search_f _ hbr => cases hbr
  · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, _, _, _, h⟩) <;> simp [T] at h
  · intro defs i h; simp [T] at h
  · intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp [T] at h
  · intro L h
    cases L with
    | nil => simp [searchPlug, T] at h
    | cons hd tl =>
        obtain ⟨g', ψ', e'⟩ := hd
        simp only [searchPlug, T, Prog.search.injEq] at h
        obtain ⟨-, -, h, -⟩ := h
        cases tl with
        | nil => simp [searchPlug] at h
        | cons hd' tl' =>
            obtain ⟨g'', ψ'', e''⟩ := hd'
            simp only [searchPlug, Prog.search.injEq] at h
            obtain ⟨-, -, h, -⟩ := h
            cases tl' with
            | nil => simp [searchPlug] at h
            | cons hd'' tl'' => obtain ⟨_, _, _⟩ := hd''; simp [searchPlug] at h
  · intro hd L h
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, T, Prog.search.injEq] at h
        obtain ⟨-, -, h, -⟩ := h
        cases L with
        | nil => simp [ctxPlug] at h
        | cons hd' tl' =>
            cases hd' with
            | searchL g' ψ' e' =>
                simp only [ctxPlug, Prog.search.injEq] at h
                exact const_ne_ctxPlug (by decide) tl' h.2.2.1
            | iteL z' aT' other' => simp [ctxPlug] at h
    | iteL z aT other => simp [ctxPlug, T] at h
  · intro hd L hme
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, T, Prog.search.injEq] at hme
        obtain ⟨rfl, -, h, -⟩ := hme
        cases L with
        | nil => simp [plug2] at h
        | cons hd2 tl2 =>
            cases hd2 with
            | thenL g2 ψ2 e2 =>
                exfalso
                simp only [plug2, Prog.search.injEq] at h
                obtain ⟨-, -, h, -⟩ := h
                cases tl2 with
                | nil => simp [plug2] at h
                | cons hd3 tl3 => cases hd3 <;> simp [plug2] at h
            | elseL g2 P2 Q2 c2 q2 =>
                simp only [plug2, Prog.search.injEq] at h
                obtain ⟨rfl, -, -, -⟩ := h
                simp only [layersCost, layerCost, c_node]
                omega
    | elseL g P' Q' c' q =>
        simp only [plug2, T, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega


/-! ## The terra bots, verbatim from `classes.json` -/

def StatedBot0 (k : Nat) : Prog := .search k (.impl (.plays .self .opp Action.D) (.plays .opp .self Action.C)) (.const Action.D) (.search k (.impl (.plays .self .opp Action.C) (.plays .opp .self Action.C)) (.const Action.C) (.const Action.D))
def StatedBot1 (k : Nat) : Prog := .search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)
def StatedBot2 (k : Nat) : Prog := .search k (.eq .opp (.const Action.C)) (.const Action.D) (.search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D))
def StatedBot3 (k : Nat) : Prog := .search k (.plays .opp .self Action.C) (.search k (.eq .opp (.const Action.C)) (.const Action.D) (.const Action.C)) (.const Action.D)
def StatedBot4 (k : Nat) : Prog := .search k (.plays .opp (.bot (.const Action.D)) Action.C) (.const Action.D) (.search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D))

/-! ## Generic helpers -/

theorem ps_false_of_not {k : Nat} {φ : Formula} (h : ¬ φ.interp) : proofSearch k φ = false := by
  cases hp : proofSearch k φ with
  | false => rfl
  | true => exact absurd (proofSearch_sound k φ hp) h

theorem ps_false_of_floor {k : Nat} {T φ : Formula}
    (hfl : ∀ K ψ, Pf K ψ → K ≤ k → TailTo T ψ → False) (ht : TailTo T φ) :
    proofSearch k φ = false := by
  cases hp : proofSearch k φ with
  | false => rfl
  | true => exact (hfl k φ ((proofSearch_spec k φ).1 hp) le_rfl ht).elim

theorem not_pf_of_ps_false {k : Nat} {φ : Formula} (h : proofSearch k φ = false) : ¬ Pf k φ :=
  fun hp => by rw [(proofSearch_spec k φ).2 hp] at h; exact Bool.noConfusion h

theorem not_plays_of {n : Nat} {p q : Prog} {a b : Action}
    (h : play n p q = some a) (hne : a ≠ b) : ¬ (Formula.plays p q b).interp := by
  rintro ⟨m, hm⟩; exact hne (play_unique h hm)

/-- Searcher with constant branches. -/
theorem srch_t {k n : Nat} {g : Formula} {a b : Action} {me O : Prog}
    (hme : me = .search k g (.const a) (.const b)) (h : proofSearch k (g.subst me O) = true) :
    play (n + 2) me O = some a := by subst hme; simp [play, eval, h]
theorem srch_f {k n : Nat} {g : Formula} {a b : Action} {me O : Prog}
    (hme : me = .search k g (.const a) (.const b)) (h : proofSearch k (g.subst me O) = false) :
    play (n + 2) me O = some b := by subst hme; simp [play, eval, h]

/-- Shape E (S0/S2/S4). -/
theorem E_D1 {k n : Nat} {g₁ g₂ : Formula} {me O : Prog}
    (hme : me = .search k g₁ (.const .D) (.search k g₂ (.const .C) (.const .D)))
    (h1 : proofSearch k (g₁.subst me O) = true) : play (n + 3) me O = some .D := by
  subst hme; simp [play, eval, h1]
theorem E_D2 {k n : Nat} {g₁ g₂ : Formula} {me O : Prog}
    (hme : me = .search k g₁ (.const .D) (.search k g₂ (.const .C) (.const .D)))
    (h1 : proofSearch k (g₁.subst me O) = false) (h2 : proofSearch k (g₂.subst me O) = false) :
    play (n + 3) me O = some .D := by
  subst hme; simp [play, eval, h1, h2]
theorem E_C {k n : Nat} {g₁ g₂ : Formula} {me O : Prog}
    (hme : me = .search k g₁ (.const .D) (.search k g₂ (.const .C) (.const .D)))
    (h1 : proofSearch k (g₁.subst me O) = false) (h2 : proofSearch k (g₂.subst me O) = true) :
    play (n + 3) me O = some .C := by
  subst hme; simp [play, eval, h1, h2]

/-- Shape T (S3). -/
theorem T_D1 {k n : Nat} {g₁ g₂ : Formula} {me O : Prog}
    (hme : me = .search k g₁ (.search k g₂ (.const .D) (.const .C)) (.const .D))
    (h1 : proofSearch k (g₁.subst me O) = false) : play (n + 3) me O = some .D := by
  subst hme; simp [play, eval, h1]
theorem T_D2 {k n : Nat} {g₁ g₂ : Formula} {me O : Prog}
    (hme : me = .search k g₁ (.search k g₂ (.const .D) (.const .C)) (.const .D))
    (h1 : proofSearch k (g₁.subst me O) = true) (h2 : proofSearch k (g₂.subst me O) = true) :
    play (n + 3) me O = some .D := by
  subst hme; simp [play, eval, h1, h2]
theorem T_C {k n : Nat} {g₁ g₂ : Formula} {me O : Prog}
    (hme : me = .search k g₁ (.search k g₂ (.const .D) (.const .C)) (.const .D))
    (h1 : proofSearch k (g₁.subst me O) = true) (h2 : proofSearch k (g₂.subst me O) = false) :
    play (n + 3) me O = some .C := by
  subst hme; simp [play, eval, h1, h2]

/-- Every transcript of a searcher whose outer guard is unprovable at its own budget
    pays the floor. -/
theorem search_probe {me O body : Prog} {k : Nat} {g : Formula} {pT pE : Prog} {a : Action}
    {n : Nat} (hb : body = .search k g pT pE) (h : PlaysProof me O body a n)
    (hg : ¬ Pf k (g.subst me O)) : k ≤ n := by
  subst hb
  cases h with
  | search_t hP _ => exact absurd hP hg
  | search_f _ _ => simp only [c_node]; omega

set_option maxHeartbeats 1000000 in
/-- **Generalized probe-first floor**: `no_provable_probeFirst_tail` with the opponent's
    floor given as a hypothesis on its probe transcripts instead of via a false guard
    of a fixed shape. -/
theorem probe_floor (k : Nat) (z p q X : Prog) (aT aTgt : Action)
    (hprobe : ∀ a n, PlaysProof X (.bot z) X a n → k ≤ n)
    (hshape : ∀ k' ψ c0 c1, p ≠ .search k' ψ (.const c0) (.const c1))
    (hpthen : ∀ (L : List CtxLayer), p ≠ ctxPlug L (.const aTgt)) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (.ite (.sim .opp (.bot z)) aT p q) X aTgt) φ → False := by
  refine no_provable_tailTo_floor k _ _ _ ?_ ?_ (by intro _ _; simp) ?_ ?_ ?_ ?_
  · intro K hK hA
    cases hA with
    | mk hpp hn =>
      cases hpp with
      | ite_t hg hr hbr =>
          cases hg with
          | sim hin =>
            simp only [Prog.subst] at hin
            have := hprobe _ _ hin
            simp only [c_node] at hn; omega
      | ite_f hg hr hbr =>
          cases hg with
          | sim hin =>
            simp only [Prog.subst] at hin
            have := hprobe _ _ hin
            simp only [c_node] at hn; omega
  · rintro (⟨k', ψ, a, b, h⟩ | ⟨p', r, h⟩ | ⟨p', r, h⟩ | ⟨k', ψ, a, b, h⟩ |
            ⟨w, a', k', ψ, c0, c1, r, h⟩)
    · simp at h
    · simp at h
    · simp at h
    · simp at h
    · simp only [Prog.ite.injEq] at h
      exact hshape _ _ _ _ h.2.2.1
  · intro k₁ ψ₁ k₂ ψ₂ c1 q' h
    simp at h
  · intro L h
    cases L with
    | nil => simp [searchPlug] at h
    | cons hd tl => obtain ⟨g, ψ, e⟩ := hd; simp [searchPlug] at h
  · intro hd L h
    cases hd with
    | searchL g' ψ' e' => simp [ctxPlug] at h
    | iteL z' aT' other' =>
        simp only [ctxPlug, Prog.ite.injEq] at h
        exact hpthen L h.2.2.1
  · intro hd L h
    cases hd <;> simp [plug2] at h

/-- Package two plays (at possibly different offsets) into an outcome at pad `P`. -/
theorem cell {L R : Prog} {a b : Action} {c₁ c₂ P : Nat}
    (hA : ∀ n, play (n + c₁) L R = some a) (hB : ∀ n, play (n + c₂) R L = some b)
    (h1 : c₁ ≤ P) (h2 : c₂ ≤ P) : ∀ fuel, outcome (fuel + P) L R = some (a, b) := by
  intro fuel
  have e1 : fuel + P = (fuel + P - c₁) + c₁ := by omega
  have e2 : fuel + P = (fuel + P - c₂) + c₂ := by omega
  apply outcome_of_plays
  · rw [e1]; exact hA _
  · rw [e2]; exact hB _

/-! ## Simple zoo bots against anything -/

theorem cb_play (n : Nat) (X : Prog) : play (n + 1) CooperateBot X = some .C := by
  simp [play, eval, CooperateBot]
theorem db_play (n : Nat) (X : Prog) : play (n + 1) DefectBot X = some .D := by
  simp [play, eval, DefectBot]

/-- A probe `.sim .opp (.bot z)` reads the opponent's play against `.bot z`. -/
theorem probe_eval {n : Nat} {me X z : Prog} {a : Action} (h : play n X (.bot z) = some a)
    (m : Nat) (hm : n + 1 ≤ m) : eval m me X (.sim .opp (.bot z)) = some a :=
  eval_mono_le (eval_sim_opp_bot_of_play n me X z a h) m hm

theorem dbot_play_C {n : Nat} {X : Prog} (h : play n X (.bot DefectBot) = some .D) :
    play (n + 3) DBot X = some .C := by
  show eval (n + 3) DBot X (.ite (.sim .opp (.bot DefectBot)) .C (.const .D) (.const .C)) = _
  rw [eval_ite_from_guard (n + 2) DBot X _ _ _ .C .D (probe_eval h _ (by omega)),
    if_neg (by decide)]
  simp [eval]

theorem tft_play {n : Nat} {X : Prog} {a : Action} (h : play n X (.bot CooperateBot) = some a) :
    play (n + 3) TitForTatBot X = some a := by
  show eval (n + 3) TitForTatBot X
    (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C) (.const .D)) = _
  rw [eval_ite_from_guard (n + 2) TitForTatBot X _ _ _ .C a (probe_eval h _ (by omega))]
  cases a
  · rw [if_pos (by decide)]; simp [eval]
  · rw [if_neg (by decide)]; simp [eval]

theorem obot_D_of_CB {n : Nat} {X : Prog} (h : play n X (.bot CooperateBot) = some .D) :
    play (n + 3) OBot X = some .D := by
  show eval (n + 3) OBot X (.ite (.sim .opp (.bot CooperateBot)) .C
    (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) (.const .D)) = _
  rw [eval_ite_from_guard (n + 2) OBot X _ _ _ .C .D (probe_eval h _ (by omega)),
    if_neg (by decide)]
  simp [eval]

theorem obot_D_of_CB_DB {n : Nat} {X : Prog} (hc : play n X (.bot CooperateBot) = some .C)
    (hd : play n X (.bot DefectBot) = some .D) : play (n + 4) OBot X = some .D := by
  show eval (n + 4) OBot X (.ite (.sim .opp (.bot CooperateBot)) .C
    (.ite (.sim .opp (.bot DefectBot)) .C (.const .C) (.const .D)) (.const .D)) = _
  rw [eval_ite_from_guard (n + 3) OBot X _ _ _ .C .C (probe_eval hc _ (by omega)),
    if_pos (by decide),
    eval_ite_from_guard (n + 2) OBot X _ _ _ .C .D (probe_eval hd _ (by omega)),
    if_neg (by decide)]
  simp [eval]

theorem ebot_unfold (m : Nat) (X : Prog) :
    eval m EBot X EBot = eval m EBot X (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) := rfl

theorem ebot_C_of_CB {n : Nat} {X : Prog} (hd : play n X (.bot DefectBot) = some .D)
    (hc : play n X (.bot CooperateBot) = some .C) : play (n + 4) EBot X = some .C := by
  show eval (n + 4) EBot X EBot = _
  rw [ebot_unfold,
    eval_ite_from_guard (n + 3) EBot X _ _ _ .C .D (probe_eval hd _ (by omega)),
    if_neg (by decide),
    eval_ite_from_guard (n + 2) EBot X _ _ _ .C .C (probe_eval hc _ (by omega)),
    if_pos (by decide)]
  simp [eval]

theorem ebot_C_of_M {n : Nat} {X : Prog} (hd : play n X (.bot DefectBot) = some .D)
    (hc : play n X (.bot CooperateBot) = some .D) (hm : play n X (.bot MirrorBot) = some .C) :
    play (n + 5) EBot X = some .C := by
  show eval (n + 5) EBot X EBot = _
  rw [ebot_unfold,
    eval_ite_from_guard (n + 4) EBot X _ _ _ .C .D (probe_eval hd _ (by omega)),
    if_neg (by decide),
    eval_ite_from_guard (n + 3) EBot X _ _ _ .C .D (probe_eval hc _ (by omega)),
    if_neg (by decide),
    eval_ite_from_guard (n + 2) EBot X _ _ _ .C .C (probe_eval hm _ (by omega)),
    if_pos (by decide)]
  simp [eval]

theorem ebot_D_all {n : Nat} {X : Prog} (hd : play n X (.bot DefectBot) = some .D)
    (hc : play n X (.bot CooperateBot) = some .D) (hm : play n X (.bot MirrorBot) = some .D) :
    play (n + 5) EBot X = some .D := by
  show eval (n + 5) EBot X EBot = _
  rw [ebot_unfold,
    eval_ite_from_guard (n + 4) EBot X _ _ _ .C .D (probe_eval hd _ (by omega)),
    if_neg (by decide),
    eval_ite_from_guard (n + 3) EBot X _ _ _ .C .D (probe_eval hc _ (by omega)),
    if_neg (by decide),
    eval_ite_from_guard (n + 2) EBot X _ _ _ .C .D (probe_eval hm _ (by omega)),
    if_neg (by decide)]
  simp [eval]

theorem botM_play {n : Nat} {X : Prog} {a : Action} (h : play n X (.bot MirrorBot) = some a) :
    play (n + 3) (.bot MirrorBot) X = some a := by
  have h' : eval (n + 1) X (.bot MirrorBot) X = some a := eval_mono_le h (n + 1) (by omega)
  show eval (n + 3) (.bot MirrorBot) X (.bot MirrorBot) = some a
  simp only [eval, Prog.subst, MirrorBot] at h' ⊢
  exact h'


/-! ## Cell facts. Throughout `hb : 40 * Nat.log2 k + 400 ≤ k` (all large k). -/

section Facts
variable {k : Nat}

/-! ### S0's guards self-refute whenever the opponent does not cooperate with it -/

theorem s0_g1_false {O : Prog} (hO : ¬ (Formula.plays O (StatedBot0 k) .C).interp) :
    proofSearch k ((Formula.impl (.plays .self .opp .D) (.plays .opp .self .C)).subst
      (StatedBot0 k) O) = false := by
  cases h : proofSearch k ((Formula.impl (.plays .self .opp .D) (.plays .opp .self .C)).subst
      (StatedBot0 k) O) with
  | false => rfl
  | true =>
    exfalso
    have hD : play (0 + 3) (StatedBot0 k) O = some .D := E_D1 rfl h
    have hs : (Formula.plays (StatedBot0 k) O .D).interp →
        (Formula.plays O (StatedBot0 k) .C).interp := proofSearch_sound _ _ h
    exact hO (hs ⟨_, hD⟩)

theorem s0_g2_false {O : Prog}
    (h1 : proofSearch k ((Formula.impl (.plays .self .opp .D) (.plays .opp .self .C)).subst
      (StatedBot0 k) O) = false)
    (hO : ¬ (Formula.plays O (StatedBot0 k) .C).interp) :
    proofSearch k ((Formula.impl (.plays .self .opp .C) (.plays .opp .self .C)).subst
      (StatedBot0 k) O) = false := by
  cases h : proofSearch k ((Formula.impl (.plays .self .opp .C) (.plays .opp .self .C)).subst
      (StatedBot0 k) O) with
  | false => rfl
  | true =>
    exfalso
    have hC : play (0 + 3) (StatedBot0 k) O = some .C := E_C rfl h1 h
    have hs : (Formula.plays (StatedBot0 k) O .C).interp →
        (Formula.plays O (StatedBot0 k) .C).interp := proofSearch_sound _ _ h
    exact hO (hs ⟨_, hC⟩)

theorem s0_D_of {n : Nat} {O : Prog} (hO : ¬ (Formula.plays O (StatedBot0 k) .C).interp) :
    play (n + 3) (StatedBot0 k) O = some .D :=
  E_D2 rfl (s0_g1_false hO) (s0_g2_false (s0_g1_false hO) hO)

/-! ### Probe plays: each stated bot against the frozen probes `.bot CB/DB/Mirror` -/

theorem s0_botCB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot0 k) (.bot CooperateBot) = some .D := by
  refine E_D1 rfl ((proofSearch_spec _ _).2 ?_)
  show Pf k (.impl (.plays (StatedBot0 k) (.bot CooperateBot) .D)
                   (.plays (.bot CooperateBot) (StatedBot0 k) .C))
  refine Pf.weakenImpl _ _ 2 (Pf.atom ⟨PlaysProof.bot PlaysProof.const, by simp [c_leaf, c_node]⟩) ?_
  simp only [numCost, Formula.size, Prog.size, StatedBot0, CooperateBot]
  omega

theorem s0_botDB (n : Nat) : play (n + 3) (StatedBot0 k) (.bot DefectBot) = some .D :=
  s0_D_of (interp_bot_DefectBot_plays_C_false _)

theorem s0_g1_false_M :
    proofSearch k ((Formula.impl (.plays .self .opp .D) (.plays .opp .self .C)).subst
      (StatedBot0 k) (.bot MirrorBot)) = false := by
  cases h : proofSearch k ((Formula.impl (.plays .self .opp .D) (.plays .opp .self .C)).subst
      (StatedBot0 k) (.bot MirrorBot)) with
  | false => rfl
  | true =>
    exfalso
    have hD : play (0 + 3) (StatedBot0 k) (.bot MirrorBot) = some .D := E_D1 rfl h
    have hM := botM_play hD
    have hs : (Formula.plays (StatedBot0 k) (.bot MirrorBot) .D).interp →
        (Formula.plays (.bot MirrorBot) (StatedBot0 k) .C).interp := proofSearch_sound _ _ h
    exact not_plays_of hM (by decide) (hs ⟨_, hD⟩)

theorem s0_botM (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot0 k) (.bot MirrorBot) = some .C := by
  refine E_C rfl s0_g1_false_M ((proofSearch_spec _ _).2 ?_)
  show Pf k (.impl (.plays (StatedBot0 k) (.bot MirrorBot) .C)
                   (.plays (.bot MirrorBot) (StatedBot0 k) .C))
  refine Pf.botSimStep (.bot MirrorBot) .opp .self (StatedBot0 k) .C rfl ?_
  simp only [Prog.subst, numCost, Formula.size, Prog.size, StatedBot0, MirrorBot]
  omega

theorem s2_botCB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot2 k) (.bot CooperateBot) = some .C := by
  refine E_C rfl (ps_false_of_not ?_) ((proofSearch_spec _ _).2 ?_)
  · show ¬ (Formula.eq (.bot CooperateBot) (.const .C)).interp
    simp [Formula.interp]
  · show Pf k (.plays (.bot CooperateBot) (StatedBot2 k) .C)
    exact Pf.atom ⟨PlaysProof.bot PlaysProof.const, by simp [c_leaf, c_node]; omega⟩

theorem s2_botDB (n : Nat) : play (n + 3) (StatedBot2 k) (.bot DefectBot) = some .D := by
  refine E_D2 rfl (ps_false_of_not ?_) (ps_false_of_not ?_)
  · show ¬ (Formula.eq (.bot DefectBot) (.const .C)).interp
    simp [Formula.interp]
  · exact interp_bot_DefectBot_plays_C_false _

theorem s3_botCB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot3 k) (.bot CooperateBot) = some .C := by
  refine T_C rfl ((proofSearch_spec _ _).2 ?_) (ps_false_of_not ?_)
  · show Pf k (.plays (.bot CooperateBot) (StatedBot3 k) .C)
    exact Pf.atom ⟨PlaysProof.bot PlaysProof.const, by simp [c_leaf, c_node]; omega⟩
  · show ¬ (Formula.eq (.bot CooperateBot) (.const .C)).interp
    simp [Formula.interp]

theorem s3_botDB (n : Nat) : play (n + 3) (StatedBot3 k) (.bot DefectBot) = some .D :=
  T_D1 rfl (ps_false_of_not (interp_bot_DefectBot_plays_C_false _))

theorem s4_botCB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot4 k) (.bot CooperateBot) = some .D := by
  refine E_D1 rfl ((proofSearch_spec _ _).2 ?_)
  show Pf k (.plays (.bot CooperateBot) (.bot (.const .D)) .C)
  exact Pf.atom ⟨PlaysProof.bot PlaysProof.const, by simp [c_leaf, c_node]; omega⟩

theorem s4_botDB (n : Nat) : play (n + 3) (StatedBot4 k) (.bot DefectBot) = some .D :=
  E_D2 rfl (ps_false_of_not (interp_bot_DefectBot_plays_C_false _))
    (ps_false_of_not (interp_bot_DefectBot_plays_C_false _))

/-! ### Probe floors: no stated bot's play against `.bot DefectBot` is certifiable ≤ k -/

theorem s0_probeDB : ∀ a n, PlaysProof (StatedBot0 k) (.bot DefectBot) (StatedBot0 k) a n → k ≤ n :=
  fun _ _ h => search_probe (body := StatedBot0 k) rfl h
    (not_pf_of_ps_false (s0_g1_false (interp_bot_DefectBot_plays_C_false _)))
theorem s2_probeDB : ∀ a n, PlaysProof (StatedBot2 k) (.bot DefectBot) (StatedBot2 k) a n → k ≤ n :=
  fun _ _ h => search_probe (body := StatedBot2 k) rfl h
    (not_pf_of_ps_false (ps_false_of_not (by
      show ¬ (Formula.eq (.bot DefectBot) (.const .C)).interp
      simp [Formula.interp])))
theorem s3_probeDB : ∀ a n, PlaysProof (StatedBot3 k) (.bot DefectBot) (StatedBot3 k) a n → k ≤ n :=
  fun _ _ h => search_probe (body := StatedBot3 k) rfl h
    (not_pf_of_ps_false (ps_false_of_not (interp_bot_DefectBot_plays_C_false _)))
theorem s4_probeDB : ∀ a n, PlaysProof (StatedBot4 k) (.bot DefectBot) (StatedBot4 k) a n → k ≤ n :=
  fun _ _ h => search_probe (body := StatedBot4 k) rfl h
    (not_pf_of_ps_false (ps_false_of_not (interp_bot_DefectBot_plays_C_false _)))

theorem constD_shape : ∀ k' ψ c0 c1, (Prog.const .D) ≠ .search k' ψ (.const c0) (.const c1) := by
  intros; simp
theorem constD_pthen : ∀ (L : List CtxLayer), (Prog.const .D) ≠ ctxPlug L (.const .C) :=
  fun L => const_ne_ctxPlug (by decide) L

/-- EBot's else-branch, spelled out (for the probe floor's `q`). -/
abbrev EBotElse : Prog :=
  .ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
    (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))

end Facts

/-! ## The zoo's play against each stated bot -/

section Zoo
variable {k : Nat}

theorem eq_false_of {me Y : Prog} (h : Y ≠ .const .C) :
    proofSearch k ((Formula.eq .opp (.const .C)).subst me Y) = false :=
  ps_false_of_not (by show ¬ (Formula.eq Y (.const .C)).interp; exact h)

-- DupocBot defects against every stated bot but S1: their C is floor-priced (new census).
theorem dupoc_vs_s0 (n : Nat) : play (n + 2) (DupocBot k) (StatedBot0 k) = some .D :=
  srch_f (me := DupocBot k) rfl (ps_false_of_floor
    (E_C_floor k (.impl (.plays .self .opp .D) (.plays .opp .self .C))
      (.impl (.plays .self .opp .C) (.plays .opp .self .C)) (DupocBot k)) (by exact rfl))
theorem dupoc_vs_s2 (n : Nat) : play (n + 2) (DupocBot k) (StatedBot2 k) = some .D :=
  srch_f (me := DupocBot k) rfl (ps_false_of_floor
    (E_C_floor k (.eq .opp (.const .C)) (.plays .opp .self .C) (DupocBot k)) (by exact rfl))
theorem dupoc_vs_s3 (n : Nat) : play (n + 2) (DupocBot k) (StatedBot3 k) = some .D :=
  srch_f (me := DupocBot k) rfl (ps_false_of_floor
    (T_C_floor k (.plays .opp .self .C) (.eq .opp (.const .C)) (DupocBot k)) (by exact rfl))
theorem dupoc_vs_s4 (n : Nat) : play (n + 2) (DupocBot k) (StatedBot4 k) = some .D :=
  srch_f (me := DupocBot k) rfl (ps_false_of_floor
    (E_C_floor k (.plays .opp (.bot (.const .D)) .C) (.plays .opp .self .C) (DupocBot k))
    (by exact rfl))

-- CupodTrollBot cooperates: no stated bot is literally CupodBot.
theorem ctroll_vs_s0 (n : Nat) : play (n + 2) (CupodTrollBot k) (StatedBot0 k) = some .C :=
  srch_f (me := CupodTrollBot k) rfl (ps_false_of_not (by
    simp [Formula.subst, Prog.subst, Formula.interp, StatedBot0, CupodBot]))
theorem ctroll_vs_s2 (n : Nat) : play (n + 2) (CupodTrollBot k) (StatedBot2 k) = some .C :=
  srch_f (me := CupodTrollBot k) rfl (ps_false_of_not (by
    simp [Formula.subst, Prog.subst, Formula.interp, StatedBot2, CupodBot]))
theorem ctroll_vs_s3 (n : Nat) : play (n + 2) (CupodTrollBot k) (StatedBot3 k) = some .C :=
  srch_f (me := CupodTrollBot k) rfl (ps_false_of_not (by
    simp [Formula.subst, Prog.subst, Formula.interp, StatedBot3, CupodBot]))
theorem ctroll_vs_s4 (n : Nat) : play (n + 2) (CupodTrollBot k) (StatedBot4 k) = some .C :=
  srch_f (me := CupodTrollBot k) rfl (ps_false_of_not (by
    simp [Formula.subst, Prog.subst, Formula.interp, StatedBot4, CupodBot]))

theorem cupod_botDB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 2) (CupodBot k) (.bot DefectBot) = some .D :=
  srch_t (me := CupodBot k) rfl ((proofSearch_spec _ _).2 (by
    show Pf k (.plays (.bot DefectBot) (CupodBot k) .D)
    exact Pf.atom ⟨PlaysProof.bot PlaysProof.const, by simp [c_leaf, c_node]; omega⟩))

theorem obot_botDB (n : Nat) : play (n + 2 + 3) OBot (.bot DefectBot) = some .D :=
  obot_D_of_CB (play_bot_DefectBot n _)
theorem tft_botDB (n : Nat) : play (n + 2 + 3) TitForTatBot (.bot DefectBot) = some .D :=
  tft_play (play_bot_DefectBot n _)
theorem ebot_botDB (n : Nat) : play (n + 2 + 5) EBot (.bot DefectBot) = some .D :=
  ebot_D_all (play_bot_DefectBot n _) (play_bot_DefectBot n _) (play_bot_DefectBot n _)

end Zoo

/-! ## Each stated bot's play against the zoo (offset 3 throughout) -/

section Stated
variable {k : Nat}

-- S0 ------------------------------------------------------------------------
theorem s0_vs_CB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot0 k) CooperateBot = some .D := by
  refine E_D1 rfl ((proofSearch_spec _ _).2 ?_)
  show Pf k (.impl (.plays (StatedBot0 k) CooperateBot .D) (.plays CooperateBot (StatedBot0 k) .C))
  refine Pf.weakenImpl _ _ 1 (Pf.atom ⟨PlaysProof.const, by simp [c_leaf]⟩) ?_
  simp only [numCost, Formula.size, Prog.size, StatedBot0, CooperateBot]
  omega
theorem s0_vs_DB (n : Nat) : play (n + 3) (StatedBot0 k) DefectBot = some .D :=
  s0_D_of (interp_DefectBot_plays_C_false _)
theorem s0_vs_Dupoc (n : Nat) : play (n + 3) (StatedBot0 k) (DupocBot k) = some .D :=
  s0_D_of (not_plays_of (dupoc_vs_s0 0) (by decide))
theorem s0_vs_OBot (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot0 k) OBot = some .D :=
  s0_D_of (not_plays_of (obot_D_of_CB (s0_botCB hb 0)) (by decide))
theorem s0_vs_TFT (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot0 k) TitForTatBot = some .D :=
  s0_D_of (not_plays_of (tft_play (s0_botCB hb 0)) (by decide))
theorem s0_vs_Cupod (n : Nat) : play (n + 3) (StatedBot0 k) (CupodBot k) = some .D :=
  E_D2 rfl
    (ps_false_of_floor (no_provable_searcherElse_tail k (.plays .opp .self .D) .D .C (by decide)
      (StatedBot0 k)) ((TailTo_impl _ _ _).2 ⟨by exact rfl, by simp [Formula.subst, Prog.subst]⟩))
    (ps_false_of_floor (no_provable_searcherElse_tail k (.plays .opp .self .D) .D .C (by decide)
      (StatedBot0 k)) ((TailTo_impl _ _ _).2 ⟨by exact rfl,
        by simp [Formula.subst, Prog.subst, StatedBot0]⟩))
theorem s0_vs_CTroll (n : Nat) : play (n + 3) (StatedBot0 k) (CupodTrollBot k) = some .D :=
  E_D2 rfl
    (ps_false_of_floor (no_provable_searcherElse_tail k (.eq .opp (CupodBot k)) .D .C (by decide)
      (StatedBot0 k)) ((TailTo_impl _ _ _).2 ⟨by exact rfl, by simp [Formula.subst, Prog.subst]⟩))
    (ps_false_of_floor (no_provable_searcherElse_tail k (.eq .opp (CupodBot k)) .D .C (by decide)
      (StatedBot0 k)) ((TailTo_impl _ _ _).2 ⟨by exact rfl,
        by simp [Formula.subst, Prog.subst, StatedBot0]⟩))
theorem s0_vs_DBot (n : Nat) : play (n + 3) (StatedBot0 k) DBot = some .D :=
  E_D2 rfl
    (ps_false_of_floor (probe_floor k DefectBot (.const .D) (.const .C) (StatedBot0 k) .C .C
      s0_probeDB constD_shape constD_pthen)
      ((TailTo_impl _ _ _).2 ⟨by exact rfl, by simp [Formula.subst, Prog.subst]⟩))
    (ps_false_of_floor (probe_floor k DefectBot (.const .D) (.const .C) (StatedBot0 k) .C .C
      s0_probeDB constD_shape constD_pthen)
      ((TailTo_impl _ _ _).2 ⟨by exact rfl, by simp [Formula.subst, Prog.subst, StatedBot0]⟩))
theorem s0_vs_EBot (n : Nat) : play (n + 3) (StatedBot0 k) EBot = some .D :=
  E_D2 rfl
    (ps_false_of_floor (probe_floor k DefectBot (.const .D) EBotElse (StatedBot0 k) .C .C
      s0_probeDB constD_shape constD_pthen)
      ((TailTo_impl _ _ _).2 ⟨by exact rfl, by simp [Formula.subst, Prog.subst]⟩))
    (ps_false_of_floor (probe_floor k DefectBot (.const .D) EBotElse (StatedBot0 k) .C .C
      s0_probeDB constD_shape constD_pthen)
      ((TailTo_impl _ _ _).2 ⟨by exact rfl, by simp [Formula.subst, Prog.subst, StatedBot0]⟩))

-- S2 ------------------------------------------------------------------------
theorem s2_vs_CB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot2 k) CooperateBot = some .D :=
  E_D1 rfl ((proofSearch_spec _ _).2 (by
    show Pf k (.eq CooperateBot (.const .C))
    exact Pf.eqRefl _ (by simp only [Formula.size, Prog.size, CooperateBot]; omega)))
theorem s2_vs_DB (n : Nat) : play (n + 3) (StatedBot2 k) DefectBot = some .D :=
  E_D2 rfl (eq_false_of (by simp [DefectBot])) (ps_false_of_not (interp_DefectBot_plays_C_false _))
theorem s2_vs_Dupoc (n : Nat) : play (n + 3) (StatedBot2 k) (DupocBot k) = some .D :=
  E_D2 rfl (eq_false_of (by simp [DupocBot]))
    (ps_false_of_not (not_plays_of (dupoc_vs_s2 0) (by decide)))
theorem s2_vs_Cupod (n : Nat) : play (n + 3) (StatedBot2 k) (CupodBot k) = some .D :=
  E_D2 rfl (eq_false_of (by simp [CupodBot]))
    (ps_false_of_floor (no_provable_searcherElse_tail k (.plays .opp .self .D) .D .C (by decide)
      (StatedBot2 k)) (by exact rfl))
theorem s2_vs_CTroll (n : Nat) : play (n + 3) (StatedBot2 k) (CupodTrollBot k) = some .D :=
  E_D2 rfl (eq_false_of (by simp [CupodTrollBot]))
    (ps_false_of_floor (no_provable_searcherElse_tail k (.eq .opp (CupodBot k)) .D .C (by decide)
      (StatedBot2 k)) (by exact rfl))
theorem s2_vs_DBot (n : Nat) : play (n + 3) (StatedBot2 k) DBot = some .D :=
  E_D2 rfl (eq_false_of (by simp [DBot]))
    (ps_false_of_floor (probe_floor k DefectBot (.const .D) (.const .C) (StatedBot2 k) .C .C
      s2_probeDB constD_shape constD_pthen) (by exact rfl))
theorem s2_vs_OBot (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot2 k) OBot = some .D :=
  E_D2 rfl (eq_false_of (by simp [OBot]))
    (ps_false_of_not (not_plays_of (obot_D_of_CB_DB (s2_botCB hb 0) (s2_botDB 0)) (by decide)))
theorem s2_vs_EBot (n : Nat) : play (n + 3) (StatedBot2 k) EBot = some .D :=
  E_D2 rfl (eq_false_of (by simp [EBot]))
    (ps_false_of_floor (probe_floor k DefectBot (.const .D) EBotElse (StatedBot2 k) .C .C
      s2_probeDB constD_shape constD_pthen) (by exact rfl))

-- S3 ------------------------------------------------------------------------
theorem s3_vs_CB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot3 k) CooperateBot = some .D := by
  refine T_D2 rfl ((proofSearch_spec _ _).2 ?_) ((proofSearch_spec _ _).2 ?_)
  · show Pf k (.plays CooperateBot (StatedBot3 k) .C)
    exact Pf.atom ⟨PlaysProof.const, by simp [c_leaf]; omega⟩
  · show Pf k (.eq CooperateBot (.const .C))
    exact Pf.eqRefl _ (by simp only [Formula.size, Prog.size, CooperateBot]; omega)
theorem s3_vs_DB (n : Nat) : play (n + 3) (StatedBot3 k) DefectBot = some .D :=
  T_D1 rfl (ps_false_of_not (interp_DefectBot_plays_C_false _))
theorem s3_vs_Dupoc (n : Nat) : play (n + 3) (StatedBot3 k) (DupocBot k) = some .D :=
  T_D1 rfl (ps_false_of_not (not_plays_of (dupoc_vs_s3 0) (by decide)))
theorem s3_vs_Cupod (n : Nat) : play (n + 3) (StatedBot3 k) (CupodBot k) = some .D :=
  T_D1 rfl (ps_false_of_floor (no_provable_searcherElse_tail k (.plays .opp .self .D) .D .C
    (by decide) (StatedBot3 k)) (by exact rfl))
theorem s3_vs_CTroll (n : Nat) : play (n + 3) (StatedBot3 k) (CupodTrollBot k) = some .D :=
  T_D1 rfl (ps_false_of_floor (no_provable_searcherElse_tail k (.eq .opp (CupodBot k)) .D .C
    (by decide) (StatedBot3 k)) (by exact rfl))
theorem s3_vs_DBot (n : Nat) : play (n + 3) (StatedBot3 k) DBot = some .D :=
  T_D1 rfl (ps_false_of_floor (probe_floor k DefectBot (.const .D) (.const .C) (StatedBot3 k)
    .C .C s3_probeDB constD_shape constD_pthen) (by exact rfl))
theorem s3_vs_OBot (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot3 k) OBot = some .D :=
  T_D1 rfl (ps_false_of_not (not_plays_of (obot_D_of_CB_DB (s3_botCB hb 0) (s3_botDB 0))
    (by decide)))
theorem s3_vs_EBot (n : Nat) : play (n + 3) (StatedBot3 k) EBot = some .D :=
  T_D1 rfl (ps_false_of_floor (probe_floor k DefectBot (.const .D) EBotElse (StatedBot3 k)
    .C .C s3_probeDB constD_shape constD_pthen) (by exact rfl))

-- S4 ------------------------------------------------------------------------
theorem s4_vs_CB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot4 k) CooperateBot = some .D :=
  E_D1 rfl ((proofSearch_spec _ _).2 (by
    show Pf k (.plays CooperateBot (.bot (.const .D)) .C)
    exact Pf.atom ⟨PlaysProof.const, by simp [c_leaf]; omega⟩))
theorem s4_vs_DB (n : Nat) : play (n + 3) (StatedBot4 k) DefectBot = some .D :=
  E_D2 rfl (ps_false_of_not (interp_DefectBot_plays_C_false _))
    (ps_false_of_not (interp_DefectBot_plays_C_false _))
theorem s4_vs_Dupoc (n : Nat) : play (n + 3) (StatedBot4 k) (DupocBot k) = some .D :=
  E_D2 rfl (ps_false_of_not (not_plays_of (DupocBot_plays_D_against_bot_DefectBot k 0) (by decide)))
    (ps_false_of_not (not_plays_of (dupoc_vs_s4 0) (by decide)))
theorem s4_vs_Cupod (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot4 k) (CupodBot k) = some .D :=
  E_D2 rfl (ps_false_of_not (not_plays_of (cupod_botDB hb 0) (by decide)))
    (ps_false_of_floor (no_provable_searcherElse_tail k (.plays .opp .self .D) .D .C (by decide)
      (StatedBot4 k)) (by exact rfl))
theorem s4_vs_CTroll (n : Nat) : play (n + 3) (StatedBot4 k) (CupodTrollBot k) = some .D :=
  E_D2 rfl
    (ps_false_of_floor (no_provable_searcherElse_tail k (.eq .opp (CupodBot k)) .D .C (by decide)
      (.bot (.const .D))) (by exact rfl))
    (ps_false_of_floor (no_provable_searcherElse_tail k (.eq .opp (CupodBot k)) .D .C (by decide)
      (StatedBot4 k)) (by exact rfl))
theorem s4_vs_DBot (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot4 k) DBot = some .D :=
  E_D1 rfl ((proofSearch_spec _ _).2 (by
    show Pf k (.plays DBot (.bot (.const .D)) .C)
    exact Pf.atom ⟨PlaysProof.ite_f (PlaysProof.sim (PlaysProof.bot PlaysProof.const)) (by decide)
      PlaysProof.const, by simp [c_leaf, c_node]; omega⟩))
theorem s4_vs_OBot (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot4 k) OBot = some .D :=
  E_D2 rfl (ps_false_of_not (not_plays_of (obot_botDB 0) (by decide)))
    (ps_false_of_not (not_plays_of (obot_D_of_CB (s4_botCB hb 0)) (by decide)))
theorem s4_vs_TFT (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot4 k) TitForTatBot = some .D :=
  E_D2 rfl (ps_false_of_not (not_plays_of (tft_botDB 0) (by decide)))
    (ps_false_of_not (not_plays_of (tft_play (s4_botCB hb 0)) (by decide)))
theorem s4_vs_EBot (n : Nat) : play (n + 3) (StatedBot4 k) EBot = some .D :=
  E_D2 rfl (ps_false_of_not (not_plays_of (ebot_botDB 0) (by decide)))
    (ps_false_of_floor (probe_floor k DefectBot (.const .D) EBotElse (StatedBot4 k) .C .C
      s4_probeDB constD_shape constD_pthen) (by exact rfl))

end Stated

/-! ## 2a — stated vs stated -/

section Stated2a
variable {k : Nat}

theorem s0_Cfloor (O : Prog) : ∀ K φ, Pf K φ → K ≤ k →
    TailTo (.plays (StatedBot0 k) O .C) φ → False :=
  E_C_floor k (.impl (.plays .self .opp .D) (.plays .opp .self .C))
    (.impl (.plays .self .opp .C) (.plays .opp .self .C)) O
theorem s2_Cfloor (O : Prog) : ∀ K φ, Pf K φ → K ≤ k →
    TailTo (.plays (StatedBot2 k) O .C) φ → False :=
  E_C_floor k (.eq .opp (.const .C)) (.plays .opp .self .C) O
theorem s3_Cfloor (O : Prog) : ∀ K φ, Pf K φ → K ≤ k →
    TailTo (.plays (StatedBot3 k) O .C) φ → False :=
  T_C_floor k (.plays .opp .self .C) (.eq .opp (.const .C)) O
theorem s4_Cfloor (O : Prog) : ∀ K φ, Pf K φ → K ≤ k →
    TailTo (.plays (StatedBot4 k) O .C) φ → False :=
  E_C_floor k (.plays .opp (.bot (.const .D)) .C) (.plays .opp .self .C) O

-- S2 against S0/S2/S3/S4: "is it CooperateBot?" fails, "does it provably cooperate?" floors.
theorem s2_vs_s0 (n : Nat) : play (n + 3) (StatedBot2 k) (StatedBot0 k) = some .D :=
  E_D2 rfl (eq_false_of (by simp [StatedBot0])) (ps_false_of_floor (s0_Cfloor _) (by exact rfl))
theorem s2_vs_s2 (n : Nat) : play (n + 3) (StatedBot2 k) (StatedBot2 k) = some .D :=
  E_D2 rfl (eq_false_of (by simp [StatedBot2])) (ps_false_of_floor (s2_Cfloor _) (by exact rfl))
theorem s2_vs_s3 (n : Nat) : play (n + 3) (StatedBot2 k) (StatedBot3 k) = some .D :=
  E_D2 rfl (eq_false_of (by simp [StatedBot3])) (ps_false_of_floor (s3_Cfloor _) (by exact rfl))
theorem s2_vs_s4 (n : Nat) : play (n + 3) (StatedBot2 k) (StatedBot4 k) = some .D :=
  E_D2 rfl (eq_false_of (by simp [StatedBot4])) (ps_false_of_floor (s4_Cfloor _) (by exact rfl))

theorem s3_vs_s0 (n : Nat) : play (n + 3) (StatedBot3 k) (StatedBot0 k) = some .D :=
  T_D1 rfl (ps_false_of_floor (s0_Cfloor _) (by exact rfl))
theorem s3_vs_s2 (n : Nat) : play (n + 3) (StatedBot3 k) (StatedBot2 k) = some .D :=
  T_D1 rfl (ps_false_of_floor (s2_Cfloor _) (by exact rfl))
theorem s3_vs_s3 (n : Nat) : play (n + 3) (StatedBot3 k) (StatedBot3 k) = some .D :=
  T_D1 rfl (ps_false_of_floor (s3_Cfloor _) (by exact rfl))
theorem s3_vs_s4 (n : Nat) : play (n + 3) (StatedBot3 k) (StatedBot4 k) = some .D :=
  T_D1 rfl (ps_false_of_floor (s4_Cfloor _) (by exact rfl))

theorem s4_vs_s0 (n : Nat) : play (n + 3) (StatedBot4 k) (StatedBot0 k) = some .D :=
  E_D2 rfl (ps_false_of_floor (s0_Cfloor _) (by exact rfl))
    (ps_false_of_floor (s0_Cfloor _) (by exact rfl))
theorem s4_vs_s2 (n : Nat) : play (n + 3) (StatedBot4 k) (StatedBot2 k) = some .D :=
  E_D2 rfl (ps_false_of_floor (s2_Cfloor _) (by exact rfl))
    (ps_false_of_floor (s2_Cfloor _) (by exact rfl))
theorem s4_vs_s3 (n : Nat) : play (n + 3) (StatedBot4 k) (StatedBot3 k) = some .D :=
  E_D2 rfl (ps_false_of_floor (s3_Cfloor _) (by exact rfl))
    (ps_false_of_floor (s3_Cfloor _) (by exact rfl))
theorem s4_vs_s4 (n : Nat) : play (n + 3) (StatedBot4 k) (StatedBot4 k) = some .D :=
  E_D2 rfl (ps_false_of_floor (s4_Cfloor _) (by exact rfl))
    (ps_false_of_floor (s4_Cfloor _) (by exact rfl))

theorem s0_vs_s2 (n : Nat) : play (n + 3) (StatedBot0 k) (StatedBot2 k) = some .D :=
  E_D2 rfl
    (ps_false_of_floor (s2_Cfloor _) ((TailTo_impl _ _ _).2 ⟨by exact rfl, by simp [Formula.subst, Prog.subst]⟩))
    (ps_false_of_floor (s2_Cfloor _) ((TailTo_impl _ _ _).2 ⟨by exact rfl,
      by simp [Formula.subst, Prog.subst, StatedBot0, StatedBot2]⟩))
theorem s0_vs_s3 (n : Nat) : play (n + 3) (StatedBot0 k) (StatedBot3 k) = some .D :=
  E_D2 rfl
    (ps_false_of_floor (s3_Cfloor _) ((TailTo_impl _ _ _).2 ⟨by exact rfl, by simp [Formula.subst, Prog.subst]⟩))
    (ps_false_of_floor (s3_Cfloor _) ((TailTo_impl _ _ _).2 ⟨by exact rfl,
      by simp [Formula.subst, Prog.subst, StatedBot0, StatedBot3]⟩))
theorem s0_vs_s4 (n : Nat) : play (n + 3) (StatedBot0 k) (StatedBot4 k) = some .D :=
  E_D2 rfl
    (ps_false_of_floor (s4_Cfloor _) ((TailTo_impl _ _ _).2 ⟨by exact rfl, by simp [Formula.subst, Prog.subst]⟩))
    (ps_false_of_floor (s4_Cfloor _) ((TailTo_impl _ _ _).2 ⟨by exact rfl,
      by simp [Formula.subst, Prog.subst, StatedBot0, StatedBot4]⟩))

/-- S0 against itself: the exploit guard self-refutes (soundness); the cooperation
    guard is `A → A` (`Pf.implRefl`). -/
theorem s0_self_g1_false :
    proofSearch k ((Formula.impl (.plays .self .opp .D) (.plays .opp .self .C)).subst
      (StatedBot0 k) (StatedBot0 k)) = false := by
  cases h : proofSearch k ((Formula.impl (.plays .self .opp .D) (.plays .opp .self .C)).subst
      (StatedBot0 k) (StatedBot0 k)) with
  | false => rfl
  | true =>
    exfalso
    have hD : play (0 + 3) (StatedBot0 k) (StatedBot0 k) = some .D := E_D1 rfl h
    have hs : (Formula.plays (StatedBot0 k) (StatedBot0 k) .D).interp →
        (Formula.plays (StatedBot0 k) (StatedBot0 k) .C).interp := proofSearch_sound _ _ h
    exact not_plays_of hD (by decide) (hs ⟨_, hD⟩)

theorem s0_vs_s0 (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot0 k) (StatedBot0 k) = some .C := by
  refine E_C rfl s0_self_g1_false ((proofSearch_spec _ _).2 ?_)
  show Pf k (.impl (.plays (StatedBot0 k) (StatedBot0 k) .C) (.plays (StatedBot0 k) (StatedBot0 k) .C))
  refine Pf.implRefl _ ?_
  simp only [numCost, Formula.size, Prog.size, StatedBot0]
  omega

end Stated2a

/-! ## Packaging into the library's strict template -/

theorem eventual_of {P : Nat} {L R : Nat → Prog} {r : Option Outcome}
    (f : ∀ k, 40 * Nat.log2 k + 400 ≤ k → ∀ fuel, outcome (fuel + P) (L k) (R k) = r) :
    OutcomeSpec .eventual P L R r := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 40 400
  exact ⟨K, fun k hk => f k (hK k (Nat.le_of_lt hk))⟩

/-- Statements about ONE side of a match (the other side is open). -/
abbrev PlaysEventually (P : Nat) (L R : Nat → Prog) (a : Action) : Prop :=
  ∃ K, ∀ k, K < k → ∀ n, play (n + P) (L k) (R k) = some a

theorem plays_eventually {P : Nat} {L R : Nat → Prog} {a : Action}
    (f : ∀ k, 40 * Nat.log2 k + 400 ≤ k → ∀ n, play (n + P) (L k) (R k) = some a) :
    PlaysEventually P L R a := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 40 400
  exact ⟨K, fun k hk => f k (hK k (Nat.le_of_lt hk))⟩

-- 2b, S0 row -----------------------------------------------------------------
theorem outcome_StatedBot0_vs_CooperateBot :
    OutcomeSpec .eventual 10 StatedBot0 (fun _ => CooperateBot) (some (.D, .C)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 1) (s0_vs_CB hb) (fun n => cb_play n _) (by omega) (by omega)
theorem outcome_StatedBot0_vs_DefectBot :
    OutcomeSpec .eventual 10 StatedBot0 (fun _ => DefectBot) (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 1) s0_vs_DB (fun n => db_play n _) (by omega) (by omega)
theorem outcome_StatedBot0_vs_DupocBot :
    OutcomeSpec .eventual 10 StatedBot0 DupocBot (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 2) s0_vs_Dupoc dupoc_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot0_vs_CupodTrollBot :
    OutcomeSpec .eventual 10 StatedBot0 CupodTrollBot (some (.D, .C)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 2) s0_vs_CTroll ctroll_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot0_vs_DBot :
    OutcomeSpec .eventual 10 StatedBot0 (fun _ => DBot) (some (.D, .C)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 6) s0_vs_DBot
    (fun n => (dbot_play_C (s0_botDB n) : play (n + 6) DBot (StatedBot0 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot0_vs_TitForTatBot :
    OutcomeSpec .eventual 10 StatedBot0 (fun _ => TitForTatBot) (some (.D, .D)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 6) (s0_vs_TFT hb)
    (fun n => (tft_play (s0_botCB hb n) : play (n + 6) TitForTatBot (StatedBot0 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot0_vs_OBot :
    OutcomeSpec .eventual 10 StatedBot0 (fun _ => OBot) (some (.D, .D)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 6) (s0_vs_OBot hb)
    (fun n => (obot_D_of_CB (s0_botCB hb n) : play (n + 6) OBot (StatedBot0 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot0_vs_EBot :
    OutcomeSpec .eventual 10 StatedBot0 (fun _ => EBot) (some (.D, .C)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 8) s0_vs_EBot
    (fun n => (ebot_C_of_M (s0_botDB n) (s0_botCB hb n) (s0_botM hb n) :
      play (n + 8) EBot (StatedBot0 k) = _)) (by omega) (by omega)
theorem StatedBot0_plays_D_vs_CupodBot : PlaysEventually 3 StatedBot0 CupodBot .D :=
  plays_eventually fun _ _ => s0_vs_Cupod

-- 2b, S2 row -----------------------------------------------------------------
theorem outcome_StatedBot2_vs_CooperateBot :
    OutcomeSpec .eventual 10 StatedBot2 (fun _ => CooperateBot) (some (.D, .C)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 1) (s2_vs_CB hb) (fun n => cb_play n _) (by omega) (by omega)
theorem outcome_StatedBot2_vs_DefectBot :
    OutcomeSpec .eventual 10 StatedBot2 (fun _ => DefectBot) (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 1) s2_vs_DB (fun n => db_play n _) (by omega) (by omega)
theorem outcome_StatedBot2_vs_DupocBot :
    OutcomeSpec .eventual 10 StatedBot2 DupocBot (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 2) s2_vs_Dupoc dupoc_vs_s2 (by omega) (by omega)
theorem outcome_StatedBot2_vs_CupodTrollBot :
    OutcomeSpec .eventual 10 StatedBot2 CupodTrollBot (some (.D, .C)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 2) s2_vs_CTroll ctroll_vs_s2 (by omega) (by omega)
theorem outcome_StatedBot2_vs_DBot :
    OutcomeSpec .eventual 10 StatedBot2 (fun _ => DBot) (some (.D, .C)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 6) s2_vs_DBot
    (fun n => (dbot_play_C (s2_botDB n) : play (n + 6) DBot (StatedBot2 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot2_vs_OBot :
    OutcomeSpec .eventual 10 StatedBot2 (fun _ => OBot) (some (.D, .D)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 7) (s2_vs_OBot hb)
    (fun n => (obot_D_of_CB_DB (s2_botCB hb n) (s2_botDB n) : play (n + 7) OBot (StatedBot2 k) = _))
    (by omega) (by omega)
theorem outcome_StatedBot2_vs_EBot :
    OutcomeSpec .eventual 10 StatedBot2 (fun _ => EBot) (some (.D, .C)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 7) s2_vs_EBot
    (fun n => (ebot_C_of_CB (s2_botDB n) (s2_botCB hb n) : play (n + 7) EBot (StatedBot2 k) = _))
    (by omega) (by omega)
theorem StatedBot2_plays_D_vs_CupodBot : PlaysEventually 3 StatedBot2 CupodBot .D :=
  plays_eventually fun _ _ => s2_vs_Cupod
theorem TitForTatBot_plays_C_vs_StatedBot2 :
    PlaysEventually 6 (fun _ => TitForTatBot) StatedBot2 .C :=
  plays_eventually fun k hb n => (tft_play (s2_botCB hb n) : play (n + 6) TitForTatBot (StatedBot2 k) = _)

-- 2b, S3 row -----------------------------------------------------------------
theorem outcome_StatedBot3_vs_CooperateBot :
    OutcomeSpec .eventual 10 StatedBot3 (fun _ => CooperateBot) (some (.D, .C)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 1) (s3_vs_CB hb) (fun n => cb_play n _) (by omega) (by omega)
theorem outcome_StatedBot3_vs_DefectBot :
    OutcomeSpec .eventual 10 StatedBot3 (fun _ => DefectBot) (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 1) s3_vs_DB (fun n => db_play n _) (by omega) (by omega)
theorem outcome_StatedBot3_vs_DupocBot :
    OutcomeSpec .eventual 10 StatedBot3 DupocBot (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 2) s3_vs_Dupoc dupoc_vs_s3 (by omega) (by omega)
theorem outcome_StatedBot3_vs_CupodTrollBot :
    OutcomeSpec .eventual 10 StatedBot3 CupodTrollBot (some (.D, .C)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 2) s3_vs_CTroll ctroll_vs_s3 (by omega) (by omega)
theorem outcome_StatedBot3_vs_DBot :
    OutcomeSpec .eventual 10 StatedBot3 (fun _ => DBot) (some (.D, .C)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 6) s3_vs_DBot
    (fun n => (dbot_play_C (s3_botDB n) : play (n + 6) DBot (StatedBot3 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot3_vs_OBot :
    OutcomeSpec .eventual 10 StatedBot3 (fun _ => OBot) (some (.D, .D)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 7) (s3_vs_OBot hb)
    (fun n => (obot_D_of_CB_DB (s3_botCB hb n) (s3_botDB n) : play (n + 7) OBot (StatedBot3 k) = _))
    (by omega) (by omega)
theorem outcome_StatedBot3_vs_EBot :
    OutcomeSpec .eventual 10 StatedBot3 (fun _ => EBot) (some (.D, .C)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 7) s3_vs_EBot
    (fun n => (ebot_C_of_CB (s3_botDB n) (s3_botCB hb n) : play (n + 7) EBot (StatedBot3 k) = _))
    (by omega) (by omega)
theorem StatedBot3_plays_D_vs_CupodBot : PlaysEventually 3 StatedBot3 CupodBot .D :=
  plays_eventually fun _ _ => s3_vs_Cupod
theorem TitForTatBot_plays_C_vs_StatedBot3 :
    PlaysEventually 6 (fun _ => TitForTatBot) StatedBot3 .C :=
  plays_eventually fun k hb n => (tft_play (s3_botCB hb n) : play (n + 6) TitForTatBot (StatedBot3 k) = _)

-- 2b, S4 row -----------------------------------------------------------------
theorem outcome_StatedBot4_vs_CooperateBot :
    OutcomeSpec .eventual 10 StatedBot4 (fun _ => CooperateBot) (some (.D, .C)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 1) (s4_vs_CB hb) (fun n => cb_play n _) (by omega) (by omega)
theorem outcome_StatedBot4_vs_DefectBot :
    OutcomeSpec .eventual 10 StatedBot4 (fun _ => DefectBot) (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 1) s4_vs_DB (fun n => db_play n _) (by omega) (by omega)
theorem outcome_StatedBot4_vs_DupocBot :
    OutcomeSpec .eventual 10 StatedBot4 DupocBot (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 2) s4_vs_Dupoc dupoc_vs_s4 (by omega) (by omega)
theorem outcome_StatedBot4_vs_CupodTrollBot :
    OutcomeSpec .eventual 10 StatedBot4 CupodTrollBot (some (.D, .C)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 2) s4_vs_CTroll ctroll_vs_s4 (by omega) (by omega)
theorem outcome_StatedBot4_vs_DBot :
    OutcomeSpec .eventual 10 StatedBot4 (fun _ => DBot) (some (.D, .C)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 6) (s4_vs_DBot hb)
    (fun n => (dbot_play_C (s4_botDB n) : play (n + 6) DBot (StatedBot4 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot4_vs_TitForTatBot :
    OutcomeSpec .eventual 10 StatedBot4 (fun _ => TitForTatBot) (some (.D, .D)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 6) (s4_vs_TFT hb)
    (fun n => (tft_play (s4_botCB hb n) : play (n + 6) TitForTatBot (StatedBot4 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot4_vs_OBot :
    OutcomeSpec .eventual 10 StatedBot4 (fun _ => OBot) (some (.D, .D)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 6) (s4_vs_OBot hb)
    (fun n => (obot_D_of_CB (s4_botCB hb n) : play (n + 6) OBot (StatedBot4 k) = _)) (by omega) (by omega)
theorem StatedBot4_plays_D_vs_CupodBot : PlaysEventually 3 StatedBot4 CupodBot .D :=
  plays_eventually fun _ hb => s4_vs_Cupod hb
theorem StatedBot4_plays_D_vs_EBot : PlaysEventually 3 StatedBot4 (fun _ => EBot) .D :=
  plays_eventually fun _ _ => s4_vs_EBot

-- 2b, S1 row: StatedBot1 IS DupocBot, so its row is the library's ---------------
/-- S1's zoo row and S1 vs S1 are the library's `outcome_DupocBot_vs_*` theorems verbatim. -/
theorem statedBot1_is_DupocBot : StatedBot1 = DupocBot := rfl

-- 2a -------------------------------------------------------------------------
theorem outcome_StatedBot0_vs_StatedBot0 :
    OutcomeSpec .eventual 10 StatedBot0 StatedBot0 (some (.C, .C)) :=
  eventual_of fun k hb => cell (c₁ := 3) (c₂ := 3) (s0_vs_s0 hb) (s0_vs_s0 hb) (by omega) (by omega)
theorem outcome_StatedBot0_vs_StatedBot1 :
    OutcomeSpec .eventual 10 StatedBot0 StatedBot1 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 2) s0_vs_Dupoc dupoc_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot0_vs_StatedBot2 :
    OutcomeSpec .eventual 10 StatedBot0 StatedBot2 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 3) s0_vs_s2 s2_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot0_vs_StatedBot3 :
    OutcomeSpec .eventual 10 StatedBot0 StatedBot3 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 3) s0_vs_s3 s3_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot0_vs_StatedBot4 :
    OutcomeSpec .eventual 10 StatedBot0 StatedBot4 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 3) s0_vs_s4 s4_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot1_vs_StatedBot2 :
    OutcomeSpec .eventual 10 StatedBot1 StatedBot2 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 2) (c₂ := 3) dupoc_vs_s2 s2_vs_Dupoc (by omega) (by omega)
theorem outcome_StatedBot1_vs_StatedBot3 :
    OutcomeSpec .eventual 10 StatedBot1 StatedBot3 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 2) (c₂ := 3) dupoc_vs_s3 s3_vs_Dupoc (by omega) (by omega)
theorem outcome_StatedBot1_vs_StatedBot4 :
    OutcomeSpec .eventual 10 StatedBot1 StatedBot4 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 2) (c₂ := 3) dupoc_vs_s4 s4_vs_Dupoc (by omega) (by omega)
theorem outcome_StatedBot2_vs_StatedBot2 :
    OutcomeSpec .eventual 10 StatedBot2 StatedBot2 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 3) s2_vs_s2 s2_vs_s2 (by omega) (by omega)
theorem outcome_StatedBot2_vs_StatedBot3 :
    OutcomeSpec .eventual 10 StatedBot2 StatedBot3 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 3) s2_vs_s3 s3_vs_s2 (by omega) (by omega)
theorem outcome_StatedBot2_vs_StatedBot4 :
    OutcomeSpec .eventual 10 StatedBot2 StatedBot4 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 3) s2_vs_s4 s4_vs_s2 (by omega) (by omega)
theorem outcome_StatedBot3_vs_StatedBot3 :
    OutcomeSpec .eventual 10 StatedBot3 StatedBot3 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 3) s3_vs_s3 s3_vs_s3 (by omega) (by omega)
theorem outcome_StatedBot3_vs_StatedBot4 :
    OutcomeSpec .eventual 10 StatedBot3 StatedBot4 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 3) s3_vs_s4 s4_vs_s3 (by omega) (by omega)
theorem outcome_StatedBot4_vs_StatedBot4 :
    OutcomeSpec .eventual 10 StatedBot4 StatedBot4 (some (.D, .D)) :=
  eventual_of fun k _ => cell (c₁ := 3) (c₂ := 3) s4_vs_s4 s4_vs_s4 (by omega) (by omega)
end PD.Stated
