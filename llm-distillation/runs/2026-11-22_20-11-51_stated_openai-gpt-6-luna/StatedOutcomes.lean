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
import PrisonersDilemma.Theorems.CooperateBot.Helpers

open PD PD.BaseTheorems PD.Bots PD.Theorems
namespace PD.StatedLuna


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


/-! ## The luna bots, verbatim from `classes.json` -/

def StatedBot0 (k : Nat) : Prog := .search k (.plays .opp .self Action.C) (.search k (.plays .opp (.const Action.D) Action.D) (.const Action.C) (.const Action.D)) (.const Action.D)
def StatedBot1 : Prog := .const Action.D
def StatedBot2 : Prog := .ite (.sim .opp .self) Action.C (.const Action.C) (.const Action.D)
def StatedBot3 (k : Nat) : Prog := .search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)

theorem statedBot1_is_DefectBot : StatedBot1 = DefectBot := rfl
theorem statedBot3_is_DupocBot : StatedBot3 = DupocBot := rfl

/-! ## S0: PrudentBot's nested shape, prudence probe `.const D` (unfrozen) -/

section S0
variable {k : Nat}

abbrev gC : Formula := .plays .opp .self .C
abbrev gP : Formula := .plays .opp (.const .D) .D

theorem N_C {n : Nat} {O : Prog}
    (h1 : proofSearch k (gC.subst (StatedBot0 k) O) = true)
    (h2 : proofSearch k (gP.subst (StatedBot0 k) O) = true) :
    play (n + 3) (StatedBot0 k) O = some .C := by
  show eval (n + 3) (StatedBot0 k) O (.search k gC (.search k gP (.const .C) (.const .D)) (.const .D)) = _
  simp [eval, h1, h2]
theorem N_D1 {n : Nat} {O : Prog} (h1 : proofSearch k (gC.subst (StatedBot0 k) O) = false) :
    play (n + 3) (StatedBot0 k) O = some .D := by
  show eval (n + 3) (StatedBot0 k) O (.search k gC (.search k gP (.const .C) (.const .D)) (.const .D)) = _
  simp [eval, h1]
theorem N_D2 {n : Nat} {O : Prog} (h2 : proofSearch k (gP.subst (StatedBot0 k) O) = false) :
    play (n + 3) (StatedBot0 k) O = some .D := by
  cases h1 : proofSearch k (gC.subst (StatedBot0 k) O)
  · exact N_D1 h1
  · show eval (n + 3) (StatedBot0 k) O (.search k gC (.search k gP (.const .C) (.const .D)) (.const .D)) = _
    simp [eval, h1, h2]

/-- Library census: the nested searcher's D is floor-priced against ANY opponent. -/
theorem s0_Dfloor (O : Prog) : ∀ K φ, Pf K φ → K ≤ k →
    TailTo (.plays (StatedBot0 k) O .D) φ → False :=
  no_provable_nestedSearcher_D_tail k gC gP O

/-- The prudence probe against a DupocBot-style searcher fails: its D vs `.const D`
    is its own else-play (floor). -/
theorem s0_vs_Dupoc (n : Nat) : play (n + 3) (StatedBot0 k) (DupocBot k) = some .D :=
  N_D2 (ps_false_of_floor (no_provable_searcherElse_tail k (.plays .opp .self .C) .C .D (by decide)
    (.const .D)) (by exact rfl))
theorem dupoc_vs_s0 (n : Nat) : play (n + 2) (DupocBot k) (StatedBot0 k) = some .D :=
  srch_f (me := DupocBot k) rfl (ps_false_of_not (not_plays_of (s0_vs_Dupoc 0) (by decide)))

theorem s0_vs_CB (hb : 40 * Nat.log2 k + 400 ≤ k) (n : Nat) :
    play (n + 3) (StatedBot0 k) CooperateBot = some .D :=
  N_D2 (ps_false_of_not (not_plays_of (cb_play 0 (.const .D)) (by decide)))
theorem s0_vs_DB (n : Nat) : play (n + 3) (StatedBot0 k) DefectBot = some .D :=
  N_D1 (ps_false_of_not (interp_DefectBot_plays_C_false _))

theorem s0_vs_Cupod (n : Nat) : play (n + 3) (StatedBot0 k) (CupodBot k) = some .D :=
  N_D1 (ps_false_of_floor (no_provable_searcherElse_tail k (.plays .opp .self .D) .D .C (by decide)
    (StatedBot0 k)) (by exact rfl))
theorem cupod_vs_s0 (n : Nat) : play (n + 2) (CupodBot k) (StatedBot0 k) = some .C :=
  srch_f (me := CupodBot k) rfl (ps_false_of_floor (s0_Dfloor _) (by exact rfl))

theorem s0_vs_CTroll (n : Nat) : play (n + 3) (StatedBot0 k) (CupodTrollBot k) = some .D :=
  N_D1 (ps_false_of_floor (no_provable_searcherElse_tail k (.eq .opp (CupodBot k)) .D .C (by decide)
    (StatedBot0 k)) (by exact rfl))
theorem ctroll_vs_s0 (n : Nat) : play (n + 2) (CupodTrollBot k) (StatedBot0 k) = some .C :=
  srch_f (me := CupodTrollBot k) rfl (ps_false_of_not (by
    simp [Formula.subst, Prog.subst, Formula.interp, StatedBot0, CupodBot]))

theorem s0_botDB (n : Nat) : play (n + 3) (StatedBot0 k) (.bot DefectBot) = some .D :=
  N_D1 (ps_false_of_not (interp_bot_DefectBot_plays_C_false _))
theorem s0_botCB (n : Nat) : play (n + 3) (StatedBot0 k) (.bot CooperateBot) = some .D :=
  N_D2 (ps_false_of_not (not_plays_of (play_bot_CooperateBot 0 (.const .D)) (by decide)))

theorem s0_probeDB : ∀ a n, PlaysProof (StatedBot0 k) (.bot DefectBot) (StatedBot0 k) a n → k ≤ n :=
  fun _ _ h => search_probe (body := StatedBot0 k) rfl h
    (not_pf_of_ps_false (ps_false_of_not (interp_bot_DefectBot_plays_C_false _)))

theorem s0_vs_DBot (n : Nat) : play (n + 3) (StatedBot0 k) DBot = some .D :=
  N_D1 (ps_false_of_floor (probe_floor k DefectBot (.const .D) (.const .C) (StatedBot0 k) .C .C
    s0_probeDB (by intros; simp) (fun L => const_ne_ctxPlug (by decide) L)) (by exact rfl))
theorem s0_vs_OBot (n : Nat) : play (n + 3) (StatedBot0 k) OBot = some .D :=
  N_D1 (ps_false_of_not (not_plays_of (obot_D_of_CB (s0_botCB 0)) (by decide)))
theorem s0_vs_TFT (n : Nat) : play (n + 3) (StatedBot0 k) TitForTatBot = some .D :=
  N_D1 (ps_false_of_not (not_plays_of (tft_play (s0_botCB 0)) (by decide)))

abbrev EBotElse : Prog :=
  .ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
    (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))

theorem s0_vs_EBot (n : Nat) : play (n + 3) (StatedBot0 k) EBot = some .D :=
  N_D1 (ps_false_of_floor (probe_floor k DefectBot (.const .D) EBotElse (StatedBot0 k) .C .C
    s0_probeDB (by intros; simp) (fun L => const_ne_ctxPlug (by decide) L)) (by exact rfl))

/-- S0 against itself: its prudence probe about ITSELF is floor-priced (library census). -/
theorem s0_vs_s0 (n : Nat) : play (n + 3) (StatedBot0 k) (StatedBot0 k) = some .D :=
  N_D2 (ps_false_of_floor (s0_Dfloor (.const .D)) (by exact rfl))

/-! ### The Löb leg: S0 cooperates with `.bot MirrorBot` (port of PrudentBot's) -/

theorem botM_vs_constD (fuel : Nat) : play (fuel + 4) (.bot MirrorBot) (.const .D) = some .D := by
  show eval (fuel + 4) (.bot MirrorBot) (.const .D) (.bot MirrorBot) = some .D
  simp [eval, Prog.subst, MirrorBot]

theorem prudence_botM : Pf 81 (Formula.plays (.bot MirrorBot) (.const .D) Action.D) := by
  have hPlay : play 4 (.bot MirrorBot) (.const .D) = some .D := by simpa using botM_vs_constD 0
  exact Pf.atom (atom_monotone (3 ^ 4) 81 _ (by norm_num)
    (atom_complete_searchfree (.bot MirrorBot) (.const .D) Action.D 4 rfl rfl hPlay))

theorem s0_botM_loeb_premise (k : Nat) (hk : 81 ≤ k) :
    Pf (50 * Nat.log2 k + 500)
      (.impl (.box k (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C))
             (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C)) := by
  have leg1 : Pf (20 * Nat.log2 k + 200)
      (.impl (.box k (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C))
             (Formula.plays (StatedBot0 k) (.bot MirrorBot) Action.C)) := by
    refine Pf.searchThenSearch_t k k 81
      (Formula.plays .opp .self Action.C)
      (Formula.plays .opp (.const .D) Action.D)
      Action.C Action.D (.const Action.D) (StatedBot0 k) (.bot MirrorBot) rfl
      prudence_botM (by omega) ?_
    simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, StatedBot0, MirrorBot,
      c_guard]
    omega
  have leg2 : Pf (20 * Nat.log2 k + 200)
      (.impl (Formula.plays (StatedBot0 k) (.bot MirrorBot) Action.C)
             (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C)) := by
    refine Pf.botSimStep (.bot MirrorBot) .opp .self (StatedBot0 k) Action.C rfl ?_
    simp only [Prog.subst, numCost, Formula.size, Prog.size, StatedBot0, MirrorBot]
    omega
  refine Pf.implTrans _ _ _ (20 * Nat.log2 k + 200) (20 * Nat.log2 k + 200) leg1 leg2 ?_
  simp only [numCost, Formula.size, Prog.size, StatedBot0, MirrorBot]
  omega

theorem s0_botM_ps_of_play (n : Nat) (h : play n (.bot MirrorBot) (StatedBot0 k) = some .C) :
    proofSearch k (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C) = true := by
  cases hps : proofSearch k (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C) with
  | true => rfl
  | false =>
    exfalso
    have hD : play (n + 3) (StatedBot0 k) (.bot MirrorBot) = some .D := N_D1 hps
    have hM := botM_play hD
    exact absurd (play_unique h hM) (by decide)

theorem s0_botM_C : ∃ K, ∀ k, K < k → ∀ n, play (n + 3) (StatedBot0 k) (.bot MirrorBot) = some .C := by
  let φ : Nat → Formula := fun k => Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C
  have hLoeb : ∀ k, k > 81 → Pf (50 * Nat.log2 k + 500) (.impl (.box k (φ k)) (φ k)) :=
    fun k hk => s0_botM_loeb_premise k (by omega)
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    show (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, StatedBot0, MirrorBot]
    omega
  have hpm : ∀ k, 50 * Nat.log2 k + 500 ≤ 100 * Nat.log2 k + 1000 := fun k => by omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 50 * Nat.log2 k + 500) 81 hφsz hpm hLoeb
  refine ⟨max k₂ 81, fun k hk n => ?_⟩
  have hk2 : k > k₂ := lt_of_le_of_lt (le_max_left _ _) hk
  have hkP : (81 : Nat) ≤ k := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)
  obtain ⟨m, hm⟩ := hk₂ k hk2
  obtain ⟨n', hMir⟩ := Pf_sound m (φ k) hm
  exact N_C (s0_botM_ps_of_play n' hMir) ((proofSearch_spec _ _).2 (Pf_mono prudence_botM hkP))

end S0

/-! ## S2: "do what my opponent does against me" (no search, no proof-reading rule) -/

section S2

theorem m2_play {n : Nat} {X : Prog} {a : Action} (h : play n X StatedBot2 = some a) :
    play (n + 2) StatedBot2 X = some a := by
  have hg : eval (n + 1) StatedBot2 X (.sim .opp .self) = some a := h
  show eval (n + 2) StatedBot2 X (.ite (.sim .opp .self) .C (.const .C) (.const .D)) = _
  rw [eval_ite_from_guard (n + 1) StatedBot2 X _ _ _ .C a hg]
  cases a
  · rw [if_pos (by decide)]; simp [eval]
  · rw [if_neg (by decide)]; simp [eval]

theorem m2_vs_m2_none : ∀ n, play n StatedBot2 StatedBot2 = none := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => rfl
    | 1 => show eval 1 StatedBot2 StatedBot2 (.ite (.sim .opp .self) .C (.const .C) (.const .D)) = none
           simp [eval]
    | m + 2 =>
      have hm : eval m StatedBot2 StatedBot2 StatedBot2 = none := ih m (by omega)
      have hg : eval (m + 1) StatedBot2 StatedBot2 (.sim .opp .self) = none := hm
      show eval (m + 2) StatedBot2 StatedBot2 (.ite (.sim .opp .self) .C (.const .C) (.const .D)) = none
      rw [eval]; simp [hg]

theorem m2_botDB (n : Nat) : play (n + 4) StatedBot2 (.bot DefectBot) = some .D :=
  m2_play (play_bot_DefectBot n _)
theorem m2_botCB (n : Nat) : play (n + 4) StatedBot2 (.bot CooperateBot) = some .C :=
  m2_play (play_bot_CooperateBot n _)

end S2

/-! ## Packaging -/

theorem eventual_of {P : Nat} {L R : Nat → Prog} {r : Option Outcome} (K₀ : Nat)
    (f : ∀ k, K₀ < k → 40 * Nat.log2 k + 400 ≤ k → ∀ fuel, outcome (fuel + P) (L k) (R k) = r) :
    OutcomeSpec .eventual P L R r := by
  obtain ⟨K, hK⟩ := linear_log2_add_le 40 400
  exact ⟨max K K₀, fun k hk => f k (lt_of_le_of_lt (le_max_right _ _) hk)
    (hK k (le_of_lt (lt_of_le_of_lt (le_max_left _ _) hk)))⟩

theorem universal_of {P : Nat} {L R : Nat → Prog} {r : Option Outcome}
    (f : ∀ k, ∀ fuel, outcome (fuel + P) (L k) (R k) = r) : OutcomeSpec .universal P L R r := f

-- 2b, S0 row
theorem outcome_StatedBot0_vs_CooperateBot :
    OutcomeSpec .eventual 10 StatedBot0 (fun _ => CooperateBot) (some (.D, .C)) :=
  eventual_of 0 fun k _ hb => cell (c₁ := 3) (c₂ := 1) (s0_vs_CB hb) (fun n => cb_play n _) (by omega) (by omega)
theorem outcome_StatedBot0_vs_DefectBot :
    OutcomeSpec .universal 10 StatedBot0 (fun _ => DefectBot) (some (.D, .D)) :=
  universal_of fun _ => cell (c₁ := 3) (c₂ := 1) s0_vs_DB (fun n => db_play n _) (by omega) (by omega)
theorem outcome_StatedBot0_vs_DupocBot :
    OutcomeSpec .universal 10 StatedBot0 DupocBot (some (.D, .D)) :=
  universal_of fun _ => cell (c₁ := 3) (c₂ := 2) s0_vs_Dupoc dupoc_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot0_vs_CupodBot :
    OutcomeSpec .universal 10 StatedBot0 CupodBot (some (.D, .C)) :=
  universal_of fun _ => cell (c₁ := 3) (c₂ := 2) s0_vs_Cupod cupod_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot0_vs_CupodTrollBot :
    OutcomeSpec .universal 10 StatedBot0 CupodTrollBot (some (.D, .C)) :=
  universal_of fun _ => cell (c₁ := 3) (c₂ := 2) s0_vs_CTroll ctroll_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot0_vs_DBot :
    OutcomeSpec .universal 10 StatedBot0 (fun _ => DBot) (some (.D, .C)) :=
  universal_of fun k => cell (c₁ := 3) (c₂ := 6) s0_vs_DBot
    (fun n => (dbot_play_C (s0_botDB n) : play (n + 6) DBot (StatedBot0 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot0_vs_OBot :
    OutcomeSpec .universal 10 StatedBot0 (fun _ => OBot) (some (.D, .D)) :=
  universal_of fun k => cell (c₁ := 3) (c₂ := 6) s0_vs_OBot
    (fun n => (obot_D_of_CB (s0_botCB n) : play (n + 6) OBot (StatedBot0 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot0_vs_TitForTatBot :
    OutcomeSpec .universal 10 StatedBot0 (fun _ => TitForTatBot) (some (.D, .D)) :=
  universal_of fun k => cell (c₁ := 3) (c₂ := 6) s0_vs_TFT
    (fun n => (tft_play (s0_botCB n) : play (n + 6) TitForTatBot (StatedBot0 k) = _)) (by omega) (by omega)
theorem outcome_StatedBot0_vs_EBot :
    OutcomeSpec .eventual 10 StatedBot0 (fun _ => EBot) (some (.D, .C)) := by
  obtain ⟨K, hK⟩ := s0_botM_C
  exact eventual_of K fun k hk _ => cell (c₁ := 3) (c₂ := 8) s0_vs_EBot
    (fun n => (ebot_C_of_M (s0_botDB n) (s0_botCB n) (hK k hk n) : play (n + 8) EBot (StatedBot0 k) = _))
    (by omega) (by omega)

-- 2b, S2 row (all budget-free)
theorem outcome_StatedBot2_vs_CooperateBot :
    OutcomeSpec .nobudget 12 (fun _ => StatedBot2) (fun _ => CooperateBot) (some (.C, .C)) :=
  cell (c₁ := 3) (c₂ := 1) (fun n => m2_play (cb_play n _)) (fun n => cb_play n _) (by omega) (by omega)
theorem outcome_StatedBot2_vs_DefectBot :
    OutcomeSpec .nobudget 12 (fun _ => StatedBot2) (fun _ => DefectBot) (some (.D, .D)) :=
  cell (c₁ := 3) (c₂ := 1) (fun n => m2_play (db_play n _)) (fun n => db_play n _) (by omega) (by omega)
theorem outcome_StatedBot2_vs_DBot :
    OutcomeSpec .nobudget 12 (fun _ => StatedBot2) (fun _ => DBot) (some (.C, .C)) :=
  cell (c₁ := 9) (c₂ := 7) (fun n => m2_play (dbot_play_C (m2_botDB n)))
    (fun n => dbot_play_C (m2_botDB n)) (by omega) (by omega)
theorem outcome_StatedBot2_vs_TitForTatBot :
    OutcomeSpec .nobudget 12 (fun _ => StatedBot2) (fun _ => TitForTatBot) (some (.C, .C)) :=
  cell (c₁ := 9) (c₂ := 7) (fun n => m2_play (tft_play (m2_botCB n)))
    (fun n => tft_play (m2_botCB n)) (by omega) (by omega)
theorem outcome_StatedBot2_vs_OBot :
    OutcomeSpec .nobudget 12 (fun _ => StatedBot2) (fun _ => OBot) (some (.D, .D)) :=
  cell (c₁ := 10) (c₂ := 8)
    (fun n => m2_play (obot_D_of_CB_DB (m2_botCB n) (m2_botDB n)))
    (fun n => obot_D_of_CB_DB (m2_botCB n) (m2_botDB n)) (by omega) (by omega)
theorem outcome_StatedBot2_vs_EBot :
    OutcomeSpec .nobudget 12 (fun _ => StatedBot2) (fun _ => EBot) (some (.C, .C)) :=
  cell (c₁ := 10) (c₂ := 8)
    (fun n => m2_play (ebot_C_of_CB (m2_botDB n) (m2_botCB n)))
    (fun n => ebot_C_of_CB (m2_botDB n) (m2_botCB n)) (by omega) (by omega)
theorem ctroll_vs_m2 (k n : Nat) : play (n + 2) (CupodTrollBot k) StatedBot2 = some .C :=
  srch_f (me := CupodTrollBot k) rfl (ps_false_of_not (by
    simp [Formula.subst, Prog.subst, Formula.interp, StatedBot2, CupodBot]))
theorem outcome_StatedBot2_vs_CupodTrollBot :
    OutcomeSpec .universal 12 (fun _ => StatedBot2) CupodTrollBot (some (.C, .C)) :=
  universal_of fun k => cell (c₁ := 4) (c₂ := 2) (fun n => m2_play (ctroll_vs_m2 k n))
    (ctroll_vs_m2 k) (by omega) (by omega)

-- 2a
theorem outcome_StatedBot0_vs_StatedBot0 :
    OutcomeSpec .universal 10 StatedBot0 StatedBot0 (some (.D, .D)) :=
  universal_of fun _ => cell (c₁ := 3) (c₂ := 3) s0_vs_s0 s0_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot0_vs_StatedBot1 :
    OutcomeSpec .universal 10 StatedBot0 (fun _ => StatedBot1) (some (.D, .D)) :=
  universal_of fun _ => cell (c₁ := 3) (c₂ := 1) s0_vs_DB (fun n => db_play n _) (by omega) (by omega)
theorem outcome_StatedBot0_vs_StatedBot3 :
    OutcomeSpec .universal 10 StatedBot0 StatedBot3 (some (.D, .D)) :=
  universal_of fun _ => cell (c₁ := 3) (c₂ := 2) s0_vs_Dupoc dupoc_vs_s0 (by omega) (by omega)
theorem outcome_StatedBot1_vs_StatedBot2 :
    OutcomeSpec .nobudget 12 (fun _ => StatedBot1) (fun _ => StatedBot2) (some (.D, .D)) :=
  cell (c₁ := 1) (c₂ := 3) (fun n => db_play n _) (fun n => m2_play (db_play n _)) (by omega) (by omega)
/-- S2 against itself never terminates (mutual simulation), at every fuel. -/
theorem outcome_StatedBot2_vs_StatedBot2 :
    OutcomeSpec .nobudget 0 (fun _ => StatedBot2) (fun _ => StatedBot2) none := by
  intro fuel
  simp [outcome, m2_vs_m2_none]
end PD.StatedLuna
