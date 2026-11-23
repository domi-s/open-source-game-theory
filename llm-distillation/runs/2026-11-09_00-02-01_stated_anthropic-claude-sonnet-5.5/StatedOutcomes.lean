import PrisonersDilemma.BaseTheorems
import PrisonersDilemma.Base.Helpers
import PrisonersDilemma.Base.Asymptotics
import PrisonersDilemma.Base.Exclusion
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
import PrisonersDilemma.Bots.LlmGenerations.PrudentBot
import PrisonersDilemma.Theorems.CooperateBot.Helpers
import PrisonersDilemma.Theorems.DefectBot.Helpers
import PrisonersDilemma.Theorems.CupodBot.Helpers
import PrisonersDilemma.Theorems.CupodTrollBot.Helpers
import PrisonersDilemma.Theorems.PrudentBot.vs_CooperateBot
import PrisonersDilemma.Theorems.PrudentBot.vs_DBot
import PrisonersDilemma.Theorems.PrudentBot.vs_CupodTrollBot
import PrisonersDilemma.Theorems.PrudentBot.vs_EBot
import PrisonersDilemma.Theorems.PrudentBot.vs_DupocBot

/-! # Stated outcomes — anthropic/claude-sonnet-5.5, run 2026-11-09_00-02-01 (examples spec)

Two canonical programs:
* `StatedBot0` (21 samples) = `PrudentBot2 k (2k+64)`: cooperation search at `k`, prudence
  ("opp defects vs DefectBot") at `2k+64`. Same program as haiku run 2026-11-09_00-01-04's
  `StatedBot6`.
* `StatedBot1` (9 samples) = `DupocBot` (`rfl`); its row is the library's.

Row of `StatedBot0` against the 9 zoo bots, at every large `k` (one shared budget):
CB (D,C), Cupod (D,C), DBot (D,C), DB (D,D), Dupoc (C,C), OBot (D,D), TFT (D,D),
EBot (D,C), CTroll (D,C). -/

open PD PD.BaseTheorems PD.Bots PD.Theorems
namespace PD.StatedSonnetOld

def StatedBot0 (k : Nat) : Prog :=
  .search k (.plays .opp .self Action.C)
    (.search (2 * k + 64) (.plays .opp (.bot DefectBot) Action.D) (.const Action.C) (.const Action.D))
    (.const Action.D)

def StatedBot1 (k : Nat) : Prog := .search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)

theorem statedBot0_is_PrudentBot2 : StatedBot0 = fun k => PrudentBot2 k (2 * k + 64) := rfl
theorem statedBot1_is_DupocBot : StatedBot1 = DupocBot := rfl

/-! ## Evaluation of `StatedBot0` from its two guards -/

section Eval
variable (k fuel : Nat) (q : Prog)

theorem s0_outer_false (h : proofSearch k (.plays q (StatedBot0 k) .C) = false) :
    play (fuel + 2) (StatedBot0 k) q = some .D := by
  show eval (fuel + 2) (StatedBot0 k) q (StatedBot0 k) = some .D
  unfold StatedBot0 at h ⊢
  simp [eval, Prog.subst, Formula.subst, h]

theorem s0_inner_false (h1 : proofSearch k (.plays q (StatedBot0 k) .C) = true)
    (h2 : proofSearch (2 * k + 64) (.plays q (.bot DefectBot) .D) = false) :
    play (fuel + 3) (StatedBot0 k) q = some .D := by
  show eval (fuel + 3) (StatedBot0 k) q (StatedBot0 k) = some .D
  unfold StatedBot0 at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1, h2]

theorem s0_both_true (h1 : proofSearch k (.plays q (StatedBot0 k) .C) = true)
    (h2 : proofSearch (2 * k + 64) (.plays q (.bot DefectBot) .D) = true) :
    play (fuel + 3) (StatedBot0 k) q = some .C := by
  show eval (fuel + 3) (StatedBot0 k) q (StatedBot0 k) = some .C
  unfold StatedBot0 at h1 ⊢
  simp [eval, Prog.subst, Formula.subst, h1, h2]

/-- Defects whenever its prudence check fails, whichever way the outer search goes. -/
theorem s0_D_of_imprudent (h2 : proofSearch (2 * k + 64) (.plays q (.bot DefectBot) .D) = false) :
    play (fuel + 3) (StatedBot0 k) q = some .D := by
  cases h1 : proofSearch k (.plays q (StatedBot0 k) .C) with
  | false => simpa [Nat.add_assoc] using s0_outer_false k (fuel + 1) q h1
  | true => exact s0_inner_false k fuel q h1 h2

theorem s0_outer_true_of_play_C (n : Nat) (h : play n (StatedBot0 k) q = some .C) :
    proofSearch k (.plays q (StatedBot0 k) .C) = true := by
  cases hps : proofSearch k (.plays q (StatedBot0 k) .C) with
  | true => rfl
  | false =>
    exfalso
    rcases n with _ | _ | n
    · simp [play, eval] at h
    · simp [play, eval, StatedBot0, Prog.subst, Formula.subst] at h
    · rw [s0_outer_false k n q hps] at h; cases h

end Eval

theorem ps_false_of_not {k : Nat} {φ : Formula} (h : ¬ φ.interp) : proofSearch k φ = false := by
  cases hps : proofSearch k φ with
  | true => exact absurd (proofSearch_sound _ _ hps) h
  | false => rfl

theorem s0_vs_botDB (k fuel : Nat) : play (fuel + 2) (StatedBot0 k) (.bot DefectBot) = some .D :=
  s0_outer_false k fuel _ (ps_false_of_not (interp_bot_DefectBot_plays_C_false _))

theorem s0_vs_botCB (k fuel : Nat) : play (fuel + 3) (StatedBot0 k) (.bot CooperateBot) = some .D :=
  s0_D_of_imprudent k fuel _ (ps_false_of_not (interp_bot_CooperateBot_plays_D_false _))

/-! ## The D floor for a nested searcher whose inner budget is `j ≥ k`

`no_provable_nestedSearcher_D_tail` (Base/Exclusion) with the inner search's budget freed
from `k` to any `j ≥ k`; the proof is the library's, the two floor steps now use `k ≤ j`. -/

theorem no_provable_nestedSearcher2_D_tail (k j : Nat) (hj : k ≤ j) (g₁ g₂ : Formula) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k →
      TailTo (.plays (.search k g₁ (.search j g₂ (.const .C) (.const .D)) (.const .D)) O .D) φ
        → False := by
  refine no_provable_tailTo_floor k _ O .D ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro K hK hA
    cases hA with
    | mk hpp hn =>
      cases hpp with
      | search_t _ hbr =>
          cases hbr with
          | search_t _ hc => cases hc
          | search_f _ _ => simp only [c_node] at hn; omega
      | search_f _ _ => simp only [c_node] at hn; omega
  · rintro (⟨_, _, _, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, h⟩ | ⟨_, _, _, _, h⟩ |
      ⟨_, _, _, _, _, _, _, h⟩) <;> simp at h
  · intro defs i h; simp at h
  · intro k₁ ψ₁ k₂ ψ₂ c1 q h; simp at h
  · intro L h
    cases L with
    | nil => simp [searchPlug] at h
    | cons hd tl =>
        obtain ⟨g₁', ψ₁, e₁⟩ := hd
        simp only [searchPlug, Prog.search.injEq] at h
        obtain ⟨-, -, h, -⟩ := h
        cases tl with
        | nil => simp [searchPlug] at h
        | cons hd' tl' =>
            obtain ⟨g₂', ψ₂', e₂⟩ := hd'
            simp only [searchPlug, Prog.search.injEq] at h
            obtain ⟨-, -, h, -⟩ := h
            cases tl' with
            | nil => simp [searchPlug] at h
            | cons hd'' tl'' =>
                obtain ⟨g₃, ψ₃, e₃⟩ := hd''
                simp [searchPlug] at h
  · intro hd L h
    cases hd with
    | searchL g ψ e =>
        simp only [ctxPlug, Prog.search.injEq] at h
        obtain ⟨-, -, h, -⟩ := h
        cases L with
        | nil => simp [ctxPlug] at h
        | cons hd' tl' =>
            cases hd' with
            | searchL g' ψ' e' =>
                simp only [ctxPlug, Prog.search.injEq] at h
                exact const_ne_ctxPlug (by decide) tl' h.2.2.1
            | iteL z' aT' other' => simp [ctxPlug] at h
    | iteL z aT other => simp [ctxPlug] at h
  · intro hd L hme
    cases hd with
    | thenL g ψ e =>
        simp only [plug2, Prog.search.injEq] at hme
        obtain ⟨rfl, rfl, hplug, rfl⟩ := hme
        cases L with
        | nil => simp [plug2] at hplug
        | cons hd2 tl2 =>
            cases hd2 with
            | thenL g2 ψ2 e2 =>
                exfalso
                simp only [plug2, Prog.search.injEq] at hplug
                obtain ⟨-, -, hplug2, -⟩ := hplug
                cases tl2 with
                | nil => simp [plug2] at hplug2
                | cons hd3 tl3 => cases hd3 <;> simp [plug2] at hplug2
            | elseL g2 P2 Q2 c2 q2 =>
                simp only [plug2, Prog.search.injEq] at hplug
                obtain ⟨rfl, -, -, -⟩ := hplug
                simp only [layersCost, layerCost, c_node]
                omega
    | elseL g P' Q' c' q =>
        simp only [plug2, Prog.search.injEq] at hme
        obtain ⟨rfl, -, -, -⟩ := hme
        simp only [layersCost, layerCost, c_node]
        omega

theorem no_provable_s0_D_tail (k : Nat) (O : Prog) :
    ∀ K φ, Pf K φ → K ≤ k → TailTo (.plays (StatedBot0 k) O .D) φ → False :=
  fun K φ hp hK ht => no_provable_nestedSearcher2_D_tail k (2 * k + 64) (by omega) _ _ O K φ hp hK
    (by simpa only [StatedBot0] using ht)

/-! ## The 9 cells -/

-- CooperateBot: prudence fails (CooperateBot is a sucker) → D.
theorem s0_vs_CB (k fuel : Nat) : play (fuel + 3) (StatedBot0 k) CooperateBot = some .D :=
  s0_D_of_imprudent k fuel _ (proofSearch_false_CooperateBot_prudence _)

-- DefectBot: never cooperates → outer search fails → D.
theorem s0_vs_DB (k fuel : Nat) : play (fuel + 2) (StatedBot0 k) DefectBot = some .D :=
  s0_outer_false k fuel _ (ps_false_of_not (interp_DefectBot_plays_C_false _))

-- DBot: cooperates with everything that defects vs DefectBot (so with us), but is a sucker → D.
theorem s0_vs_DBot (k fuel : Nat) : play (fuel + 3) (StatedBot0 k) DBot = some .D :=
  s0_D_of_imprudent k fuel _ (proofSearch_false_DBot_prudence _)

theorem dbot_vs_s0 (k fuel : Nat) : play (fuel + 4) DBot (StatedBot0 k) = some .C := by
  have hGuard : eval (fuel + 3) DBot (StatedBot0 k) (.sim .opp (.bot DefectBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 2) DBot (StatedBot0 k) DefectBot Action.D (s0_vs_botDB k fuel)
  have hPlay := eval_ite_from_guard (fuel + 3) DBot (StatedBot0 k) (.sim .opp (.bot DefectBot))
    (.const Action.D) (.const Action.C) Action.C Action.D hGuard
  show eval (fuel + 4) DBot (StatedBot0 k) DBot = some .C
  rw [show DBot = .ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.D) (.const Action.C) from rfl] at *
  rw [hPlay]; rfl

-- CupodBot: two else-play floors facing each other → (D, C).
theorem s0_vs_Cupod (k fuel : Nat) : play (fuel + 2) (StatedBot0 k) (CupodBot k) = some .D := by
  refine s0_outer_false k fuel _ ?_
  cases h : proofSearch k (.plays (CupodBot k) (StatedBot0 k) .C) with
  | true =>
      exact absurd ((proofSearch_spec k _).mp h)
        (fun hp => no_provable_CupodBot_C_tail k (StatedBot0 k) k _ hp le_rfl (by simp))
  | false => rfl

theorem cupod_vs_s0 (k fuel : Nat) : play (fuel + 2) (CupodBot k) (StatedBot0 k) = some .C := by
  have h : proofSearch k (.plays (StatedBot0 k) (CupodBot k) .D) = false := by
    cases h : proofSearch k (.plays (StatedBot0 k) (CupodBot k) .D) with
    | true =>
        exact absurd ((proofSearch_spec k _).mp h)
          (fun hp => no_provable_s0_D_tail k (CupodBot k) k _ hp le_rfl (by simp))
    | false => rfl
  show eval (fuel + 2) (CupodBot k) (StatedBot0 k) (CupodBot k) = some .C
  unfold CupodBot at h ⊢
  simp [eval, Prog.subst, Formula.subst, h]

-- CupodTrollBot: never defects vs a `.bot`, so prudence fails → D; it trusts us → C.
theorem s0_vs_CTroll (k fuel : Nat) : play (fuel + 3) (StatedBot0 k) (CupodTrollBot k) = some .D :=
  s0_D_of_imprudent k fuel _ (ps_false_of_not (CupodTrollBot_never_D_vs_botDefect k))

theorem ctroll_vs_s0 (k fuel : Nat) : play (fuel + 2) (CupodTrollBot k) (StatedBot0 k) = some .C :=
  CupodTrollBot_cooperates_if_opp_not_CupodBot k fuel _ (by simp [StatedBot0, CupodBot])

-- OBot and TitForTatBot: both probe us vs `.bot CooperateBot`, see D, defect → (D, D).
theorem obot_vs_s0 (k fuel : Nat) : play (fuel + 5) OBot (StatedBot0 k) = some .D := by
  have hGuard : eval (fuel + 4) OBot (StatedBot0 k) (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 3) OBot (StatedBot0 k) CooperateBot Action.D (s0_vs_botCB k fuel)
  have hPlay := eval_ite_from_guard (fuel + 4) OBot (StatedBot0 k) (.sim .opp (.bot CooperateBot))
    (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
    (.const Action.D) Action.C Action.D hGuard
  show eval (fuel + 5) OBot (StatedBot0 k) OBot = some .D
  rw [show OBot = .ite (.sim .opp (.bot CooperateBot)) Action.C
        (.ite (.sim .opp (.bot DefectBot)) Action.C (.const Action.C) (.const Action.D))
        (.const Action.D) from rfl] at *
  rw [hPlay]; rfl

theorem tft_vs_s0 (k fuel : Nat) : play (fuel + 5) TitForTatBot (StatedBot0 k) = some .D := by
  have hGuard : eval (fuel + 4) TitForTatBot (StatedBot0 k) (.sim .opp (.bot CooperateBot)) = some .D :=
    eval_sim_opp_bot_of_play (fuel + 3) TitForTatBot (StatedBot0 k) CooperateBot Action.D (s0_vs_botCB k fuel)
  have hPlay := eval_ite_from_guard (fuel + 4) TitForTatBot (StatedBot0 k)
    (.sim .opp (.bot CooperateBot)) (.const Action.C) (.const Action.D) Action.C Action.D hGuard
  show eval (fuel + 5) TitForTatBot (StatedBot0 k) TitForTatBot = some .D
  rw [show TitForTatBot = .ite (.sim .opp (.bot CooperateBot)) Action.C
        (.const Action.C) (.const Action.D) from rfl] at *
  rw [hPlay]; rfl

theorem not_plays_C_of_D {n : Nat} {p q : Prog} (h : ∀ m, play (m + n) p q = some .D) :
    ¬ (Formula.plays p q .C).interp := by
  rintro ⟨m, hm⟩
  have hC : play (m + n) p q = some .C := by unfold play at hm ⊢; exact eval_mono_le hm _ (by omega)
  rw [h m] at hC; cases hC

theorem s0_vs_OBot (k fuel : Nat) : play (fuel + 2) (StatedBot0 k) OBot = some .D :=
  s0_outer_false k fuel _ (ps_false_of_not (not_plays_C_of_D (n := 5) (obot_vs_s0 k)))

theorem s0_vs_TFT (k fuel : Nat) : play (fuel + 2) (StatedBot0 k) TitForTatBot = some .D :=
  s0_outer_false k fuel _ (ps_false_of_not (not_plays_C_of_D (n := 5) (tft_vs_s0 k)))

/-! ### EBot: we defect (floor through our own failed probe search); EBot cooperates past
the Löb threshold, since we cooperate with `.bot MirrorBot` (bounded Löb). -/

theorem s0_vs_EBot (k fuel : Nat) : play (fuel + 2) (StatedBot0 k) EBot = some .D := by
  refine s0_outer_false k fuel _ ?_
  cases h : proofSearch k (.plays EBot (StatedBot0 k) .C) with
  | false => rfl
  | true =>
    refine absurd ((proofSearch_spec k _).mp h) (fun hp => ?_)
    refine no_provable_probeFirst_tail k DefectBot (.const .D)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))
        .C .C (.plays .opp .self .C)
        (.search (2 * k + 64) (.plays .opp (.bot DefectBot) .D) (.const .C) (.const .D))
        (.const .D) ?_ ?_ ?_ k _ hp le_rfl ?_
    · simpa [Formula.subst, Prog.subst, StatedBot0] using
        interp_bot_DefectBot_plays_C_false (StatedBot0 k)
    · intro k' ψ c0 c1 h; simp at h
    · exact fun L => const_ne_ctxPlug (by decide) L
    · simp [EBot, StatedBot0]

theorem s0_botM_loeb_premise (k : Nat) (hk : 81 ≤ k) :
    Pf (50 * Nat.log2 k + 500)
      (.impl (.box k (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C))
             (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C)) := by
  have hlg := log2_stagger_le k
  have leg1 : Pf (20 * Nat.log2 k + 200)
      (.impl (.box k (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C))
             (Formula.plays (StatedBot0 k) (.bot MirrorBot) Action.C)) := by
    refine Pf.searchThenSearch_t k (2 * k + 64) 81
      (Formula.plays .opp .self Action.C) (Formula.plays .opp (.bot DefectBot) Action.D)
      Action.C Action.D (.const Action.D) (StatedBot0 k) (.bot MirrorBot) rfl
      prudence_provable_bot (by omega) ?_
    simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, StatedBot0, MirrorBot,
      DefectBot, c_guard]
    omega
  have leg2 : Pf (20 * Nat.log2 k + 200)
      (.impl (Formula.plays (StatedBot0 k) (.bot MirrorBot) Action.C)
             (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C)) := by
    refine Pf.botSimStep (.bot MirrorBot) .opp .self (StatedBot0 k) Action.C rfl ?_
    simp only [Prog.subst, numCost, Formula.size, Prog.size, StatedBot0, MirrorBot, DefectBot]
    omega
  refine Pf.implTrans _ _ _ (20 * Nat.log2 k + 200) (20 * Nat.log2 k + 200) leg1 leg2 ?_
  simp only [numCost, Formula.size, Prog.size, StatedBot0, MirrorBot, DefectBot]
  omega

theorem s0_vs_botM :
    ∃ k₂, ∀ k, k₂ < k → ∀ fuel, play (fuel + 3) (StatedBot0 k) (.bot MirrorBot) = some .C := by
  let φ : Nat → Formula := fun k => .plays (.bot MirrorBot) (StatedBot0 k) .C
  have hφsz : ∀ k, (φ k).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    show (Formula.plays (.bot MirrorBot) (StatedBot0 k) Action.C).size ≤ _
    simp only [numCost, Formula.size, Prog.size, StatedBot0, MirrorBot, DefectBot]
    omega
  obtain ⟨k₂, hk₂⟩ := pblt_engine_id φ (fun k => 50 * Nat.log2 k + 500) 81 hφsz
    (fun k => by dsimp only; omega) (fun k hk => s0_botM_loeb_premise k (by omega))
  refine ⟨max k₂ 81, fun k hk fuel => ?_⟩
  obtain ⟨m, hm⟩ := hk₂ k (lt_of_le_of_lt (le_max_left _ _) hk)
  obtain ⟨n, hplay⟩ := Pf_sound m (φ k) hm
  have h1 : proofSearch k (.plays (.bot MirrorBot) (StatedBot0 k) .C) = true := by
    rcases n with _ | _ | n
    · simp [play, eval] at hplay
    · simp [play, eval] at hplay
    · have heq : play (n + 2) (.bot MirrorBot) (StatedBot0 k) = play n (StatedBot0 k) (.bot MirrorBot) := by
        simp [play, eval, Prog.subst, MirrorBot]
      rw [heq] at hplay
      exact s0_outer_true_of_play_C k _ n hplay
  have h2 : proofSearch (2 * k + 64) (.plays (.bot MirrorBot) (.bot DefectBot) .D) = true :=
    (proofSearch_spec _ _).2 (Pf_mono prudence_provable_bot (by omega))
  exact s0_both_true k fuel _ h1 h2

theorem ebot_vs_s0 :
    ∃ k₂, ∀ k, k₂ < k → ∀ fuel, play (fuel + 7) EBot (StatedBot0 k) = some .C := by
  obtain ⟨k₂, hMir⟩ := s0_vs_botM
  refine ⟨k₂, fun k hk fuel => ?_⟩
  have hG1 : eval (fuel + 6) EBot (StatedBot0 k) (.sim .opp (.bot DefectBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 5) EBot (StatedBot0 k) DefectBot .D (s0_vs_botDB k (fuel + 3))
  have hG2 : eval (fuel + 5) EBot (StatedBot0 k) (.sim .opp (.bot CooperateBot)) = some .D := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 4) EBot (StatedBot0 k) CooperateBot .D (s0_vs_botCB k (fuel + 1))
  have hG3 : eval (fuel + 4) EBot (StatedBot0 k) (.sim .opp (.bot MirrorBot)) = some .C := by
    simpa [Nat.add_assoc] using
      eval_sim_opp_bot_of_play (fuel + 3) EBot (StatedBot0 k) MirrorBot .C (hMir k hk fuel)
  have hIte3 : eval (fuel + 5) EBot (StatedBot0 k)
      (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG3]; rfl
  have hIte2 : eval (fuel + 6) EBot (StatedBot0 k)
      (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
        (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D))) = some .C := by
    rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG2]; exact hIte3
  show eval (fuel + 7) EBot (StatedBot0 k)
      (.ite (.sim .opp (.bot DefectBot)) .C (.const .D)
        (.ite (.sim .opp (.bot CooperateBot)) .C (.const .C)
          (.ite (.sim .opp (.bot MirrorBot)) .C (.const .C) (.const .D)))) = some .C
  rw [eval_ite_from_guard _ _ _ _ _ _ _ _ hG1]; exact hIte2

/-! ### DupocBot: mutual cooperation at ONE shared budget. Our prudence check runs at
`2k+64`, which affords Dupoc's floor-priced else-play vs `.bot DefectBot`, so the
`PrudentBot (2k+64)` staggered argument goes through with our outer search at `k`. -/

theorem s0_dupoc_legPD (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box k (.plays (DupocBot k) (StatedBot0 k) .C)) (.plays (StatedBot0 k) (DupocBot k) .C)) := by
  have hlk := log2_le_self k
  have hlg := log2_stagger_le k
  refine Pf.searchThenSearch_t k (2 * k + 64) (k + Nat.log2 k + 15)
    (.plays .opp .self .C) (.plays .opp (.bot DefectBot) .D)
    .C .D (.const .D) (StatedBot0 k) (DupocBot k) rfl
    (by simpa [Formula.subst, Prog.subst] using prudence_dupoc k) (by omega) ?_
  simp only [numCost, Formula.subst, Prog.subst, Formula.size, Prog.size, DupocBot, StatedBot0,
    DefectBot, c_guard]
  omega

theorem s0_dupoc_legDP (k : Nat) :
    Pf (30 * Nat.log2 k + 700)
      (.impl (.box k (.plays (StatedBot0 k) (DupocBot k) .C)) (.plays (DupocBot k) (StatedBot0 k) .C)) := by
  have hlg := log2_stagger_le k
  refine Pf.searchBranch k (.plays .opp .self .C) .C .D (DupocBot k) (StatedBot0 k) rfl ?_
  simp only [Formula.subst, Prog.subst, numCost, Formula.size, Prog.size, DupocBot, StatedBot0, DefectBot]
  omega

theorem s0_dupoc_coop :
    ∃ k₂, ∀ k, k₂ < k → ∀ fuel,
      play (fuel + 3) (StatedBot0 k) (DupocBot k) = some .C ∧
      play (fuel + 3) (DupocBot k) (StatedBot0 k) = some .C := by
  have hsz : ∀ k, (Formula.plays (DupocBot k) (StatedBot0 k) .C).size ≤ 100 * Nat.log2 k + 1000 ∧
      (Formula.plays (StatedBot0 k) (DupocBot k) .C).size ≤ 100 * Nat.log2 k + 1000 := by
    intro k
    have hlg := log2_stagger_le k
    constructor <;>
    · simp only [numCost, Formula.size, Prog.size, StatedBot0, DupocBot, DefectBot]; omega
  obtain ⟨k₂, hk₂⟩ := mutual_pblt_engine_staggered
    (fun k => Formula.plays (DupocBot k) (StatedBot0 k) .C)
    (fun k => Formula.plays (StatedBot0 k) (DupocBot k) .C)
    (fun k => k) (fun k => 30 * Nat.log2 k + 700) (fun k => 30 * Nat.log2 k + 700) 0
    (fun k => le_rfl) (fun k => by dsimp only; omega) (fun k => (hsz k).1) (fun k => (hsz k).2)
    (fun k => by dsimp only; omega) (fun k => by dsimp only; omega)
    (fun k _ => s0_dupoc_legPD k) (fun k _ => s0_dupoc_legDP k)
  obtain ⟨KL, hKL⟩ := linear_log2_add_le 1 20
  refine ⟨max k₂ KL, fun k hk fuel => ?_⟩
  have hKLk : Nat.log2 k + 20 ≤ k := by
    have := hKL k (le_of_lt (lt_of_le_of_lt (le_max_right _ _) hk)); omega
  obtain ⟨m, hm⟩ := hk₂ k (lt_of_le_of_lt (le_max_left _ _) hk)
  obtain ⟨n, hplayD⟩ := Pf_sound m _ hm
  have hpsP : proofSearch k (.plays (StatedBot0 k) (DupocBot k) .C) = true :=
    ps_k_of_play_dupoc_any k n (StatedBot0 k) hplayD
  have hpsD : proofSearch k (.plays (DupocBot k) (StatedBot0 k) .C) = true := by
    refine (proofSearch_spec _ _).2 (Pf.atom
      (⟨PlaysProof.search_t ((proofSearch_spec _ _).1 hpsP) PlaysProof.const, ?_⟩ :
        AtomProvable k (.plays (DupocBot k) (StatedBot0 k) .C)))
    show c_leaf + c_guard k + c_node ≤ k
    simp only [numCost, c_leaf, c_guard, c_node]
    omega
  have hprud : proofSearch (2 * k + 64) (.plays (DupocBot k) (.bot DefectBot) .D) = true :=
    (proofSearch_spec _ _).2 (Pf_mono (prudence_dupoc k) (by omega))
  exact ⟨s0_both_true k fuel _ hpsD hprud,
    by simpa [Nat.add_assoc] using dupoc_C_vs_any k (fuel + 1) (StatedBot0 k) hpsP⟩

/-! ## Packaging -/

theorem outcome_StatedBot0_vs_CooperateBot :
    OutcomeSpec .universal 3 StatedBot0 (fun _ => CooperateBot) (some (.D, .C)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (s0_vs_CB k fuel)
    (by simpa [Nat.add_comm] using play_CooperateBot (fuel + 2) (StatedBot0 k))

theorem outcome_StatedBot0_vs_DefectBot :
    OutcomeSpec .universal 2 StatedBot0 (fun _ => DefectBot) (some (.D, .D)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (s0_vs_DB k fuel)
    (by simpa [Nat.add_comm] using play_DefectBot (fuel + 1) (StatedBot0 k))

theorem outcome_StatedBot0_vs_DBot :
    OutcomeSpec .universal 4 StatedBot0 (fun _ => DBot) (some (.D, .C)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (by simpa [Nat.add_assoc] using s0_vs_DBot k (fuel + 1)) (dbot_vs_s0 k fuel)

theorem outcome_StatedBot0_vs_CupodBot :
    OutcomeSpec .universal 2 StatedBot0 CupodBot (some (.D, .C)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (s0_vs_Cupod k fuel) (cupod_vs_s0 k fuel)

theorem outcome_StatedBot0_vs_CupodTrollBot :
    OutcomeSpec .universal 3 StatedBot0 CupodTrollBot (some (.D, .C)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (s0_vs_CTroll k fuel)
    (by simpa [Nat.add_assoc] using ctroll_vs_s0 k (fuel + 1))

theorem outcome_StatedBot0_vs_OBot :
    OutcomeSpec .universal 5 StatedBot0 (fun _ => OBot) (some (.D, .D)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (by simpa [Nat.add_assoc] using s0_vs_OBot k (fuel + 3)) (obot_vs_s0 k fuel)

theorem outcome_StatedBot0_vs_TitForTatBot :
    OutcomeSpec .universal 5 StatedBot0 (fun _ => TitForTatBot) (some (.D, .D)) := fun k fuel =>
  outcome_of_plays _ _ _ _ _ (by simpa [Nat.add_assoc] using s0_vs_TFT k (fuel + 3)) (tft_vs_s0 k fuel)

theorem outcome_StatedBot0_vs_EBot :
    OutcomeSpec .eventual 7 StatedBot0 (fun _ => EBot) (some (.D, .C)) := by
  obtain ⟨k₂, hE⟩ := ebot_vs_s0
  exact ⟨k₂, fun k hk fuel => outcome_of_plays _ _ _ _ _
    (by simpa [Nat.add_assoc] using s0_vs_EBot k (fuel + 5)) (hE k hk fuel)⟩

theorem outcome_StatedBot0_vs_DupocBot :
    OutcomeSpec .eventual 3 StatedBot0 DupocBot (some (.C, .C)) := by
  obtain ⟨k₂, h⟩ := s0_dupoc_coop
  exact ⟨k₂, fun k hk fuel => outcome_of_plays _ _ _ _ _ (h k hk fuel).1 (h k hk fuel).2⟩

end PD.StatedSonnetOld
