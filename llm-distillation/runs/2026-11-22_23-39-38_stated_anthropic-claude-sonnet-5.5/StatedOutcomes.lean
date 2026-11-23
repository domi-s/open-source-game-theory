import PrisonersDilemma.Theorems.DupocBot.vs_CooperateBot
import PrisonersDilemma.Theorems.DupocBot.vs_CupodBot
import PrisonersDilemma.Theorems.DupocBot.vs_DBot
import PrisonersDilemma.Theorems.DupocBot.vs_DefectBot
import PrisonersDilemma.Theorems.DupocBot.vs_DupocBot
import PrisonersDilemma.Theorems.DupocBot.vs_OBot
import PrisonersDilemma.Theorems.DupocBot.vs_TitForTatBot
import PrisonersDilemma.Theorems.DupocBot.vs_EBot
import PrisonersDilemma.Theorems.DupocBot.vs_CupodTrollBot

/-! # Stated outcomes — anthropic/claude-sonnet-5.5 (run 2026-11-22_23-39-38)

All 20 samples are ONE canonical program, `StatedBot0`, and it IS `DupocBot` (`rfl`).
So every 2b cell is a library theorem, restated here for `StatedBot0`, and the only 2a
cell (S0 vs S0) is DupocBot self-play: `(C, C)` at all large `k` (bounded Löb). -/

open PD PD.Bots PD.Theorems
namespace PD.StatedSonnet

def StatedBot0 (k : Nat) : Prog := .search k (.plays .opp .self Action.C) (.const Action.C) (.const Action.D)

theorem statedBot0_is_DupocBot : StatedBot0 = DupocBot := rfl

theorem s0_vs_CooperateBot : OutcomeSpec .eventual 2 StatedBot0 (fun _ => CooperateBot) (some (.C, .C)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_CooperateBot

theorem s0_vs_CupodBot : OutcomeSpec .universal 2 StatedBot0 CupodBot (some (.D, .C)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_CupodBot

theorem s0_vs_DBot : OutcomeSpec .universal 4 StatedBot0 (fun _ => DBot) (some (.D, .C)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_DBot

theorem s0_vs_DefectBot : OutcomeSpec .universal 2 StatedBot0 (fun _ => DefectBot) (some (.D, .D)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_DefectBot

theorem s0_vs_DupocBot : OutcomeSpec .eventual 2 StatedBot0 DupocBot (some (.C, .C)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_DupocBot

theorem s0_vs_OBot : OutcomeSpec .eventual 5 StatedBot0 (fun _ => OBot) (some (.D, .D)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_OBot

theorem s0_vs_TitForTatBot : OutcomeSpec .eventual 4 StatedBot0 (fun _ => TitForTatBot) (some (.C, .C)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_TitForTatBot

theorem s0_vs_EBot : OutcomeSpec .eventual 5 StatedBot0 (fun _ => EBot) (some (.D, .C)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_EBot

theorem s0_vs_CupodTrollBot : OutcomeSpec .universal 2 StatedBot0 CupodTrollBot (some (.D, .C)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_CupodTrollBot

/-- 2a: the only stated–stated cell. -/
theorem s0_vs_s0 : OutcomeSpec .eventual 2 StatedBot0 StatedBot0 (some (.C, .C)) := by
  rw [statedBot0_is_DupocBot]; exact outcome_DupocBot_vs_DupocBot

end PD.StatedSonnet
