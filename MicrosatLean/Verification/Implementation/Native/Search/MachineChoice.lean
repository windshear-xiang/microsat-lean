import MicrosatLean.Verification.Implementation.Native.Search.MachineInvariant
import MicrosatLean.Verification.Implementation.Native.Search.ChoiceSettlement

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Std.Sat

theorem ChoiceSettlementRunning.invariant {formula : Formula} {after : Machine}
    (facts : ChoiceSettlementRunning formula after) : MachineInvariant formula after := by
  obtain ⟨original, learned, heads, rank, base, history, saved, units, settled⟩ := facts.data
  have begin : BeginEvidence after.solver :=
    Or.inr ⟨facts.choice.nonroot, facts.choice.pending, facts.choice.decisionReason⟩
  refine ⟨original, learned, heads, rank, base, facts.choice.variables, history, saved, units,
    fun _ => facts.choice.cursor, ?_, ?_⟩
  · rw [PhaseInvariant, facts.choice.phase]
    exact ⟨begin, facts.choice.cursor, facts.choice.oldLemmas, facts.choice.root,
      facts.choice.currentLit, facts.choice.previousWatch, settled⟩
  · rw [facts.choice.oldLemmas]
    exact Nat.zero_le _

/-- Actual choice either returns a valid SAT model or saves the completed
watch boundary before its genuine fresh decision and new propagation phase. -/
theorem step_choose_invariant {formula : Formula} {machine : Machine}
    (invariant : MachineInvariant formula machine) (phase : machine.phase = .choose) :
    InvariantProgress formula (step machine) := by
  obtain ⟨original, learned, heads, rank, certificate⟩ := invariant
  rcases machine with ⟨s, decision, current, old, root, lit, previous⟩
  dsimp only at phase
  subst current
  have concrete := certificate.phase
  change s.processed = s.assigned ∧ lit = 0 ∧ previous = 0 ∧ LevelCover s ∧ SixBefore s ∧
    SettledPrefix s (original ++ learned) heads s.processed at concrete
  have settled : SettledWatches s (original ++ learned) heads s.assigned := by
    simpa only [SettledPrefix, SettledWatches, concrete.1] using concrete.2.2.2.2.2
  have cursor : s.nLemmas ≤ old → DecisionCursor s decision := certificate.cursor
  have outcome := step_choose_settlement_outcome s decision old root lit previous certificate.base
    certificate.variables certificate.history concrete.2.2.2.1 concrete.2.2.2.2.1 certificate.saved settled
    certificate.units (fun noLearning => cursor (by omega)) concrete.1
  cases result : step ⟨s, decision, .choose, old, root, lit, previous⟩ with
  | running after =>
    have facts : ChoiceSettlementRunning formula after := by
      simpa only [result, ChoiceSettlementOutcome] using outcome
    simpa only [result, InvariantProgress] using facts.invariant
  | finished answer =>
    simpa only [result, ChoiceSettlementOutcome, InvariantProgress] using outcome

end MicrosatLean.Verification.Implementation.Native.Search
