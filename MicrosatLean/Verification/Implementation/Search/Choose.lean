import MicrosatLean.Verification.Contracts
import MicrosatLean.Verification.Implementation.Search.ChoosePrepare
import MicrosatLean.Verification.Implementation.Search.ChooseTerminal
import MicrosatLean.Verification.Implementation.Bridge.ToNative
import MicrosatLean.Verification.Implementation.Native.Search.MachineChoice

namespace MicrosatLean.Verification.Implementation.Search

open Bridge

/-- Actual choice refines optional restart and forgetting followed by one
fresh decision, or reaches the complete propagated SAT boundary. -/
theorem choose : PhaseCorrect .choose := by
  intro formula machine a w certificate phase
  rcases machine with ⟨s, decision, current, old, root, lit, previous⟩
  dsimp only at phase
  subst current
  have native := machineCertificate_toNative certificate
  have facts := native.phase
  change s.processed = s.assigned ∧ lit = 0 ∧ previous = 0 ∧
    Native.Analysis.LevelCover s ∧ Native.Analysis.SixBefore s ∧
    Native.Propagation.SettledPrefix s _ w.heads s.processed at facts
  have settled : Native.Propagation.SettledWatches s
      (w.original ++ w.learned) w.heads s.assigned := by
    simpa only [Native.Propagation.SettledPrefix, Native.Propagation.SettledWatches, facts.1]
      using facts.2.2.2.2.2
  have closed := Native.Propagation.prefixUnitClosed_of_settled native.base.active (Nat.le_refl _)
    native.base.watches native.base.nonempty native.units settled
  obtain ⟨nextLearned, nextHeads, preparedData⟩ := native.base.prepareChoice_settlement
    native.history facts.2.2.2.1 facts.2.2.2.2.1 closed native.saved settled native.units decision old
  let prepared := Native.Search.prepareChoice s decision old
  have nextCursor : Native.Search.DecisionCursor prepared.1 prepared.2 :=
    Native.Search.prepareChoice_decisionCursor decision old native.base.order
      (fun none => native.cursor (by change s.nLemmas ≤ old; omega))
  obtain ⟨traceLearned, traceHeads, traceBase, trace⟩ := prepare_execution native.base decision old
  have sameLearned := (traceBase.database.unique preparedData.certificate.database).2
  subst traceLearned
  obtain ⟨order, ordered⟩ := native.base.order
  have initialEq := rep_unique certificate.representation
    (native_rep (m := ⟨s, decision, .choose, old, root, lit, previous⟩) native.base ordered)
  rw [← initialEq] at trace
  rw [Native.Search.step_choose_eq]
  change (match (if CDCL.nextDecision prepared.1 prepared.2 == 0 then
      CDCL.Progress.finished (.sat prepared.1.phases prepared.1.stats)
    else CDCL.Progress.running ⟨prepared.1.decide (CDCL.nextDecision prepared.1 prepared.2),
      CDCL.nextDecision prepared.1 prepared.2, .beginPropagation, 0, false, 0, 0⟩) with
    | .running after => RunningPost formula a after
    | .finished result => FinishedPost formula a result)
  by_cases zero : CDCL.nextDecision prepared.1 prepared.2 = 0
  · simp only [zero, beq_self_eq_true, ite_true]
    refine ⟨nativeState prepared.1 _ nextLearned, trace, ?_⟩
    apply choose_sat_gate (m := ⟨prepared.1, prepared.2, .choose, old, root, 0, 0⟩)
      preparedData.certificate _ preparedData.closed nextCursor zero
    simpa only [prepared, Native.Search.prepareChoice_nVars] using native.variables
  · simp only [beq_iff_eq, zero, ite_false]
    let selected := CDCL.nextDecision prepared.1 prepared.2
    let after : CDCL.Machine := ⟨prepared.1.decide selected, selected, .beginPropagation, 0, false, 0, 0⟩
    have unset : Native.Search.UnassignedVariable prepared.1 selected :=
      Native.Search.nextDecisionScan_nonzero_unassigned (prepared.1.nVars + 1) prepared.1 prepared.2 zero
    have declared : 1 ≤ selected ∧ selected ≤ prepared.1.nVars := by
      rcases (nextCursor.advance zero).declared_or_zero with equal | bounds
      · exact False.elim (zero equal)
      · exact bounds
    have decisionTrace := decision_execution
      (m := ⟨prepared.1, prepared.2, .choose, old, root, 0, 0⟩)
      preparedData.certificate preparedData.closed declared.1 declared.2 unset
    have execution := Logic.execution_trans trace decisionTrace
    have afterNative : Native.Search.MachineInvariant formula after := by
      have outcome := Native.Search.step_choose_invariant (native_of_certificate certificate) rfl
      rw [Native.Search.step_choose_eq] at outcome
      simpa only [prepared, beq_iff_eq, zero, ite_false, Native.Search.InvariantProgress,
        after, selected] using outcome
    have afterVariables : after.solver.nVars = max 1 formula.numVars := by
      change prepared.1.nVars = max 1 formula.numVars
      rw [Native.Search.prepareChoice_nVars]
      exact certificate.representation.variables.symm.trans certificate.variables
    obtain ⟨next, witness, afterCertificate⟩ :=
      from_native certificate.input afterNative afterVariables
    have afterBase := preparedData.certificate.nextDecision prepared.2 nextCursor.declared_or_zero zero
    obtain ⟨afterOrder, afterOrdered⟩ := afterBase.order
    have finalEq := rep_unique
      (native_rep (m := after) afterBase afterOrdered) afterCertificate.representation
    rw [finalEq] at execution
    exact ⟨next, witness, afterCertificate.representation, afterCertificate.variables,
      execution, afterCertificate.control, afterCertificate.progress⟩

end MicrosatLean.Verification.Implementation.Search
