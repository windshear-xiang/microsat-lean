import MicrosatLean.Verification.Implementation.Search.ChooseDecision
import MicrosatLean.Verification.Contracts
import MicrosatLean.Verification.Implementation.Search.ChoosePrepare
import MicrosatLean.Verification.Implementation.Bridge.ToConcrete
import MicrosatLean.Verification.Implementation.Search.Concrete.MachineChoice

namespace MicrosatLean.Verification.Implementation.Search

open Bridge

/-- The SAT gate is derived at the completed prepared boundary: the actual
cursor covers every variable and saved phases agree with the current trail. -/
theorem choose_sat_gate {formula : Formula} {m : CDCL.Machine}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    (variables : formula.numVars ≤ m.solver.nVars)
    (closed : Analysis.PropagationClosed m.solver (original ++ learned))
    {cursor : Nat} (covered : Search.Concrete.DecisionCursor m.solver cursor)
    (finished : CDCL.nextDecision m.solver cursor = 0) :
    Terminal formula (logicalView m.solver original learned) (.sat m.solver.phases m.solver.stats) := by
  obtain ⟨order, ordered⟩ := base.order
  have represented := view_rep base ordered
  refine ⟨?_, ?_, ?_, closed_of_concrete base closed⟩
  · change formula.numVars < m.solver.phases.size
    rw [base.arrays.phasesSize]
    omega
  · intro lit member
    have declared := (view_semantic base ordered).declaredTrail lit member
    have phaseBound : lit.1 < m.solver.phases.size := by
      rw [base.arrays.phasesSize]
      change 0 < lit.1 ∧ lit.1 ≤ m.solver.nVars at declared
      omega
    obtain ⟨entry, contained, equal⟩ := List.mem_map.mp member
    obtain ⟨i, before, value⟩ := List.mem_iff_getElem.mp contained
    have get : (logicalView m.solver original learned).trail[i]! = entry := by
      rw [getElem!_pos _ i before]
      exact value
    have saved := represented.phases i before
    rw [get, equal] at saved
    change assignment m.solver.phases lit.1 = lit.2
    rw [assignment_eq_getElem _ phaseBound]
    simpa only [getElem!_pos m.solver.phases lit.1 phaseBound] using saved
  · intro var lower upper
    exact view_assigned base ordered (covered.zero_all_assigned finished var lower upper)

end MicrosatLean.Verification.Implementation.Search

namespace MicrosatLean.Verification.Implementation.Search

open Bridge

/-- Actual choice refines optional restart and forgetting followed by one
fresh decision, or reaches the complete propagated SAT boundary. -/
theorem choose : PhaseCorrect .choose := by
  intro formula machine a w certificate phase
  rcases machine with ⟨s, decision, current, old, root, lit, previous⟩
  dsimp only at phase
  subst current
  have concrete := machineCertificate_concrete certificate
  have facts := concrete.phase
  change s.processed = s.assigned ∧ lit = 0 ∧ previous = 0 ∧
    Analysis.LevelCover s ∧ Analysis.SixBefore s ∧
    Propagation.SettledPrefix s _ w.heads s.processed at facts
  have settled : Propagation.SettledWatches s
      (w.original ++ w.learned) w.heads s.assigned := by
    simpa only [Propagation.SettledPrefix, Propagation.SettledWatches, facts.1]
      using facts.2.2.2.2.2
  have closed := Propagation.prefixUnitClosed_of_settled concrete.base.active (Nat.le_refl _)
    concrete.base.watches concrete.base.nonempty concrete.units settled
  obtain ⟨nextLearned, nextHeads, preparedData⟩ := concrete.base.prepareChoice_settlement
    concrete.history facts.2.2.2.1 facts.2.2.2.2.1 closed concrete.saved settled concrete.units decision old
  let prepared := Search.Concrete.prepareChoice s decision old
  have nextCursor : Search.Concrete.DecisionCursor prepared.1 prepared.2 :=
    Search.Concrete.prepareChoice_decisionCursor decision old concrete.base.order
      (fun none => concrete.cursor (by change s.nLemmas ≤ old; omega))
  obtain ⟨traceLearned, traceHeads, traceBase, trace⟩ := prepare_execution concrete.base decision old
  have sameLearned := (traceBase.database.unique preparedData.certificate.database).2
  subst traceLearned
  obtain ⟨order, ordered⟩ := concrete.base.order
  have initialEq := rep_unique certificate.representation
    (view_rep (m := ⟨s, decision, .choose, old, root, lit, previous⟩) concrete.base ordered)
  rw [← initialEq] at trace
  rw [Search.Concrete.step_choose_eq]
  change (match (if CDCL.nextDecision prepared.1 prepared.2 == 0 then
      CDCL.Progress.finished (.sat prepared.1.phases prepared.1.stats)
    else CDCL.Progress.running ⟨prepared.1.decide (CDCL.nextDecision prepared.1 prepared.2),
      CDCL.nextDecision prepared.1 prepared.2, .beginPropagation, 0, false, 0, 0⟩) with
    | .running after => RunningPost formula a after
    | .finished result => FinishedPost formula a result)
  by_cases zero : CDCL.nextDecision prepared.1 prepared.2 = 0
  · simp only [zero, beq_self_eq_true, ite_true]
    refine ⟨logicalView prepared.1 _ nextLearned, trace, ?_⟩
    apply choose_sat_gate (m := ⟨prepared.1, prepared.2, .choose, old, root, 0, 0⟩)
      preparedData.certificate _ preparedData.closed nextCursor zero
    simpa only [prepared, Search.Concrete.prepareChoice_nVars] using concrete.variables
  · simp only [beq_iff_eq, zero, ite_false]
    let selected := CDCL.nextDecision prepared.1 prepared.2
    let after : CDCL.Machine := ⟨prepared.1.decide selected, selected, .beginPropagation, 0, false, 0, 0⟩
    have unset : Search.Concrete.UnassignedVariable prepared.1 selected :=
      Search.Concrete.nextDecisionScan_nonzero_unassigned (prepared.1.nVars + 1) prepared.1 prepared.2 zero
    have declared : 1 ≤ selected ∧ selected ≤ prepared.1.nVars := by
      rcases (nextCursor.advance zero).declared_or_zero with equal | bounds
      · exact False.elim (zero equal)
      · exact bounds
    have decisionTrace := decision_execution
      (m := ⟨prepared.1, prepared.2, .choose, old, root, 0, 0⟩)
      preparedData.certificate preparedData.closed declared.1 declared.2 unset
    have execution := Logic.execution_trans trace decisionTrace
    have afterNative : Search.Concrete.MachineInvariant formula after := by
      have outcome := Search.Concrete.step_choose_invariant (concrete_of_certificate certificate) rfl
      rw [Search.Concrete.step_choose_eq] at outcome
      simpa only [prepared, beq_iff_eq, zero, ite_false, Search.Concrete.InvariantProgress,
        after, selected] using outcome
    have afterVariables : after.solver.nVars = max 1 formula.numVars := by
      change prepared.1.nVars = max 1 formula.numVars
      rw [Search.Concrete.prepareChoice_nVars]
      exact certificate.representation.variables.symm.trans certificate.variables
    obtain ⟨next, witness, afterCertificate⟩ :=
      of_concrete certificate.input afterNative afterVariables
    have afterBase := preparedData.certificate.nextDecision prepared.2 nextCursor.declared_or_zero zero
    obtain ⟨afterOrder, afterOrdered⟩ := afterBase.order
    have finalEq := rep_unique
      (view_rep (m := after) afterBase afterOrdered) afterCertificate.representation
    rw [finalEq] at execution
    exact ⟨next, witness, afterCertificate.representation, afterCertificate.variables,
      execution, afterCertificate.control, afterCertificate.progress⟩

end MicrosatLean.Verification.Implementation.Search
