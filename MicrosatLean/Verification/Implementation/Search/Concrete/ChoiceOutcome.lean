import MicrosatLean.Verification.Implementation.Search.Concrete.Decision
import MicrosatLean.Verification.Implementation.Representation.Assignment
import MicrosatLean.Verification.Implementation.Representation.Semantics
import MicrosatLean.Verification.Implementation.Search.Concrete.ChoiceState
import MicrosatLean.Verification.Implementation.Search.Concrete.DecisionCursor
import MicrosatLean.Verification.Implementation.Search.Concrete.Assignment
import MicrosatLean.Verification.Implementation.Search.Concrete.AnalysisEntry
import MicrosatLean.Verification.Implementation.Propagation.WatchSettled

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation
open Std.Sat

/-- Writing a decision reason yields zero even if the slot is out of bounds:
the logical total array access then has its zero default. Reachable states
separately establish all executable accesses are within their allocated arrays. -/
theorem decide_reason_at_decision (s : State) (var : Nat) :
    (s.decide var).reason (decisionLiteral s var).negate = 0 := by
  change (s.reasons.set! var 0)[(decisionLiteral s var).negate.var]! = 0
  rw [negate_var, decisionLiteral_var]
  by_cases bound : var < s.reasons.size
  · exact Array.getElem!_set!_self s.reasons var 0 bound
  · simp [Array.setIfInBounds, bound]

end MicrosatLean.Verification.Implementation.Search.Concrete

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Analysis Reduction Std.Sat

private theorem prepareChoice_orderFrame (s : State) (cursor old : Nat) :
    (prepareChoice s cursor old).1.nVars = s.nVars ∧
      (prepareChoice s cursor old).1.head = s.head ∧
      (prepareChoice s cursor old).1.previous = s.previous ∧
      (prepareChoice s cursor old).1.next = s.next := by
  simp only [prepareChoice, Id.run, pure]
  split
  · split
    · split
      · have frame := reduceDB_restore
          ({ s with res := 0, fast := s.slow / 100 * 125 }.restart)
          ({ s with res := 0, fast := s.slow / 100 * 125 }.restart.config.reductionK)
        exact ⟨(by simpa only [restart_nVars] using congrArg State.nVars frame),
          (by simpa only [restart_head] using congrArg State.head frame),
          (by simpa only [restart_previous] using congrArg State.previous frame),
          (by simpa only [restart_next] using congrArg State.next frame)⟩
      · exact ⟨restart_nVars, restart_head, restart_previous, restart_next⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  · exact ⟨rfl, rfl, rfl, rfl⟩

theorem prepareChoice_nVars (s : State) (cursor old : Nat) :
    (prepareChoice s cursor old).1.nVars = s.nVars := (prepareChoice_orderFrame s cursor old).1

theorem prepareChoice_head (s : State) (cursor old : Nat) :
    (prepareChoice s cursor old).1.head = s.head := (prepareChoice_orderFrame s cursor old).2.1

theorem prepareChoice_cursor (s : State) (cursor old : Nat) :
    (prepareChoice s cursor old).2 = if s.nLemmas > old then s.head else cursor := by
  simp only [prepareChoice, Id.run, pure]
  split
  · split
    · split <;> rfl
    · rfl
  · rfl

/-- Learning resets the real scan cursor to the unchanged MTF head. With no
learning the state and old cursor are retained together. -/
theorem prepareChoice_decisionCursor {s : State} (cursor old : Nat) (coverage : MTFCoverage s)
    (covered : ¬s.nLemmas > old → DecisionCursor s cursor) :
    DecisionCursor (prepareChoice s cursor old).1 (prepareChoice s cursor old).2 := by
  by_cases learning : s.nLemmas > old
  · have coverage : MTFCoverage (prepareChoice s cursor old).1 := by
      obtain ⟨order, valid⟩ := coverage
      have frame := prepareChoice_orderFrame s cursor old
      exact ⟨order, valid.frame frame.1 frame.2.1 frame.2.2.1 frame.2.2.2⟩
    have head := DecisionCursor.head coverage
    simpa only [prepareChoice_cursor, learning, ite_true, prepareChoice_head] using head
  · rw [prepareChoice_no_learning s cursor old learning]
    exact covered learning

/-- Restart sets both propagation cursors to the forced boundary, and real
reduction preserves them. Thus actual choice preparation retains quiescence. -/
theorem prepareChoice_quiescent {s : State} (bounds : TrailBounds s)
    (quiet : s.processed = s.assigned) (cursor old : Nat) :
    (prepareChoice s cursor old).1.processed = (prepareChoice s cursor old).1.assigned := by
  have resetBounds : TrailBounds { s with res := 0, fast := s.slow / 100 * 125 } :=
    ⟨bounds.forcedProcessed, bounds.processedAssigned, bounds.assignedVars⟩
  simp only [prepareChoice, Id.run, pure]
  split
  · split
    · split
      · rw [reduceDB_processed, reduceDB_assigned, restart_processed, restart_assigned resetBounds]
      · rw [restart_processed, restart_assigned resetBounds]
    · exact quiet
  · exact quiet

/-- A genuine choice return starts exactly one pending, reason-free decision.
The shared database witness carries its saved decision history; cursor and
nonroot phase data are ready for the subsequent propagation invocation. -/
structure ChoiceRunning (formula : Formula) (after : Machine) : Prop where
  data : ∃ original learned heads rank,
    StateCertificate (formulaView formula) after.solver original learned heads rank ∧
      DecisionHistory after.solver (original ++ learned)
  variables : formula.numVars ≤ after.solver.nVars
  nonroot : NonrootPhase after.solver
  cursor : DecisionCursor after.solver after.decision
  phase : after.phase = .beginPropagation
  oldLemmas : after.oldLemmas = 0
  root : after.root = false
  currentLit : after.currentLit = 0
  previousWatch : after.previousWatch = 0
  pending : after.solver.processed + 1 = after.solver.assigned
  decisionReason : after.solver.reason after.solver.trail[after.solver.processed]! = 0

def ChoiceOutcome (formula : Formula) : Progress → Prop
  | .running after => ChoiceRunning formula after
  | .finished result => ValidResult formula result

/-- Full actual `.choose` semantics. The zero branch proves the saved model
valid from real propagation closure and cursor coverage. The nonzero branch
derives fresh capacity, a complete new state certificate, saved decision
closure, nonroot phase and the pending decision's actual zero reason. -/
theorem step_choose_outcome {formula : Formula} (s : State) (cursor old : Nat)
    (root : Bool) (lit previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate (formulaView formula) s original learned heads rank)
    (variables : formula.numVars ≤ s.nVars) (history : DecisionHistory s (original ++ learned))
    (levels : LevelCover s) (six : SixBefore s) (closed : PropagationClosed s (original ++ learned))
    (covered : ¬s.nLemmas > old → DecisionCursor s cursor) (quiet : s.processed = s.assigned) :
    ChoiceOutcome formula (step ⟨s, cursor, .choose, old, root, lit, previous⟩) := by
  obtain ⟨nextLearned, nextHeads, nextCertificate, nextHistory, nextLevels, nextSix, nextClosed⟩ :=
    certificate.prepareChoice history levels six closed cursor old
  let prepared := prepareChoice s cursor old
  have nextCursor : DecisionCursor prepared.1 prepared.2 :=
    prepareChoice_decisionCursor cursor old certificate.order covered
  have nextQuiet : prepared.1.processed = prepared.1.assigned :=
    prepareChoice_quiescent certificate.bounds quiet cursor old
  have nextVariables : formula.numVars ≤ prepared.1.nVars := by
    simpa only [prepared, prepareChoice_nVars] using variables
  rw [step_choose_eq]
  change ChoiceOutcome formula (if nextDecision prepared.1 prepared.2 == 0 then
    .finished (.sat prepared.1.phases prepared.1.stats) else
    .running ⟨prepared.1.decide (nextDecision prepared.1 prepared.2), nextDecision prepared.1 prepared.2,
      .beginPropagation, 0, false, 0, 0⟩)
  by_cases zero : nextDecision prepared.1 prepared.2 = 0
  · simp only [zero, beq_self_eq_true, ite_true, ChoiceOutcome]
    exact validResult_sat_of_decisionCursor nextVariables nextCertificate.arrays nextCertificate.marked
      nextCertificate.phases nextCertificate.database nextCertificate.meaning
      (databaseNoConflict_of_prefixUnitClosed nextCertificate.active nextCertificate.marked
        nextCertificate.nonempty nextClosed) nextCursor zero
  · simp only [beq_iff_eq, zero, ite_false, ChoiceOutcome]
    let selected := nextDecision prepared.1 prepared.2
    have unset : UnassignedVariable prepared.1 selected :=
      nextDecisionScan_nonzero_unassigned (prepared.1.nVars + 1) prepared.1 prepared.2 zero
    have declared : 1 ≤ selected ∧ selected ≤ prepared.1.nVars := by
      rcases (nextCursor.advance zero).declared_or_zero with equal | bounded
      · exact False.elim (zero equal)
      · exact bounded
    have fresh := freshVariable_of_unmarked nextCertificate.active unset.1 unset.2
    have room : prepared.1.assigned < prepared.1.nVars :=
      assigned_lt_of_fresh nextCertificate.active nextCertificate.distinct fresh declared.1 declared.2
    have space : prepared.1.assigned < prepared.1.trail.size := by
      have size : prepared.1.trail.size = prepared.1.nVars + 1 := nextCertificate.arrays.trailSize
      rw [size]
      omega
    have reasonBound : selected < prepared.1.reasons.size := (nextCertificate.arrays.variable_index declared.2).1
    have literal := decisionLiteral_bound (s := prepared.1) declared.1 declared.2
    refine ⟨?_, nextVariables, ?_, nextCursor.choose zero, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
    · exact ⟨original, nextLearned, nextHeads, extendTrailRank rank selected prepared.1.assigned,
        nextCertificate.nextDecision prepared.2 nextCursor.declared_or_zero zero,
        nextHistory.decide nextClosed selected fresh⟩
    · exact nonrootPhase_decide nextLevels nextSix selected
        (Nat.le_trans nextCertificate.bounds.forcedProcessed nextCertificate.bounds.processedAssigned)
        space reasonBound (nextCertificate.arrays.literal_index literal.negate).1 fresh
    · change prepared.1.processed + 1 = prepared.1.assigned + 1
      rw [nextQuiet]
    · change (prepared.1.decide selected).reason (prepared.1.decide selected).trail[prepared.1.processed]! = 0
      rw [nextQuiet, decide_trail_last space, decide_reason_at_decision]

end MicrosatLean.Verification.Implementation.Search.Concrete
