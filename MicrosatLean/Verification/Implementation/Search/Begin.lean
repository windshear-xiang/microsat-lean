import MicrosatLean.Verification.Contracts
import MicrosatLean.Verification.Implementation.Bridge.Identity

namespace MicrosatLean.Verification.Implementation.Search

/-!
Beginning propagation changes only machine bookkeeping. Initial root units
select root mode; a fresh reason-free decision selects nonroot mode. The
unconditional entry cursor is reused after resetting the old learned count.
-/

private theorem begin_mode {m : CDCL.Machine} {a : LogicalState}
    (rep : Rep m a w) (evidence : BeginEvidence m a) :
    NextMode { m with
      phase := .nextLiteral
      oldLemmas := m.solver.nLemmas
      root := m.solver.processed < m.solver.assigned &&
        m.solver.reason m.solver.trail[m.solver.processed]! != 0
      currentLit := 0
      previousWatch := 0 } a := by
  rcases evidence with ⟨processed, forced, roots⟩ | ⟨nonroot, _, decision⟩
  · constructor
    · intro _ i before
      exact (roots i before).1
    · intro falseRoot
      apply Or.inl
      have empty : m.solver.assigned = 0 := by
        by_cases empty : m.solver.assigned = 0
        · exact empty
        · have positive : 0 < m.solver.assigned := by omega
          have reason := (roots 0 positive).2
          change (m.solver.processed < m.solver.assigned &&
            m.solver.reason m.solver.trail[m.solver.processed]! != 0) = false at falseRoot
          simp [processed, positive, reason] at falseRoot
      rw [rep.trailLength, rep.rootSize, empty, forced]
  · have falseGuard : (m.solver.processed < m.solver.assigned &&
        m.solver.reason m.solver.trail[m.solver.processed]! != 0) = false := by simp [decision]
    constructor
    · intro trueRoot
      change (m.solver.processed < m.solver.assigned &&
        m.solver.reason m.solver.trail[m.solver.processed]! != 0) = true at trueRoot
      rw [falseGuard] at trueRoot
      cases trueRoot
    · intro _
      exact Or.inr nonroot

theorem begin_propagation : PhaseCorrect .beginPropagation := by
  intro formula machine a w certificate phase
  rcases machine with ⟨s, decision, current, old, root, lit, previous⟩
  dsimp only at phase
  subst current
  have before := certificate.control.phase
  change BeginEvidence _ a ∧ DecisionCursor a w decision ∧ _ at before
  let after : CDCL.Machine := ⟨s, decision, .nextLiteral, s.nLemmas,
    s.processed < s.assigned && s.reason s.trail[s.processed]! != 0, 0, 0⟩
  change RunningPost formula a after
  refine ⟨a, w, Bridge.rep_frame_solver
      (before := ⟨s, decision, .beginPropagation, old, root, lit, previous⟩)
      (after := after) rfl certificate.representation, certificate.variables,
    LogicalExecution.refl a, ?_, certificate.progress⟩
  refine ⟨certificate.control.history, certificate.control.saved, certificate.control.units,
    fun _ => before.2.1, Nat.le_refl _, certificate.control.tags,
    certificate.control.rootTags, certificate.control.rootPrefix, ?_⟩
  exact ⟨begin_mode certificate.representation before.1, rfl, rfl, before.2.2.2.2.2.2⟩

end MicrosatLean.Verification.Implementation.Search
