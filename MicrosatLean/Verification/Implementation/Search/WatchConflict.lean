import MicrosatLean.Verification.Implementation.Search.WatchState

namespace MicrosatLean.Verification.Implementation.Search

open CDCL Bridge
private abbrev NEntry := Native.Representation.StoredClause

/-- Root mode makes the entire active trail unconditional. Recording those
roots exposes the genuine false clause required by the readable UNSAT gate. -/
theorem root_conflict_trace {formula : Formula} {s : State}
    {original learned : List NEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate (formulaView formula) s original learned heads rank)
    (roots : ∀ i, i < s.assigned → s.mark s.trail[i]! = 6)
    {entry : NEntry} (stored : entry ∈ original ++ learned)
    (falseClause : ∀ lit ∈ entry.lits, s.mark lit ≠ 0) (stats : Stats) :
    ∃ after, LogicalExecution (formulaView formula) (nativeState s original learned) after ∧
      Terminal formula after (.unsat stats) := by
  obtain ⟨order, ordered⟩ := base.order
  let machine : Machine := ⟨s, 0, .watch, 0, true, 0, 0⟩
  let before := nativeState s original learned
  have rep : Rep machine before (nativeWitness original learned heads order) := native_rep base ordered
  let after := { before with rootSize := s.assigned }
  refine ⟨after, Logic.single_move (.commitRoots before s.assigned ?_ ?_ ?_), ?_⟩
  · exact Nat.le_trans base.bounds.forcedProcessed base.bounds.processedAssigned
  · simp only [before, nativeState, nativeTrail_length, Nat.le_refl]
  · intro lit member valuation model
    obtain ⟨i, bound, equal⟩ := (prefix_mem_iff
      (by simp only [before, nativeState, nativeTrail_length, Nat.le_refl]) lit).mp member
    have falseValue := base.roots s.trail[i]! ⟨i, bound, rfl⟩ (roots i bound) valuation model
    rw [← equal, rep.trail i bound]
    exact native_true_of_falsifies valuation _ falseValue
  · refine ⟨by simp only [after, before, nativeState, nativeTrail_length], entry.view, ?_, ?_⟩
    · change entry.view ∈ before.database
      rw [nativeState_database]
      exact List.mem_map.mpr ⟨entry, stored, rfl⟩
    · intro lit member
      obtain ⟨encoded, contained, equal⟩ := MicrosatLean.Verification.clauseView_mem.mp member
      rw [← equal]
      have falseBefore := (falseBefore_iff rep (Nat.le_refl s.assigned) encoded).mpr
        (base.marked encoded (falseClause encoded contained))
      have whole : (nativeTrail s (original ++ learned)).take s.assigned =
          nativeTrail s (original ++ learned) :=
        List.take_of_length_le (by simp only [nativeTrail_length, Nat.le_refl])
      simpa only [FalseBefore, prefixLiterals, before, nativeState, nativeTrail_length, List.take_length,
        after, LogicalState.trueTrail, whole] using falseBefore

end MicrosatLean.Verification.Implementation.Search
