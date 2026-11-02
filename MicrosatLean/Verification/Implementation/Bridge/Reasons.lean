import MicrosatLean.Verification.Implementation.Bridge.TrailData

namespace MicrosatLean.Verification.Implementation.Bridge

/-- The existing concrete reason graph only needs the unique active position. -/
def trailRank (s : CDCL.State) (lit : Lit) : Nat :=
  (List.range s.assigned).findIdx (fun i => s.trail[i]! == lit)

theorem trailRank_at {s : CDCL.State} (distinct : Representation.DistinctTrailVariables s)
    {i : Nat} (before : i < s.assigned) : trailRank s s.trail[i]! = i := by
  apply (List.findIdx_eq (by simpa only [List.length_range] using before)).mpr
  constructor
  · simp
  · intro j earlier
    simp only [List.getElem_range, beq_eq_false_iff_ne]
    intro same
    have equal := distinct j i (Nat.lt_trans earlier before) before (congrArg Lit.var same)
    omega

theorem encoded_head {lits : Array Lit} {lit : Literal}
    (head : (clauseView lits).literals.head? = some lit) :
    0 < lits.size ∧ literalView lits[0]! = lit := by
  have positive : 0 < lits.size := by
    by_cases positive : 0 < lits.size
    · exact positive
    · have size : lits.size = 0 := by omega
      have words : lits = #[] := Array.eq_empty_of_size_eq_zero size
      simp [words] at head
  refine ⟨positive, ?_⟩
  have first : (clauseView lits).literals.head? = some (literalView lits[0]!) := by
    simp [clauseView_literals, List.head?_eq_getElem?, positive]
  exact Option.some.inj (first.symm.trans head)

theorem encoded_tail {lits : Array Lit} {j : Nat} (positive : 0 < j) (before : j < lits.size) :
    literalView lits[j]! ∈ (clauseView lits).literals.tail := by
  rw [clauseView_literals, ← List.map_tail]
  apply List.mem_map.mpr
  refine ⟨lits[j], ?_, by simp [getElem!_pos lits j before]⟩
  apply List.mem_iff_getElem.mpr
  refine ⟨j - 1, ?_, ?_⟩
  · simp only [List.length_tail, Array.length_toList]
    omega
  · simp [List.getElem_tail, show j - 1 + 1 = j by omega]

theorem graph_concrete {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Analysis.ReasonGraph (formulaView formula) m.solver m.solver.assigned
      (trailRank m.solver) := by
  have represented := certificate.representation
  refine ⟨?_, fun i before => trailRank_at (distinct_concrete certificate) before,
    distinct_concrete certificate, ?_⟩
  · rw [represented.arrays.trailSize]
    have bounded := represented.cursors.2.2
    omega
  · intro i before nonzero
    have active : i < a.trail.length := by simpa only [represented.trailLength] using before
    cases reason : a.trail[i]!.reason with
    | none => exact False.elim (nonzero ((reason_none_iff represented before).mp reason))
    | some clause =>
      have present := represented.reasons i before
      simp only [reason] at present
      obtain ⟨entry, member, id, view⟩ := present
      have facts := certificate.semantic.reasons i active clause reason
      have head : (clauseView entry.lits).literals.head? = some a.trail[i]!.literal := by
        simpa only [← view, Representation.StoredClause.view] using facts.2.1
      obtain ⟨positive, first⟩ := encoded_head head
      have packed := (database_concrete represented).layout.packed
        (by simpa only [RepresentationWitness.entries] using member)
      refine ⟨entry.lits, ?_, positive, ?_, ?_, ?_⟩
      · simpa only [id] using packed
      · apply literalView_injective
        rw [literalView_negate]
        exact first.trans (represented.trail i before)
      · change Std.Sat.CNF.EntailsClause (formulaView formula) (clauseView entry.lits)
        simpa only [← view, Representation.StoredClause.view] using facts.1
      · intro j positiveJ beforeJ
        have tail := facts.2.2 (literalView entry.lits[j]!)
          (by simpa only [← view, Representation.StoredClause.view] using encoded_tail positiveJ beforeJ)
        exact (falseBefore_iff represented (Nat.le_of_lt before) entry.lits[j]!).mp tail

end MicrosatLean.Verification.Implementation.Bridge
