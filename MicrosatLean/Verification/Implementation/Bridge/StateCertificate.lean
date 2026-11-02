import MicrosatLean.Verification.Implementation.Bridge.Reasons

namespace MicrosatLean.Verification.Implementation.Bridge

theorem entry_nonempty {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w)
    {entry : StoredClause} (member : entry ∈ w.entries) : 0 < entry.lits.size := by
  have nonempty := certificate.semantic.nonempty entry.view
    (stored_view_mem certificate.representation member)
  by_cases positive : 0 < entry.lits.size
  · exact positive
  · have zero : entry.lits.size = 0 := by omega
    have empty : entry.lits = #[] := Array.eq_empty_of_size_eq_zero zero
    simp [Representation.StoredClause.view, empty] at nonempty

theorem falsifies_of_negated_view (lit : Lit) (valuation : Assignment)
    (truth : valuation (literalView lit).negate.1 = (literalView lit).negate.2) :
    Representation.Falsifies valuation lit := by
  change valuation (literalView lit).1 = !(literalView lit).2 at truth
  change valuation (literalView lit).1 ≠ (literalView lit).2
  intro equal
  rw [equal] at truth
  cases polarity : (literalView lit).2 <;> simp_all

theorem stateCertificate_concrete {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Search.Concrete.StateCertificate (formulaView formula) m.solver
      w.original w.learned w.heads (trailRank m.solver) := by
  have represented := certificate.representation
  refine ⟨represented.arrays,
    ⟨represented.cursors.1, represented.cursors.2.1, represented.cursors.2.2⟩,
    active_concrete certificate, distinct_concrete certificate, phases_concrete represented,
    (fun lit marked => (represented.marks lit).mp marked),
    ⟨w.order, represented.order⟩, database_concrete represented,
    ?_, reasonDatabase_concrete represented, graph_concrete certificate,
    represented.watches, ?_, ?_, ?_, learnedDistinct_concrete certificate,
    ?_, ?_, certificate.control.rootPrefix⟩
  · constructor
    · rw [mapped_databaseView, ← represented.original]
      exact certificate.semantic.original
    · rw [mapped_databaseView, ← represented.learned]
      exact certificate.semantic.learned
  · intro entry member
    exact entry_nonempty certificate member
  · intro entry member
    exact (normalized_concrete certificate member).1
  · intro entry member
    exact (normalized_concrete certificate member).2
  · intro lit member
    obtain ⟨i, before, rfl⟩ := member
    exact Or.inr (certificate.control.tags i before)
  · intro lit member six valuation model
    obtain ⟨i, before, rfl⟩ := member
    have active : i < a.trail.length := by simpa only [represented.trailLength] using before
    have truth := certificate.control.rootTags i active six valuation model
    rw [represented.trail i before] at truth
    exact falsifies_of_negated_view _ _ truth

end MicrosatLean.Verification.Implementation.Bridge
