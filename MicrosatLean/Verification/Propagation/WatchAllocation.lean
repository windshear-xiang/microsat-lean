import MicrosatLean.Verification.Propagation.WatchInvariant
import MicrosatLean.Verification.Representation.ClauseWatches

namespace MicrosatLean.Verification.Propagation

open CDCL Representation

/-- The same head insertion as actual clause allocation, including its width
test. This ghost function never changes the executable solver. -/
def allocatedHeads (s : State) (heads : Nat → List Nat) (lits : Array Lit) : Nat → List Nat :=
  if 1 < lits.size then clauseWatchHeads heads (s.arena.size + 2) lits[0]! lits[1]! else heads

/-- Real `addClause` preserves all finite linked lists and genuine reference
ownership, and installs both slots of the new long clause. No normalization
of old clauses is required; only the newly watched pair must be distinct. -/
theorem WatchCertificate.addClause {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    (lits : Array Lit) (isOriginal : Bool) (arrays : ArrayBounds s)
    (reserved : 2 ≤ s.arena.size) (wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit)
    (distinct : 1 < lits.size → lits[0]! ≠ lits[1]!) :
    WatchCertificate (s.addClause lits isOriginal).1
      ((original ++ learned) ++ [⟨(s.addClause lits isOriginal).2, lits⟩])
      (allocatedHeads s heads lits) := by
  have lists := certificate.watchLists database
  constructor
  · intro lit
    have next := WatchList.links (addClause_watchLists_all (original := isOriginal) heads lists arrays reserved wellFormed distinct lit)
    by_cases wide : 1 < lits.size <;> simpa only [allocatedHeads, wide, ite_true, ite_false] using next
  · intro lit ref member
    by_cases wide : 1 < lits.size
    · simp only [allocatedHeads, wide, ite_true] at member
      rcases clauseWatchHeads_source_head member with old | first | second
      · obtain ⟨entry, stored, id, long⟩ := certificate.references lit ref old
        exact ⟨entry, List.mem_append_left _ stored, id, long⟩
      · refine ⟨⟨(s.addClause lits isOriginal).2, lits⟩, by simp, ?_, ?_⟩
        · simp only [first.1, watchClause, addClause_id]
          omega
        · change 2 ≤ lits.size
          omega
      · refine ⟨⟨(s.addClause lits isOriginal).2, lits⟩, by simp, ?_, ?_⟩
        · simp only [second.1, watchClause, addClause_id]
          omega
        · change 2 ≤ lits.size
          omega
    · simp only [allocatedHeads, wide, ite_false] at member
      obtain ⟨entry, stored, id, long⟩ := certificate.references lit ref member
      exact ⟨entry, List.mem_append_left _ stored, id, long⟩
  · intro entry member wideEntry
    rcases List.mem_append.mp member with old | new
    · have covered := certificate.covered entry old wideEntry
      by_cases wide : 1 < lits.size
      · simpa only [allocatedHeads, wide, ite_true] using
          covered.clauseWatchHeads (s.arena.size + 2) lits[0]! lits[1]!
      · simpa only [allocatedHeads, wide, ite_false] using covered
    · have same : entry = ⟨(s.addClause lits isOriginal).2, lits⟩ := List.mem_singleton.mp new
      subst entry
      change 2 ≤ lits.size at wideEntry
      have wide : 1 < lits.size := by omega
      simpa only [allocatedHeads, wide, ite_true, addClause_id] using
        (addClause_watchLists (original := isOriginal) heads lists arrays reserved wellFormed wide (distinct wide)).2
  · by_cases wide : 1 < lits.size
    · simpa only [allocatedHeads, wide, ite_true] using clauseWatchHeads_unique lists certificate.unique lits[0]! lits[1]!
    · simpa only [allocatedHeads, wide, ite_false] using certificate.unique

end MicrosatLean.Verification.Propagation
