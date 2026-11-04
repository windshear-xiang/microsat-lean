import MicrosatLean.Verification.Implementation.Propagation.WatchReasons
import MicrosatLean.Verification.Implementation.Propagation.WatchRetention

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL Representation Analysis Std.Sat

/-- A false current watch cannot be the true head of an active reason.
Consequently a retained active reason keeps its original literal order. -/
theorem retainWatch_reasonGraph {s : State} {formula : Std.Sat.CNF Nat} {rank : Lit → Nat}
    {original learned : List StoredClause} (database : Database s original learned)
    (graph : ReasonGraph formula s s.assigned rank) (active : ActiveTrail s)
    (proper : ReasonDatabase s (original ++ learned))
    {entry : StoredClause} (member : entry ∈ original ++ learned) (wide : 2 ≤ entry.lits.size)
    (lit : Lit) (falseLit : s.mark lit ≠ 0)
    (watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit) :
    ReasonGraph formula { s with arena := retainWatch s.arena entry.id lit } s.assigned rank := by
  let f := retainWatchEntry entry.id (s.db entry.id == lit)
  let after := { s with arena := retainWatch s.arena entry.id lit }
  have nextDatabase := retainWatch_database database member lit wide watched
  refine ⟨graph.countBound, graph.ranks, graph.distinctVariables, ?_⟩
  intro i before nondecision
  obtain ⟨lits, packed, nonempty, head, entailed, tails⟩ := graph.clauses i before nondecision
  obtain ⟨reasonEntry, reasonMember, reasonId⟩ := proper i before nondecision
  have unchanged : f reasonEntry = reasonEntry := by
    by_cases different : reasonEntry.id ≠ entry.id
    · exact retainWatchEntry_of_ne _ _ _ different
    · have same : reasonEntry.id = entry.id := by simpa using different
      have reason : s.reason s.trail[i]! = entry.id := reasonId.trans same
      have first : s.db entry.id = s.trail[i]!.negate := by
        have read := packed.literals 0 nonempty
        simpa only [reason, Nat.add_zero, head] using read
      have unmarked : s.mark (s.db entry.id) = 0 := by
        rw [first]
        exact (active i before).2.2
      have notFirst : s.db entry.id ≠ lit :=
        fun equal => falseLit ((congrArg s.mark equal).symm.trans unmarked)
      have test : (s.db entry.id == lit) = false := by simp [notFirst]
      simp only [f, test, retainWatchEntry_false]
  have mapped : reasonEntry ∈ original.map f ++ learned.map f := by
    rw [← List.map_append]
    exact List.mem_map.mpr ⟨reasonEntry, reasonMember, unchanged⟩
  have oldPacked : PackedClause s (s.reason s.trail[i]!) reasonEntry.lits := by
    simpa only [reasonId] using database.layout.packed reasonMember
  have sameLits := oldPacked.unique packed
  have newPacked : PackedClause after (after.reason after.trail[i]!) lits := by
    change PackedClause after (s.reason s.trail[i]!) lits
    rw [reasonId]
    simpa only [sameLits] using nextDatabase.layout.packed mapped
  exact ⟨lits, newPacked, nonempty, head, entailed, tails⟩

end MicrosatLean.Verification.Implementation.Propagation
