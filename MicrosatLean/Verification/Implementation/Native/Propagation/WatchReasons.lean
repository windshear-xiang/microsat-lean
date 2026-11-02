import MicrosatLean.Verification.Implementation.Native.Propagation.WatchStep
import MicrosatLean.Verification.Implementation.Native.Analysis.ReasonGraph
import MicrosatLean.Verification.Implementation.Native.Representation.ReasonDatabase

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation Analysis
open Std.Sat

/-- An active reason has false tails, so a successful scan of a genuine long
clause can never select that clause as a replacement target. -/
theorem replacement_not_active_reason {s : State} {formula : CNF Nat} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula s count rank) (active : ActiveTrail s) (countActive : count ≤ s.assigned)
    {id : Nat} {lits : Array Lit} (packed : PackedClause s id lits) (wide : 2 ≤ lits.size)
    (lit : Lit) {pos : Nat} (found : replacement (orientWatch s.arena id lit) s.marks id = some pos)
    (i : Nat) (before : i < count) : s.reason s.trail[i]! ≠ id := by
  intro same
  have nondecision : s.reason s.trail[i]! ≠ 0 := by rw [same]; have := packed.startLower; omega
  obtain ⟨reasonLits, reasonPacked, _, _, _, earlier⟩ := graph.clauses i before nondecision
  rw [same] at reasonPacked
  have unique := reasonPacked.unique packed
  subst reasonLits
  rw [replacement_orientWatch] at found
  obtain ⟨offset, afterWatches, within, _, unmarked⟩ := replacement_some_of_packed packed wide found
  obtain ⟨k, earlierIndex, value⟩ := earlier offset (by omega) within
  have marked := (active k (by omega)).2.1
  exact marked ((congrArg s.mark value).trans unmarked)

/-- Successful actual replacement and header rewiring preserve the complete
reason DAG: active reason IDs are genuine, and the target cannot equal one.
No active reason clause is permitted to be arbitrarily permuted. -/
theorem replacement_branch_reasonGraph {s : State} {formula : CNF Nat} {count : Nat} {rank : Lit → Nat}
    {original learned : List StoredClause} (database : Database s original learned)
    (meaning : DatabaseMeaning formula original learned) (graph : ReasonGraph formula s count rank)
    (active : ActiveTrail s) (countActive : count ≤ s.assigned)
    (storedReasons : ReasonDatabase s (original ++ learned) count)
    (lit : Lit) (ref previous : Nat) {entry : StoredClause} (member : entry ∈ original ++ learned)
    (id : watchClause ref = entry.id) (wide : 2 ≤ entry.lits.size) (watched : WatchEntry s lit ref)
    (prior : previous = 0 ∨ StoredWatchRef (original ++ learned) previous) {pos : Nat}
    (found : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = some pos) :
    let arrays := movedWatchArrays s.arena s.first lit ref previous pos
    ReasonGraph formula (restoreWatchArrays s arrays.1 arrays.2) count rank := by
  obtain ⟨offset, _, _, _, nextDatabase, _⟩ :=
    replacement_branch_database database meaning lit ref previous member id wide watched prior found
  let f := moveWatchEntry entry.id offset (s.db entry.id == lit)
  let arrays := movedWatchArrays s.arena s.first lit ref previous pos
  let after := restoreWatchArrays s arrays.1 arrays.2
  have scan : replacement (orientWatch s.arena entry.id lit) s.marks entry.id = some pos := by
    simpa only [id] using found
  constructor
  · exact graph.countBound
  · exact graph.ranks
  · exact graph.distinctVariables
  · intro i before nondecision
    obtain ⟨lits, packed, nonempty, head, entailed, earlier⟩ := graph.clauses i before nondecision
    obtain ⟨reasonEntry, reasonMember, reasonId⟩ := storedReasons i before nondecision
    have different : reasonEntry.id ≠ entry.id := by
      rw [← reasonId]
      exact replacement_not_active_reason graph active countActive (database.layout.packed member) wide lit scan i before
    have unchanged : f reasonEntry = reasonEntry := moveWatchEntry_of_ne _ _ _ _ different
    have mapped : reasonEntry ∈ original.map f ++ learned.map f := by
      rw [← List.map_append]
      exact List.mem_map.mpr ⟨reasonEntry, reasonMember, unchanged⟩
    have oldStored : PackedClause s (s.reason s.trail[i]!) reasonEntry.lits := by
      simpa only [reasonId] using database.layout.packed reasonMember
    have sameLits := oldStored.unique packed
    have newPacked : PackedClause after (after.reason after.trail[i]!) lits := by
      have reasonAfter : after.reason after.trail[i]! = reasonEntry.id := reasonId
      rw [reasonAfter]
      simpa only [sameLits] using nextDatabase.layout.packed mapped
    exact ⟨lits, newPacked, nonempty, head, entailed, earlier⟩

end MicrosatLean.Verification.Implementation.Native.Propagation
