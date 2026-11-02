import MicrosatLean.Verification.Implementation.Search.WatchState
import MicrosatLean.Verification.Implementation.Bridge.Assignment

namespace MicrosatLean.Verification.Implementation.Search

open CDCL Bridge
open Native.Representation Native.Propagation
private abbrev NEntry := Native.Representation.StoredClause

/-- A failed replacement scan supplies the false tails of the actual reason;
the two mark tests supply a fresh head. Orientation and assignment are then
two separate logical moves. -/
theorem watch_unit_trace {input : CNF} {s : State}
    {original learned : List NEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (falseLit : s.mark lit ≠ 0)
    (missing : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = none)
    (head : s.mark ((retainWatch s.arena (watchClause ref) lit)[watchClause ref]!) = 0)
    (opposite : s.mark (Lit.negate ((retainWatch s.arena (watchClause ref) lit)[watchClause ref]!)) = 0)
    (root : Bool) {nextOriginal nextLearned : List NEntry}
    (database : Database
      ({ s with arena := retainWatch s.arena (watchClause ref) lit }.assign (watchClause ref) root)
      nextOriginal nextLearned) :
    LogicalExecution input (nativeState s original learned)
      (nativeState ({ s with arena := retainWatch s.arena (watchClause ref) lit }.assign (watchClause ref) root)
        nextOriginal nextLearned) := by
  obtain ⟨entry, member, id, wide⟩ := base.watches.references lit ref current
  have watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (base.watches.entry base.database current).2.2.2
  have exactDatabase := retainWatch_database base.database member lit wide watched
  rw [← id] at exactDatabase
  obtain ⟨retainedOriginal, retainedLearned, retainedBase, _⟩ := base.retainWatch current falseLit
  obtain ⟨rfl, rfl⟩ := retainedBase.database.unique exactDatabase
  obtain ⟨rfl, rfl⟩ := database.unique (retainedBase.database.assign (watchClause ref) root)
  let f := retainWatchEntry (watchClause ref) (s.db (watchClause ref) == lit)
  let retained := { s with arena := retainWatch s.arena (watchClause ref) lit }
  have mapped : f entry ∈ original.map f ++ learned.map f := by
    rw [← List.map_append]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have packed := retainedBase.database.layout.packed mapped
  have packedId : (f entry).id = watchClause ref := (retainWatchEntry_id _ _ _).trans id.symm
  have packedWide : 2 ≤ (f entry).lits.size := by simpa only [f, retainWatchEntry_size] using wide
  have missingRetained : replacement retained.arena retained.marks (f entry).id = none := by
    rw [packedId]
    exact (replacement_retainWatch _ _ _ _).trans missing
  have second : (f entry).lits[1]! = lit := by
    have oldPacked := base.database.layout.packed member
    have oldHead : s.db entry.id = entry.lits[0]! := by simpa using oldPacked.literals 0 (by omega)
    have pair := retainedEntry_watches entry lit wide (base.watches.covered entry member wide).1
      (watch_ref_literals base.database base.watches member current id wide)
    simpa only [f, id, oldHead] using pair.2
  have secondFalse : retained.mark (f entry).lits[1]! ≠ 0 := by
    change s.mark (f entry).lits[1]! ≠ 0
    rw [second]
    exact falseLit
  have tails : ∀ j, 0 < j → j < (f entry).lits.size →
      Native.Analysis.TrailMember retained retained.assigned (f entry).lits[j]! := by
    intro j positive before
    apply retainedBase.marked
    by_cases one : j = 1
    · simpa only [one] using secondFalse
    · exact replacement_none_of_packed packed missingRetained (by omega) before
  have headZero : retained.mark (retained.db (f entry).id) = 0 := by
    simpa only [packedId, retained, State.mark, State.db] using head
  have oppositeZero : retained.mark (Lit.negate (retained.db (f entry).id)) = 0 := by
    simpa only [packedId, retained, State.mark, State.db] using opposite
  have orient := retained_trace base current falseLit retainedBase.database
  have assign := native_unit_trace retainedBase mapped (by omega) headZero oppositeZero tails root
  have combined := Logic.execution_trans orient assign
  simpa only [packedId, retained] using combined

end MicrosatLean.Verification.Implementation.Search
