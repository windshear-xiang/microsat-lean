import MicrosatLean.Verification.Implementation.Native.Propagation.WatchSettlementBranches

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation Analysis

/-- Literal permutations of a genuine long target leave every singleton's
sole literal unchanged. This preserves its concrete active truth witness. -/
theorem units_map_long {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {target : StoredClause}
    (member : target ∈ original ++ learned) (wide : 2 ≤ target.lits.size)
    (units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]!)
    (f : StoredClause → StoredClause) (sizes : ∀ entry, (f entry).lits.size = entry.lits.size)
    (unchanged : ∀ entry, entry.id ≠ target.id → f entry = entry)
    (arena first : Array Nat) :
    ∀ entry ∈ (original ++ learned).map f, entry.lits.size = 1 →
      TrueBefore (restoreWatchArrays s arena first) (restoreWatchArrays s arena first).assigned entry.lits[0]! := by
  intro changed changedMember unit
  obtain ⟨entry, oldMember, rfl⟩ := List.mem_map.mp changedMember
  have oldUnit : entry.lits.size = 1 := by simpa only [sizes] using unit
  have different : entry.id ≠ target.id := by
    intro same
    have equal := database.layout.entry_eq_of_id oldMember member same
    subst entry
    omega
  rw [unchanged entry different]
  exact units entry oldMember oldUnit

theorem units_assign {s : State} {entries : List StoredClause}
    (units : ∀ entry ∈ entries, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]!)
    (id : Nat) (root : Bool) :
    ∀ entry ∈ entries, entry.lits.size = 1 →
      TrueBefore (s.assign id root) (s.assign id root).assigned entry.lits[0]! := by
  intro entry member unit
  exact trueBefore_assign (units entry member unit)

end MicrosatLean.Verification.Implementation.Native.Propagation
