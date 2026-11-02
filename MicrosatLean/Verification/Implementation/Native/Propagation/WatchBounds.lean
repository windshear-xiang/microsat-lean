import MicrosatLean.Verification.Implementation.Native.Propagation.WatchCursor

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation

theorem storedWatchRef_nonzero {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {ref : Nat} (proper : StoredWatchRef (original ++ learned) ref) : ref ≠ 0 := by
  obtain ⟨entry, member, id, _⟩ := proper
  have lower := (database.layout.packed member).startLower
  simp only [watchClause] at id
  omega

theorem storedWatchRef_link_lower {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {ref : Nat} (proper : StoredWatchRef (original ++ learned) ref) :
    2 ≤ watchLinkPos ref := by
  obtain ⟨entry, member, id, _⟩ := proper
  have lower := (database.layout.packed member).startLower
  simp only [watchClause] at id
  unfold watchLinkPos
  omega

/-- Distinct refs occupy distinct genuine header cells, all above the two
reserved slots. Thus the arena-size runtime budget strictly exceeds a list. -/
theorem watchLinks_length_lt_arena {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {lit : Lit} {refs : List Nat} (links : WatchLinks s lit refs)
    (proper : ∀ ref ∈ refs, StoredWatchRef (original ++ learned) ref) : refs.length < s.arena.size := by
  have mappedNodup : (refs.map watchLinkPos).Nodup := by
    apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j hi hj equal
    have beforeI : i < refs.length := by simpa using hi
    have beforeJ : j < refs.length := by simpa using hj
    have same : refs[i] = refs[j] := storedWatchRef_link_injective database
      (proper _ (List.getElem_mem beforeI)) (proper _ (List.getElem_mem beforeJ)) (by
        simpa only [List.getElem_map] using equal)
    exact links.1.eq_of_getElem_eq beforeI beforeJ same
  have included : refs.map watchLinkPos ⊆ List.range' 2 (s.arena.size - 2) := by
    intro position member
    obtain ⟨ref, refMember, rfl⟩ := List.mem_map.mp member
    have lower := storedWatchRef_link_lower database (proper ref refMember)
    have upper := storedWatchRef_link_bound database (proper ref refMember)
    apply List.mem_range'.mpr
    exact ⟨watchLinkPos ref - 2, by omega, by omega⟩
  have bound := mappedNodup.length_le_of_subset included
  have reserved : 2 ≤ s.arena.size := by have := database.layout.size; omega
  simp only [List.length_map, List.length_range'] at bound
  omega

theorem watchCursor_length_lt_arena {s : State} {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (certificate : WatchCertificate s (original ++ learned) heads)
    {lit : Lit} {previous : Nat} {remaining : List Nat} (cursor : WatchCursor heads lit previous remaining) :
    remaining.length < s.arena.size :=
  Nat.lt_of_le_of_lt cursor.length_le (watchLinks_length_lt_arena database (certificate.links lit)
    (certificate.references lit))

theorem arrayBounds_restoreWatchArrays {s : State} (arrays : ArrayBounds s) (arena first : Array Nat)
    (size : first.size = s.first.size) : ArrayBounds (restoreWatchArrays s arena first) :=
  ⟨size.trans arrays.firstSize, arrays.marksSize, arrays.reasonsSize, arrays.phasesSize,
    arrays.trailSize, arrays.previousSize, arrays.nextSize⟩

@[simp] theorem orientWatch_size (arena : Array Nat) (id : Nat) (lit : Lit) :
    (orientWatch arena id lit).size = arena.size := by unfold orientWatch; split <;> simp

@[simp] theorem moveWatch_size (arena : Array Nat) (id : Nat) (lit : Lit) (pos : Nat) :
    (moveWatch arena id lit pos).size = arena.size := by simp [moveWatch]

@[simp] theorem rewireWatch_first_size (arena first : Array Nat) (lit newLit : Lit) (ref previous : Nat) :
    (rewireWatch arena first lit newLit ref previous).2.size = first.size := by
  unfold rewireWatch
  split <;> simp

@[simp] theorem rewireWatch_arena_size (arena first : Array Nat) (lit newLit : Lit) (ref previous : Nat) :
    (rewireWatch arena first lit newLit ref previous).1.size = arena.size := by
  unfold rewireWatch
  split <;> simp

@[simp] theorem movedWatchArrays_first_size (arena first : Array Nat) (lit : Lit) (ref previous pos : Nat) :
    (movedWatchArrays arena first lit ref previous pos).2.size = first.size := by simp [movedWatchArrays]

@[simp] theorem movedWatchArrays_arena_size (arena first : Array Nat) (lit : Lit) (ref previous pos : Nat) :
    (movedWatchArrays arena first lit ref previous pos).1.size = arena.size := by simp [movedWatchArrays]

end MicrosatLean.Verification.Implementation.Native.Propagation
