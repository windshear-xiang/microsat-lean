import MicrosatLean.Verification.Implementation.Native.Propagation.WatchLinks

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation

theorem WatchLinks.swapCells {s : State} {lit : Lit} {refs : List Nat} (links : WatchLinks s lit refs)
    (left right : Nat) (leftBound : left < s.arena.size) (rightBound : right < s.arena.size)
    (indices : ∀ ref ∈ refs, watchLinkPos ref < s.arena.size)
    (disjoint : ∀ ref ∈ refs, watchLinkPos ref ≠ left ∧ watchLinkPos ref ≠ right) :
    WatchLinks { s with arena := s.arena.swapIfInBounds left right } lit refs := by
  apply links.frame (after := { s with arena := s.arena.swapIfInBounds left right }) rfl
  intro ref member
  change (s.arena.swapIfInBounds left right)[watchLinkPos ref]! = _
  rw [swap_read _ _ _ _ leftBound rightBound (indices ref member)]
  simp only [(disjoint ref member).1, (disjoint ref member).2, ite_false]
  rfl

/-- Every linked pointer lives in a genuine header, so in-clause swaps leave
the entire finite pointer chain intact, including refs of the changed clause. -/
theorem WatchLinks.moveWatch {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {entry : StoredClause} (member : entry ∈ original ++ learned)
    (lit : Lit) (offset : Nat) (afterWatches : 2 ≤ offset) (within : offset < entry.lits.size)
    (watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit)
    {other : Lit} {refs : List Nat} (links : WatchLinks s other refs)
    (proper : ∀ ref ∈ refs, StoredWatchRef (original ++ learned) ref) :
    WatchLinks { s with arena := moveWatch s.arena entry.id lit (entry.id + offset) } other refs := by
  have packed := database.layout.packed member
  have bound (i : Nat) (hi : i < entry.lits.size) : entry.id + i < s.arena.size := by
    have := packed.endBound
    omega
  have indices := fun ref hRef => storedWatchRef_link_bound database (proper ref hRef)
  have safe (ref : Nat) (hRef : ref ∈ refs) (i : Nat) (hi : i < entry.lits.size) :
      watchLinkPos ref ≠ entry.id + i := by
    obtain ⟨header, headerMember, id, _⟩ := proper ref hRef
    have different := database.layout.header_ne_literal headerMember member (ref % 2)
      (by omega) i (Nat.le_of_lt hi)
    simp only [watchClause] at id
    simpa only [watchLinkPos, id] using different
  have headBound : entry.id + 1 < s.arena.size := bound 1 (by omega)
  have posBound : entry.id + offset < s.arena.size := bound offset within
  rw [moveWatch_eq_swaps _ _ _ _ headBound (by omega) posBound watched]
  by_cases first : s.arena[entry.id]! = lit
  · have initial := links.swapCells entry.id (entry.id + 1) (by have := bound 0 (by omega); simpa using this)
      headBound indices (fun ref hRef => ⟨by simpa using safe ref hRef 0 (by omega), safe ref hRef 1 (by omega)⟩)
    have final := initial.swapCells (entry.id + 1) (entry.id + offset) (by simpa using headBound)
      (by simpa using posBound) (by simpa using indices)
      (fun ref hRef => ⟨safe ref hRef 1 (by omega), safe ref hRef offset within⟩)
    simpa only [first, beq_self_eq_true, ite_true] using final
  · simpa only [beq_iff_eq, first, ite_false] using links.swapCells (entry.id + 1) (entry.id + offset)
      headBound posBound indices (fun ref hRef => ⟨safe ref hRef 1 (by omega), safe ref hRef offset within⟩)

theorem WatchLinks.swapLiterals {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {entry : StoredClause} (member : entry ∈ original ++ learned)
    (left right : Nat) (leftBound : left < entry.lits.size) (rightBound : right < entry.lits.size)
    {lit : Lit} {refs : List Nat} (links : WatchLinks s lit refs)
    (proper : ∀ ref ∈ refs, StoredWatchRef (original ++ learned) ref) :
    WatchLinks { s with arena := s.arena.swapIfInBounds (entry.id + left) (entry.id + right) } lit refs := by
  have packed := database.layout.packed member
  have bound (i : Nat) (hi : i < entry.lits.size) : entry.id + i < s.arena.size := by
    have := packed.endBound
    omega
  apply links.swapCells _ _ (bound left leftBound) (bound right rightBound)
    (fun ref member => storedWatchRef_link_bound database (proper ref member))
  intro ref refMember
  obtain ⟨header, headerMember, id, _⟩ := proper ref refMember
  simp only [watchClause] at id
  constructor
  · simpa only [watchLinkPos, id] using database.layout.header_ne_literal headerMember member (ref % 2)
      (by omega) left (Nat.le_of_lt leftBound)
  · simpa only [watchLinkPos, id] using database.layout.header_ne_literal headerMember member (ref % 2)
      (by omega) right (Nat.le_of_lt rightBound)

end MicrosatLean.Verification.Implementation.Native.Propagation
