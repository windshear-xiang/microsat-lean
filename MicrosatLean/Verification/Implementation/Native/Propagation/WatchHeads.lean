import MicrosatLean.Verification.Implementation.Native.Propagation.WatchInvariant

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation

/-- The simultaneous ghost movement of one reference. Unique head ownership
makes erasure on every other list a no-op except at its old owner. -/
def moveHeads (heads : Nat → List Nat) (newLit : Lit) (ref : Nat) (lit : Lit) : List Nat :=
  if lit = newLit then ref :: heads lit else (heads lit).erase ref

theorem moveHeads_mem_iff {heads : Nat → List Nat} (nodup : ∀ lit, (heads lit).Nodup)
    (newLit : Lit) (ref : Nat) (lit : Lit) (other : Nat) :
    other ∈ moveHeads heads newLit ref lit ↔
      (other = ref ∧ lit = newLit) ∨ (other ≠ ref ∧ other ∈ heads lit) := by
  by_cases head : lit = newLit <;> by_cases same : other = ref <;>
    simp [moveHeads, head, same, (nodup lit).mem_erase_iff]

theorem moveHeads_moved_mem_iff {heads : Nat → List Nat} (nodup : ∀ lit, (heads lit).Nodup)
    (newLit : Lit) (ref : Nat) (lit : Lit) :
    ref ∈ moveHeads heads newLit ref lit ↔ lit = newLit := by
  simp only [moveHeads_mem_iff nodup, true_and, ne_eq, not_true_eq_false, false_and, or_false]

theorem moveHeads_other_mem_iff {heads : Nat → List Nat} (nodup : ∀ lit, (heads lit).Nodup)
    (newLit : Lit) (ref : Nat) (lit : Lit) (other : Nat) (different : other ≠ ref) :
    other ∈ moveHeads heads newLit ref lit ↔ other ∈ heads lit := by
  rw [moveHeads_mem_iff nodup]
  constructor
  · rintro (⟨same, _⟩ | ⟨_, member⟩)
    · exact False.elim (different same)
    · exact member
  · exact fun member => Or.inr ⟨different, member⟩

theorem moveHeads_unique {heads : Nat → List Nat} (nodup : ∀ lit, (heads lit).Nodup)
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    (newLit : Lit) (ref : Nat) :
    ∀ lit other old, old ∈ moveHeads heads newLit ref lit → old ∈ moveHeads heads newLit ref other → lit = other := by
  intro lit other old left right
  by_cases same : old = ref
  · subst old
    exact ((moveHeads_moved_mem_iff nodup _ _ _).mp left).trans
      ((moveHeads_moved_mem_iff nodup _ _ _).mp right).symm
  · exact unique lit other old ((moveHeads_other_mem_iff nodup _ _ _ _ same).mp left)
      ((moveHeads_other_mem_iff nodup _ _ _ _ same).mp right)

theorem moveHeads_nodup {heads : Nat → List Nat} (nodup : ∀ lit, (heads lit).Nodup)
    (newLit : Lit) (ref : Nat) (fresh : ref ∉ heads newLit) :
    ∀ lit, (moveHeads heads newLit ref lit).Nodup := by
  intro lit
  unfold moveHeads
  split
  · rename_i same
    exact List.nodup_cons.mpr ⟨by simpa only [same] using fresh, nodup lit⟩
  · exact (nodup lit).erase ref

theorem moveHeads_references {heads : Nat → List Nat} {entries : List StoredClause}
    (nodup : ∀ lit, (heads lit).Nodup)
    (proper : ∀ lit ref, ref ∈ heads lit → StoredWatchRef entries ref)
    (newLit : Lit) (ref : Nat) (movedProper : StoredWatchRef entries ref)
    (f : StoredClause → StoredClause) (ids : ∀ entry, (f entry).id = entry.id)
    (sizes : ∀ entry, (f entry).lits.size = entry.lits.size) :
    ∀ lit old, old ∈ moveHeads heads newLit ref lit → StoredWatchRef (entries.map f) old := by
  intro lit old member
  rcases (moveHeads_mem_iff nodup _ _ _ _).mp member with moved | retained
  · rcases moved with ⟨rfl, _⟩
    exact movedProper.mapEntries f ids sizes
  · exact (proper lit old retained.2).mapEntries f ids sizes

theorem moveHeads_other {heads : Nat → List Nat}
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    (lit newLit other : Lit) (ref : Nat) (current : ref ∈ heads lit)
    (sourceDifferent : other ≠ lit) (targetDifferent : other ≠ newLit) :
    moveHeads heads newLit ref other = heads other := by
  have absent : ref ∉ heads other := fun member => sourceDifferent (unique lit other ref current member).symm
  simp only [moveHeads, targetDifferent, ite_false, List.erase_of_not_mem absent]

theorem moveHeads_source_length {heads : Nat → List Nat} (lit newLit : Lit) (ref : Nat)
    (current : ref ∈ heads lit) (different : lit ≠ newLit) :
    (moveHeads heads newLit ref lit).length + 1 = (heads lit).length := by
  simp only [moveHeads, different, ite_false, List.length_erase_of_mem current]
  have positive := List.length_pos_of_mem current
  omega

end MicrosatLean.Verification.Implementation.Native.Propagation
