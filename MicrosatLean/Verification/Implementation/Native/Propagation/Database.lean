import MicrosatLean.Verification.Implementation.Native.Representation.DatabaseUpdates
import MicrosatLean.Verification.Implementation.Native.Representation.Meaning
import Init.Data.Array.Perm

namespace MicrosatLean.Verification.Implementation.Native.Representation

open CDCL Std.Sat

/-- A zero-terminated nonzero literal slice has a unique width at its start. -/
theorem PackedClause.size_eq {s : State} {id : Nat} {left right : Array Lit}
    (first : PackedClause s id left) (second : PackedClause s id right) : left.size = right.size := by
  have notShorter {a b : Array Lit} (before : PackedClause s id a) (after : PackedClause s id b) :
      ¬a.size < b.size := by
    intro shorter
    have member : b[a.size]! ∈ b := by
      simpa only [getElem!_pos b a.size shorter] using Array.getElem_mem shorter
    have nonzero := (after.wellFormed _ member).nonzero
    exact nonzero ((after.literals a.size shorter).symm.trans before.terminator)
  have leftNot := notShorter first second
  have rightNot := notShorter second first
  omega

theorem PackedClause.unique {s : State} {id : Nat} {left right : Array Lit}
    (first : PackedClause s id left) (second : PackedClause s id right) : left = right := by
  apply Array.ext (first.size_eq second)
  intro i before after
  rw [← getElem!_pos left i before, ← getElem!_pos right i after]
  exact (first.literals i before).symm.trans (second.literals i after)

theorem DatabaseFrom.entry_eq_of_id {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) {left right : StoredClause}
    (leftMember : left ∈ entries) (rightMember : right ∈ entries) (same : left.id = right.id) : left = right := by
  obtain ⟨i, hi, vi⟩ := List.getElem_of_mem leftMember
  obtain ⟨j, hj, vj⟩ := List.getElem_of_mem rightMember
  have equal : i = j := (layout.nodup_ids.getElem_inj
    (hi := by simpa using hi) (hj := by simpa using hj)).mp (by
      simpa only [List.getElem_map, vi, vj] using same)
  subst j
  exact vi.symm.trans vj

theorem DatabaseFrom.separated {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) {left right : StoredClause}
    (leftMember : left ∈ entries) (rightMember : right ∈ entries) (different : left.id ≠ right.id) :
    left.id + left.lits.size + 3 ≤ right.id ∨ right.id + right.lits.size + 3 ≤ left.id := by
  obtain ⟨i, hi, vi⟩ := List.getElem_of_mem leftMember
  obtain ⟨j, hj, vj⟩ := List.getElem_of_mem rightMember
  by_cases order : i < j
  · left
    simpa only [vi, vj] using layout.spacing.rel_getElem_of_lt hi hj order
  · have reverse : j < i := by
      by_cases equal : i = j
      · subst j
        exact False.elim (different (congrArg StoredClause.id (vi.symm.trans vj)))
      · omega
    right
    simpa only [vi, vj] using layout.spacing.rel_getElem_of_lt hj hi reverse

/-- Genuine header cells are disjoint from every stored literal and zero
terminator, including those of their own clause. -/
theorem DatabaseFrom.header_ne_literal {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) {header entry : StoredClause}
    (headerMember : header ∈ entries) (entryMember : entry ∈ entries)
    (slot : Nat) (slotBound : slot ≤ 1) (offset : Nat) (offsetBound : offset ≤ entry.lits.size) :
    header.id - 2 + slot ≠ entry.id + offset := by
  have lower := (layout.packed headerMember).startLower
  by_cases same : header.id = entry.id
  · omega
  · rcases layout.separated headerMember entryMember same with forward | backward <;> omega

theorem DatabaseFrom.literal_ne_other {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) {source entry : StoredClause}
    (sourceMember : source ∈ entries) (entryMember : entry ∈ entries)
    (different : source.id ≠ entry.id) (left right : Nat)
    (leftBound : left < source.lits.size) (rightBound : right ≤ entry.lits.size) :
    source.id + left ≠ entry.id + right := by
  rcases layout.separated sourceMember entryMember different with forward | backward <;> omega

theorem PackedClause.sameSlice {s : State} {id : Nat} {lits : Array Lit}
    (packed : PackedClause s id lits) (arena : Array Nat) (size : arena.size = s.arena.size)
    (reads : ∀ i, i ≤ lits.size → arena[id + i]! = s.db (id + i)) :
    PackedClause { s with arena := arena } id lits := by
  refine ⟨packed.startLower, ?_, ?_, ?_, packed.wellFormed⟩
  · simpa only [size] using packed.endBound
  · intro i within
    exact (reads i (Nat.le_of_lt within)).trans (packed.literals i within)
  · exact (reads lits.size (Nat.le_refl _)).trans packed.terminator

theorem DatabaseFrom.mapEntries {s after : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) (f : StoredClause → StoredClause)
    (size : after.arena.size = s.arena.size) (ids : ∀ entry, (f entry).id = entry.id)
    (lengths : ∀ entry, (f entry).lits.size = entry.lits.size)
    (packed : ∀ entry ∈ entries, PackedClause after (f entry).id (f entry).lits) :
    DatabaseFrom after start (entries.map f) := by
  induction entries generalizing start with
  | nil => simpa only [List.map_nil, DatabaseFrom, size] using layout
  | cons entry rest ih =>
    refine ⟨(ids entry).trans layout.1, packed entry (by simp), ?_⟩
    simpa only [ids, lengths] using ih layout.2.2 (by
      intro other member
      exact packed other (by simp [member]))

theorem Database.mapEntries {s after : State} {original learned : List StoredClause}
    (database : Database s original learned) (f : StoredClause → StoredClause)
    (size : after.arena.size = s.arena.size) (fixed : after.fixed = s.fixed)
    (count : after.nLemmas = s.nLemmas) (ids : ∀ entry, (f entry).id = entry.id)
    (lengths : ∀ entry, (f entry).lits.size = entry.lits.size)
    (packed : ∀ entry ∈ original ++ learned, PackedClause after (f entry).id (f entry).lits) :
    Database after (original.map f) (learned.map f) := by
  constructor
  · rw [← List.map_append]
    exact database.layout.mapEntries f size ids lengths packed
  · simpa only [List.map_map, Function.comp_def, lengths] using fixed.trans database.fixed
  · simpa only [List.length_map] using count.trans database.learnedCount

/-- Rewriting one genuine watch header preserves the whole packed database,
regardless of which watch list owns that header. -/
theorem Database.setHeader {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {entry : StoredClause}
    (member : entry ∈ original ++ learned) (slot value : Nat) (slotBound : slot ≤ 1) :
    Database { s with arena := s.arena.set! (entry.id - 2 + slot) value } original learned := by
  have mapped := database.mapEntries
    (after := { s with arena := s.arena.set! (entry.id - 2 + slot) value })
    id (by simp) rfl rfl (fun _ => rfl) (fun _ => rfl) (by
    intro other otherMember
    apply (database.layout.packed otherMember).sameSlice
      (s.arena.set! (entry.id - 2 + slot) value) (by simp)
    intro offset within
    exact Array.getElem!_set!_ne _ _ _ _
      (database.layout.header_ne_literal member otherMember slot slotBound offset within))
  simpa only [List.map_id] using mapped

theorem swap_read (arena : Array Nat) (left right index : Nat)
    (leftBound : left < arena.size) (rightBound : right < arena.size) (bound : index < arena.size) :
    (arena.swapIfInBounds left right)[index]! =
      if index = left then arena[right]! else if index = right then arena[left]! else arena[index]! := by
  rw [getElem!_pos _ _ (by simpa using bound), Array.getElem_swapIfInBounds]
  simp only [leftBound, rightBound, and_true, getElem!_pos arena right rightBound,
    getElem!_pos arena left leftBound, getElem!_pos arena index bound]
  by_cases same : left = right <;> by_cases first : index = left <;>
    by_cases second : index = right <;> simp_all

private theorem swap_perm (lits : Array Lit) (left right : Nat) :
    (lits.swapIfInBounds left right).Perm lits := by
  unfold Array.swapIfInBounds
  split
  · split
    · exact Array.swap_perm _ _
    · exact .refl _
  · exact .refl _

/-- Swapping two in-clause arena cells exactly swaps the corresponding ghost
literal positions and leaves the terminator fixed. -/
theorem PackedClause.swapLiterals {s : State} {id : Nat} {lits : Array Lit}
    (packed : PackedClause s id lits) (left right : Nat)
    (leftBound : left < lits.size) (rightBound : right < lits.size) :
    PackedClause { s with arena := s.arena.swapIfInBounds (id + left) (id + right) }
      id (lits.swapIfInBounds left right) := by
  have arenaLeft : id + left < s.arena.size := by have := packed.endBound; omega
  have arenaRight : id + right < s.arena.size := by have := packed.endBound; omega
  refine ⟨packed.startLower, by simpa using packed.endBound, ?_, ?_, ?_⟩
  · intro i within
    have old : i < lits.size := by simpa using within
    have arenaIndex : id + i < s.arena.size := by have := packed.endBound; omega
    change (s.arena.swapIfInBounds (id + left) (id + right))[id + i]! = _
    rw [swap_read _ _ _ _ arenaLeft arenaRight arenaIndex, swap_read lits _ _ _ leftBound rightBound old]
    have firstRead : s.arena[id + left]! = lits[left]! := packed.literals left leftBound
    have secondRead : s.arena[id + right]! = lits[right]! := packed.literals right rightBound
    have indexRead : s.arena[id + i]! = lits[i]! := packed.literals i old
    simp only [Nat.add_left_cancel_iff, firstRead, secondRead, indexRead]
  · change (s.arena.swapIfInBounds (id + left) (id + right))[id + _]! = 0
    simp only [Array.size_swapIfInBounds]
    rw [swap_read _ _ _ _ arenaLeft arenaRight packed.endBound]
    simp only [show id + lits.size ≠ id + left by omega, show id + lits.size ≠ id + right by omega,
      ite_false]
    exact packed.terminator
  · intro lit member
    exact packed.wellFormed lit ((swap_perm lits left right).mem_iff.mp member)

/-- Only the targeted entry changes literal order; IDs, widths and original
versus learned classification are retained. -/
def swapEntry (id left right : Nat) (entry : StoredClause) : StoredClause :=
  if entry.id = id then { entry with lits := entry.lits.swapIfInBounds left right } else entry

@[simp] theorem swapEntry_id (id left right : Nat) (entry : StoredClause) :
    (swapEntry id left right entry).id = entry.id := by simp [swapEntry]; split <;> rfl

@[simp] theorem swapEntry_size (id left right : Nat) (entry : StoredClause) :
    (swapEntry id left right entry).lits.size = entry.lits.size := by
  unfold swapEntry
  split <;> simp

theorem swapEntry_perm (id left right : Nat) (entry : StoredClause) :
    (swapEntry id left right entry).lits.Perm entry.lits := by
  unfold swapEntry
  split
  · exact swap_perm _ _ _
  · exact .refl _

theorem Database.swapLiterals {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {entry : StoredClause}
    (member : entry ∈ original ++ learned) (left right : Nat)
    (leftBound : left < entry.lits.size) (rightBound : right < entry.lits.size) :
    Database { s with arena := s.arena.swapIfInBounds (entry.id + left) (entry.id + right) }
      (original.map (swapEntry entry.id left right)) (learned.map (swapEntry entry.id left right)) := by
  apply database.mapEntries
    (after := { s with arena := s.arena.swapIfInBounds (entry.id + left) (entry.id + right) })
    (swapEntry entry.id left right) (by simp) rfl rfl
    (swapEntry_id _ _ _) (swapEntry_size _ _ _)
  intro other otherMember
  by_cases same : other.id = entry.id
  · have unique : other = entry := by
      have ids := database.layout.nodup_ids
      obtain ⟨i, hi, vi⟩ := List.getElem_of_mem otherMember
      obtain ⟨j, hj, vj⟩ := List.getElem_of_mem member
      have equal : i = j := (ids.getElem_inj
        (hi := by simpa using hi) (hj := by simpa using hj)).mp (by
          simpa only [List.getElem_map, vi, vj] using same)
      subst j
      exact vi.symm.trans vj
    subst other
    simpa only [swapEntry, ite_true] using
      (database.layout.packed member).swapLiterals left right leftBound rightBound
  · have packed := database.layout.packed otherMember
    simp only [swapEntry, ite_false, same]
    apply packed.sameSlice (s.arena.swapIfInBounds (entry.id + left) (entry.id + right)) (by simp)
    intro offset within
    have entryPacked := database.layout.packed member
    have arenaLeft : entry.id + left < s.arena.size := by have := entryPacked.endBound; omega
    have arenaRight : entry.id + right < s.arena.size := by have := entryPacked.endBound; omega
    have arenaIndex : other.id + offset < s.arena.size := by have := packed.endBound; omega
    rw [swap_read _ _ _ _ arenaLeft arenaRight arenaIndex]
    simp only [Ne.symm (database.layout.literal_ne_other member otherMember (Ne.symm same)
      left offset leftBound within), Ne.symm (database.layout.literal_ne_other member otherMember
      (Ne.symm same) right offset rightBound within), ite_false]
    rfl

theorem swapEntry_sat_iff (id left right : Nat) (entry : StoredClause) (a : Nat → Bool) :
    CNF.Clause.Sat a (swapEntry id left right entry).view ↔ CNF.Clause.Sat a entry.view := by
  unfold swapEntry
  split
  · exact clauseView_sat_iff_of_mem_iff (fun _ => (swap_perm entry.lits left right).mem_iff) a
  · exact Iff.rfl

theorem databaseView_swapEntries_sat_iff (id left right : Nat) (entries : List StoredClause)
    (a : Nat → Bool) :
    CNF.Sat a (databaseView (entries.map (swapEntry id left right))) ↔
      CNF.Sat a (databaseView entries) := by
  rw [databaseView_sat_iff, databaseView_sat_iff]
  constructor
  · intro model entry member
    exact (swapEntry_sat_iff id left right entry a).mp
      (model _ (List.mem_map.mpr ⟨entry, member, rfl⟩))
  · intro model entry member
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp member
    exact (swapEntry_sat_iff id left right old a).mpr (model old oldMember)

theorem DatabaseMeaning.swapLiterals {formula : CNF Nat} {original learned : List StoredClause}
    (meaning : DatabaseMeaning formula original learned) (id left right : Nat) :
    DatabaseMeaning formula (original.map (swapEntry id left right))
      (learned.map (swapEntry id left right)) := by
  constructor
  · exact ⟨fun a model => (databaseView_swapEntries_sat_iff _ _ _ _ a).mpr (meaning.original.1 a model),
      fun a model => meaning.original.2 a ((databaseView_swapEntries_sat_iff _ _ _ _ a).mp model)⟩
  · exact fun a model => (databaseView_swapEntries_sat_iff _ _ _ _ a).mpr (meaning.learned a model)

end MicrosatLean.Verification.Implementation.Native.Representation
