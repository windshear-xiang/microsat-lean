import MicrosatLean.Verification.Implementation.Native.Propagation.Database
import MicrosatLean.Verification.Implementation.Native.Propagation.Replacement

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation

/-- The exact temporary orientation used before the replacement scan. The
second watch is restored only after that scan has chosen its branch. -/
def orientWatch (arena : Array Nat) (id : Nat) (lit : Lit) : Array Nat :=
  if arena[id]! == lit then arena.set! id arena[id + 1]! else arena

/-- The exact literal-cell writes in a successful replacement branch, before
its linked-list header writes. -/
def moveWatch (arena : Array Nat) (id : Nat) (lit : Lit) (pos : Nat) : Array Nat :=
  let oriented := orientWatch arena id lit
  (oriented.set! (id + 1) oriented[pos]!).set! pos lit

theorem set_read (arena : Array Nat) (index value query : Nat) (bound : index < arena.size) :
    (arena.set! index value)[query]! = if index = query then value else arena[query]! := by
  by_cases same : index = query
  · subst query
    exact (Array.getElem!_set!_self _ _ _ bound).trans (ite_eq_left rfl).symm
  · exact (Array.getElem!_set!_ne _ _ _ _ same).trans (ite_eq_right same).symm

theorem moveWatch_eq_swaps (arena : Array Nat) (id : Nat) (lit : Lit) (pos : Nat)
    (headBound : id + 1 < arena.size) (afterWatches : id + 2 ≤ pos) (posBound : pos < arena.size)
    (watched : arena[id]! = lit ∨ arena[id + 1]! = lit) :
    moveWatch arena id lit pos =
      (if arena[id]! == lit then arena.swapIfInBounds id (id + 1) else arena).swapIfInBounds (id + 1) pos := by
  have firstBound : id < arena.size := by omega
  have posHead : pos ≠ id := by omega
  have posSecond : pos ≠ id + 1 := by omega
  by_cases first : arena[id]! = lit
  · simp only [moveWatch, orientWatch, first, beq_self_eq_true, ite_true]
    apply Array.ext
    · simp
    · intro i before after
      have original : i < arena.size := by simpa using before
      rw [← getElem!_pos _ i before, ← getElem!_pos _ i after]
      rw [set_read _ _ _ _ (by simpa using posBound),
        set_read _ _ _ _ (by simpa using headBound), set_read _ _ _ _ firstBound,
        set_read _ _ _ _ firstBound,
        swap_read _ _ _ _ (by simpa using headBound) (by simpa using posBound) (by simpa using original)]
      simp only [swap_read _ _ _ _ firstBound headBound original,
        swap_read _ _ _ _ firstBound headBound posBound,
        swap_read _ _ _ _ firstBound headBound (by omega : id + 1 < arena.size)]
      by_cases atHead : i = id <;> by_cases atSecond : i = id + 1 <;>
        by_cases atPos : i = pos <;> simp_all [eq_comm] <;> omega
  · have second : arena[id + 1]! = lit := watched.resolve_left first
    simp only [moveWatch, orientWatch, beq_iff_eq, first, ite_false]
    apply Array.ext
    · simp
    · intro i before after
      have original : i < arena.size := by simpa using before
      rw [← getElem!_pos _ i before, ← getElem!_pos _ i after]
      rw [set_read _ _ _ _ (by simpa using posBound), set_read _ _ _ _ headBound,
        swap_read _ _ _ _ headBound posBound original]
      by_cases atSecond : i = id + 1 <;> by_cases atPos : i = pos <;> simp_all [eq_comm]

/-- The corresponding exact ghost update, with the same orientation test as
the runtime. Two swaps describe a first-watch move; one describes a second. -/
def moveWatchEntry (id offset : Nat) (first : Bool) (entry : StoredClause) : StoredClause :=
  if first then swapEntry id 1 offset (swapEntry id 0 1 entry) else swapEntry id 1 offset entry

@[simp] theorem moveWatchEntry_true (id offset : Nat) :
    moveWatchEntry id offset true = fun entry => swapEntry id 1 offset (swapEntry id 0 1 entry) := rfl

@[simp] theorem moveWatchEntry_false (id offset : Nat) :
    moveWatchEntry id offset false = swapEntry id 1 offset := rfl

@[simp] theorem moveWatchEntry_id (id offset : Nat) (first : Bool) (entry : StoredClause) :
    (moveWatchEntry id offset first entry).id = entry.id := by cases first <;> simp [moveWatchEntry]

@[simp] theorem moveWatchEntry_size (id offset : Nat) (first : Bool) (entry : StoredClause) :
    (moveWatchEntry id offset first entry).lits.size = entry.lits.size := by
  cases first <;> simp [moveWatchEntry]

theorem moveWatchEntry_of_ne (id offset : Nat) (first : Bool) (entry : StoredClause)
    (different : entry.id ≠ id) : moveWatchEntry id offset first entry = entry := by
  cases first <;> simp [moveWatchEntry, swapEntry, different]

theorem moveWatchEntry_perm (id offset : Nat) (first : Bool) (entry : StoredClause) :
    (moveWatchEntry id offset first entry).lits.Perm entry.lits := by
  cases first
  · exact swapEntry_perm _ _ _ _
  · exact (swapEntry_perm id 1 offset (swapEntry id 0 1 entry)).trans (swapEntry_perm _ _ _ _)

theorem moveWatchEntry_nodup (id offset : Nat) (first : Bool) (entry : StoredClause)
    (nodup : entry.lits.toList.Nodup) : (moveWatchEntry id offset first entry).lits.toList.Nodup :=
  (Array.perm_iff_toList_perm.mp (moveWatchEntry_perm id offset first entry)).symm.nodup nodup

theorem moveWatchEntry_heads (entry : StoredClause) (offset : Nat) (first : Bool)
    (afterWatches : 2 ≤ offset) (within : offset < entry.lits.size) :
    (moveWatchEntry entry.id offset first entry).lits[0]! =
      (if first then entry.lits[1]! else entry.lits[0]!) ∧
      (moveWatchEntry entry.id offset first entry).lits[1]! = entry.lits[offset]! := by
  have zero : 0 < entry.lits.size := by omega
  have one : 1 < entry.lits.size := by omega
  cases first
  · simp only [moveWatchEntry, swapEntry, Bool.false_eq_true, ↓reduceIte]
    change (entry.lits.swapIfInBounds 1 offset)[0]! = entry.lits[0]! ∧
      (entry.lits.swapIfInBounds 1 offset)[1]! = entry.lits[offset]!
    rw [swap_read _ _ _ _ one within zero, swap_read _ _ _ _ one within one]
    simp [show 0 ≠ offset by omega]
  · simp only [moveWatchEntry, swapEntry, ↓reduceIte]
    change ((entry.lits.swapIfInBounds 0 1).swapIfInBounds 1 offset)[0]! = entry.lits[1]! ∧
      ((entry.lits.swapIfInBounds 0 1).swapIfInBounds 1 offset)[1]! = entry.lits[offset]!
    rw [swap_read (entry.lits.swapIfInBounds 0 1) 1 offset 0
        (by simpa using one) (by simpa using within) (by simpa using zero),
      swap_read (entry.lits.swapIfInBounds 0 1) 1 offset 1
        (by simpa using one) (by simpa using within) (by simpa using one)]
    simp only [show 0 ≠ 1 by decide, show 0 ≠ offset by omega, ite_false, ite_true,
      swap_read _ _ _ _ zero one zero, swap_read _ _ _ _ zero one within,
      show offset ≠ 0 by omega, show offset ≠ 1 by omega]
    trivial

theorem literal_at_ne_of_nodup {lits : Array Lit} (nodup : lits.toList.Nodup)
    {left right : Nat} (leftBound : left < lits.size) (rightBound : right < lits.size)
    (different : left ≠ right) : lits[left]! ≠ lits[right]! := by
  intro equal
  have same : lits.toList[left] = lits.toList[right] := by
    simpa only [Array.getElem_toList, getElem!_pos lits left leftBound,
      getElem!_pos lits right rightBound] using equal
  exact different (nodup.eq_of_getElem_eq (by simpa using leftBound) (by simpa using rightBound) same)

theorem moveWatch_database {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {entry : StoredClause}
    (member : entry ∈ original ++ learned) (lit : Lit) (offset : Nat)
    (afterWatches : 2 ≤ offset) (within : offset < entry.lits.size)
    (watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit) :
    Database { s with arena := moveWatch s.arena entry.id lit (entry.id + offset) }
      (original.map (moveWatchEntry entry.id offset (s.db entry.id == lit)))
      (learned.map (moveWatchEntry entry.id offset (s.db entry.id == lit))) := by
  have packed := database.layout.packed member
  have headBound : entry.id + 1 < s.arena.size := by have := packed.endBound; omega
  have posBound : entry.id + offset < s.arena.size := by have := packed.endBound; omega
  rw [moveWatch_eq_swaps _ _ _ _ headBound (by omega) posBound watched]
  by_cases first : s.db entry.id = lit
  · have firstArray : s.arena[entry.id]! = lit := first
    have test : (s.arena[entry.id]! == lit) = true := by simpa only [beq_iff_eq] using firstArray
    have initial := database.swapLiterals member 0 1 (by omega) (by omega)
    have mappedMember : swapEntry entry.id 0 1 entry ∈
        original.map (swapEntry entry.id 0 1) ++ learned.map (swapEntry entry.id 0 1) := by
      rw [← List.map_append]
      exact List.mem_map.mpr ⟨entry, member, rfl⟩
    have final := initial.swapLiterals mappedMember 1 offset (by simpa using (show 1 < entry.lits.size by omega))
      (by simpa using within)
    simpa only [State.db, test, ite_true, Nat.add_zero,
      swapEntry_id, List.map_map, Function.comp_def, moveWatchEntry_true] using final
  · have final := database.swapLiterals member 1 offset (by omega) within
    have firstArray : ¬s.arena[entry.id]! = lit := first
    have test : (s.arena[entry.id]! == lit) = false := by simp [firstArray]
    simpa only [State.db, test, Bool.false_eq_true, ite_false, moveWatchEntry_false] using final

theorem moveWatch_databaseMeaning {formula : Std.Sat.CNF Nat} {original learned : List StoredClause}
    (meaning : DatabaseMeaning formula original learned) (id offset : Nat) (first : Bool) :
    DatabaseMeaning formula (original.map (moveWatchEntry id offset first))
      (learned.map (moveWatchEntry id offset first)) := by
  cases first
  · simpa only [moveWatchEntry_false] using meaning.swapLiterals id 1 offset
  · simpa only [moveWatchEntry_true, List.map_map, Function.comp_def] using
      (meaning.swapLiterals id 0 1).swapLiterals id 1 offset

private theorem replacementScan_set_before (fuel : Nat) (arena marks : Array Nat)
    (index value start : Nat) (before : index < start) :
    replacementScan fuel (arena.set! index value) marks start = replacementScan fuel arena marks start := by
  induction fuel generalizing start with
  | zero => rfl
  | succ fuel ih =>
    simp only [replacementScan, Array.getElem!_set!_ne _ _ _ _ (by omega : index ≠ start)]
    split
    · rfl
    · split
      · rfl
      · exact ih (start + 1) (by omega)

theorem replacement_set_before (arena marks : Array Nat) (id index value : Nat)
    (before : index < id + 2) :
    replacement (arena.set! index value) marks id = replacement arena marks id := by
  simp only [replacement, Array.size_set!]
  exact replacementScan_set_before _ _ _ _ _ _ before

theorem replacement_orientWatch (arena marks : Array Nat) (id : Nat) (lit : Lit) :
    replacement (orientWatch arena id lit) marks id = replacement arena marks id := by
  unfold orientWatch
  split
  · simp only [replacement, Array.size_set!]
    exact replacementScan_set_before _ _ _ _ _ _ (by omega)
  · rfl

theorem orientWatch_read_other (arena : Array Nat) (id : Nat) (lit : Lit) (pos : Nat)
    (different : id ≠ pos) : (orientWatch arena id lit)[pos]! = arena[pos]! := by
  unfold orientWatch
  split
  · exact Array.getElem!_set!_ne _ _ _ _ different
  · rfl

theorem replacement_orientWatch_some {s : State} {entry : StoredClause}
    (packed : PackedClause s entry.id entry.lits) (wide : 2 ≤ entry.lits.size)
    (lit : Lit) {pos : Nat}
    (found : replacement (orientWatch s.arena entry.id lit) s.marks entry.id = some pos) :
    ∃ offset, 2 ≤ offset ∧ offset < entry.lits.size ∧ pos = entry.id + offset ∧
      s.mark entry.lits[offset]! = 0 := by
  rw [replacement_orientWatch] at found
  exact replacement_some_of_packed packed wide found

end MicrosatLean.Verification.Implementation.Native.Propagation
