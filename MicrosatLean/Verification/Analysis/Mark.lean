import MicrosatLean.CDCL.Analysis
import MicrosatLean.Verification.Representation.Heuristic
import MicrosatLean.Verification.Representation.Arena

namespace MicrosatLean.Verification.Analysis

open CDCL Representation

private def markScan : Nat → State → Nat → State
  | 0, s, _ => s
  | fuel + 1, s, start =>
    if s.db start = 0 then s else markScan fuel (s.bump (s.db start)) (start + 1)

private def markLoop (s : State) (start count : Nat) : State := Id.run do
  let mut s := s
  for i in [start:start + count] do
    let lit := s.db i
    if lit == 0 then break
    s := s.bump lit
  return s

private theorem markLoop_eq (count : Nat) (s : State) (start : Nat) :
    markLoop s start count = markScan count s start := by
  induction count generalizing s start with
  | zero => simp [markLoop, Std.Legacy.Range.forIn_eq_forIn_range', markScan]
  | succ count ih =>
    simp only [markLoop, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
    rw [show start + (count + 1) - start = count + 1 by omega]
    simp only [List.range'_succ, List.forIn_cons, markScan]
    by_cases zero : s.db start = 0
    · simp [zero]
    · have tail := ih (s.bump (s.db start)) (start + 1)
      simpa [markLoop, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, zero] using tail

private theorem markClause_eq_scan (s : State) (start : Nat) :
    markClause s start = markScan (s.arena.size - start) s start := by
  have loop := markLoop_eq (s.arena.size - start) s start
  simpa [markLoop, markClause, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using loop

private theorem bumpFrame_refl (s : State) : BumpFrame s s := ⟨rfl, rfl, rfl, rfl⟩

private theorem bumpFrame_trans {first middle last : State}
    (before : BumpFrame first middle) (after : BumpFrame middle last) : BumpFrame first last := by
  constructor
  · exact (congrArg (fun s : State => { s with
      marks := first.marks
      previous := first.previous
      next := first.next
      head := first.head }) after.restore).trans before.restore
  · exact after.marksSize.trans before.marksSize
  · exact after.previousSize.trans before.previousSize
  · exact after.nextSize.trans before.nextSize

private theorem markScan_frame (fuel : Nat) (s : State) (start : Nat) :
    BumpFrame s (markScan fuel s start) := by
  induction fuel generalizing s start with
  | zero => exact bumpFrame_refl s
  | succ fuel ih =>
    unfold markScan
    split
    · exact bumpFrame_refl s
    · exact bumpFrame_trans (bump_frame s _) (ih _ _)

/-- The actual clause-marking loop retains all fields except analysis marks
and heuristic links/head; all affected array dimensions are retained too. -/
theorem markClause_frame (s : State) (start : Nat) : BumpFrame s (markClause s start) := by
  rw [markClause_eq_scan]
  exact markScan_frame _ _ _

private def bumpList : State → List Lit → State
  | s, [] => s
  | s, lit :: tail => bumpList (s.bump lit) tail

private theorem markScan_words (words : List Lit) (s : State) (start fuel : Nat)
    (nonzero : ∀ lit ∈ words, lit ≠ 0)
    (values : ∀ i, i < words.length → s.db (start + i) = words[i]!)
    (terminator : s.db (start + words.length) = 0) (enough : words.length < fuel) :
    markScan fuel s start = bumpList s words := by
  induction words generalizing s start fuel with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have zero : s.db start = 0 := by simpa using terminator
      simp [markScan, bumpList, zero]
  | cons lit tail ih =>
    cases fuel with
    | zero => simp only [List.length_cons] at enough; omega
    | succ fuel =>
      have head : s.db start = lit := by simpa using values 0 (by simp)
      have notZero := nonzero lit (by simp)
      simp only [markScan, head, ite_eq_right notZero, bumpList]
      apply ih
      · exact fun word member => nonzero word (List.mem_cons_of_mem lit member)
      · intro i bound
        have old := values (i + 1) (by simp only [List.length_cons]; omega)
        simpa [State.db, List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using old
      · simpa [State.db, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using terminator
      · simp only [List.length_cons] at enough
        omega

private theorem suffix_get (lits : Array Lit) (offset i : Nat) :
    (lits.toList.drop offset)[i]! = lits[offset + i]! := by
  simp [List.getElem!_eq_getElem?_getD, List.getElem?_drop,
    Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]

private theorem markClause_suffix_eq {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) (offset : Nat) (inside : offset ≤ lits.size) :
    markClause s (clauseId + offset) = bumpList s (lits.toList.drop offset) := by
  rw [markClause_eq_scan]
  apply markScan_words
  · intro lit member
    have original : lit ∈ lits := by simpa using List.mem_of_mem_drop member
    exact (packed.wellFormed lit original).nonzero
  · intro i bound
    simp only [List.length_drop, Array.length_toList] at bound
    rw [suffix_get]
    simpa only [Nat.add_assoc] using packed.literals (offset + i) (by omega)
  · have endIndex : clauseId + offset + (lits.toList.drop offset).length = clauseId + lits.size := by
      simp only [List.length_drop, Array.length_toList]
      omega
    rw [endIndex]
    exact packed.terminator
  · have endBound := packed.endBound
    simp only [List.length_drop, Array.length_toList]
    omega

private theorem bump_mark_formula (s : State) (target query : Lit) (bound : target < s.marks.size) :
    (s.bump target).mark query = if target = query ∧ s.mark query ≠ 6 then 2 else s.mark query := by
  have marks : (s.bump target).marks = if s.mark target = 6 then s.marks else s.marks.set! target 2 := by
    by_cases root : s.mark target = 6 <;> by_cases head : target.var = s.head <;>
      simp [State.bump, State.setMark, root, head]
  by_cases same : target = query
  · subst query
    by_cases root : s.mark target = 6
    · simp [bump_eq_of_root root, root]
    · unfold State.mark
      rw [marks, ite_eq_right root]
      have plain : s.marks[target]! ≠ 6 := root
      simpa [plain] using Array.getElem!_set!_self s.marks target 2 bound
  · by_cases root : s.mark target = 6
    · simp [bump_eq_of_root root, same]
    · unfold State.mark
      rw [marks, ite_eq_right root, Array.getElem!_set!_ne _ _ _ _ same]
      simp [same]

private theorem bumpList_marks (words : List Lit) (s : State) (query : Lit)
    (bounded : ∀ lit ∈ words, lit < s.marks.size) :
    (bumpList s words).mark query = if query ∈ words ∧ s.mark query ≠ 6 then 2 else s.mark query := by
  induction words generalizing s with
  | nil => simp [bumpList]
  | cons lit tail ih =>
    rw [bumpList, ih _ (by
      intro word member
      simpa using bounded word (List.mem_cons_of_mem lit member))]
    rw [bump_mark_formula s lit query (bounded lit (by simp))]
    by_cases same : lit = query
    · subst query
      by_cases member : lit ∈ tail <;> by_cases root : s.mark lit = 6 <;> simp [member, root]
    · have reverse : query ≠ lit := Ne.symm same
      by_cases member : query ∈ tail <;> by_cases root : s.mark query = 6 <;>
        simp [same, reverse, member, root]

/-- Exact mark update for the actual scan of a terminated packed-clause
suffix. Existing root tag six is retained, even when that literal occurs. -/
theorem markClause_mark_suffix {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) (arrays : ArrayBounds s)
    (offset : Nat) (inside : offset ≤ lits.size) (query : Lit) :
    (markClause s (clauseId + offset)).mark query =
      if query ∈ lits.toList.drop offset ∧ s.mark query ≠ 6 then 2 else s.mark query := by
  rw [markClause_suffix_eq packed offset inside]
  apply bumpList_marks
  intro lit member
  have original : lit ∈ lits := by simpa using List.mem_of_mem_drop member
  exact (arrays.literal_index (packed.wellFormed lit original)).1

theorem markClause_mark_member {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) (arrays : ArrayBounds s)
    (offset : Nat) (inside : offset ≤ lits.size) {query : Lit}
    (member : query ∈ lits.toList.drop offset) (nonroot : s.mark query ≠ 6) :
    (markClause s (clauseId + offset)).mark query = 2 := by
  rw [markClause_mark_suffix packed arrays offset inside]
  simp [member, nonroot]

theorem markClause_mark_root {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) (arrays : ArrayBounds s)
    (offset : Nat) (inside : offset ≤ lits.size) {query : Lit} (root : s.mark query = 6) :
    (markClause s (clauseId + offset)).mark query = 6 := by
  rw [markClause_mark_suffix packed arrays offset inside]
  simp [root]

theorem markClause_mark_outside {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) (arrays : ArrayBounds s)
    (offset : Nat) (inside : offset ≤ lits.size) {query : Lit}
    (outside : query ∉ lits.toList.drop offset) :
    (markClause s (clauseId + offset)).mark query = s.mark query := by
  rw [markClause_mark_suffix packed arrays offset inside]
  simp [outside]

/-- Marking adds precisely the nonroot suffix literals to the old MARK set. -/
theorem markClause_mark_two_iff {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) (arrays : ArrayBounds s)
    (offset : Nat) (inside : offset ≤ lits.size) (query : Lit) :
    (markClause s (clauseId + offset)).mark query = 2 ↔
      s.mark query = 2 ∨ (query ∈ lits.toList.drop offset ∧ s.mark query ≠ 6) := by
  rw [markClause_mark_suffix packed arrays offset inside]
  by_cases changed : query ∈ lits.toList.drop offset ∧ s.mark query ≠ 6 <;> simp [changed]

theorem markClause_mark_six_iff {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) (arrays : ArrayBounds s)
    (offset : Nat) (inside : offset ≤ lits.size) (query : Lit) :
    (markClause s (clauseId + offset)).mark query = 6 ↔ s.mark query = 6 := by
  rw [markClause_mark_suffix packed arrays offset inside]
  by_cases changed : query ∈ lits.toList.drop offset ∧ s.mark query ≠ 6
  · simp [changed]
  · simp [changed]

theorem markClause_terminator {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) : markClause s (clauseId + lits.size) = s := by
  rw [markClause_suffix_eq packed lits.size (Nat.le_refl _)]
  have empty : lits.toList.drop lits.size = [] := List.drop_eq_nil_of_le (by simp)
  rw [empty]
  rfl

private theorem bumpList_mtf (words : List Lit) (s : State) (arrays : ArrayBounds s)
    (coverage : MTFCoverage s) (bounded : ∀ lit ∈ words, LiteralBound s.nVars lit) :
    MTFCoverage (bumpList s words) := by
  induction words generalizing s with
  | nil => exact coverage
  | cons lit tail ih =>
    apply ih (s.bump lit) arrays.bump (coverage.bump arrays (bounded lit (by simp)))
    intro word member
    simpa using bounded word (List.mem_cons_of_mem lit member)

theorem markClause_mtf {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) (arrays : ArrayBounds s) (coverage : MTFCoverage s)
    (offset : Nat) (inside : offset ≤ lits.size) : MTFCoverage (markClause s (clauseId + offset)) := by
  rw [markClause_suffix_eq packed offset inside]
  apply bumpList_mtf _ _ arrays coverage
  intro lit member
  have original : lit ∈ lits := by simpa using List.mem_of_mem_drop member
  exact packed.wellFormed lit original

theorem markClause_arrayBounds (s : State) (start : Nat) (arrays : ArrayBounds s) :
    ArrayBounds (markClause s start) := by
  have frame := markClause_frame s start
  have restored : ArrayBounds { markClause s start with
      marks := s.marks, previous := s.previous, next := s.next, head := s.head } := by
    rw [frame.restore]
    exact arrays
  exact ⟨restored.firstSize, frame.marksSize.trans restored.marksSize,
    restored.reasonsSize, restored.phasesSize, restored.trailSize,
    frame.previousSize.trans restored.previousSize, frame.nextSize.trans restored.nextSize⟩

@[simp] theorem markClause_arena (s : State) (start : Nat) : (markClause s start).arena = s.arena := by
  simpa using congrArg State.arena (markClause_frame s start).restore

@[simp] theorem markClause_reasons (s : State) (start : Nat) : (markClause s start).reasons = s.reasons := by
  simpa using congrArg State.reasons (markClause_frame s start).restore

@[simp] theorem markClause_phases (s : State) (start : Nat) : (markClause s start).phases = s.phases := by
  simpa using congrArg State.phases (markClause_frame s start).restore

@[simp] theorem markClause_trail (s : State) (start : Nat) : (markClause s start).trail = s.trail := by
  simpa using congrArg State.trail (markClause_frame s start).restore

@[simp] theorem markClause_assigned (s : State) (start : Nat) : (markClause s start).assigned = s.assigned := by
  simpa using congrArg State.assigned (markClause_frame s start).restore

@[simp] theorem markClause_processed (s : State) (start : Nat) : (markClause s start).processed = s.processed := by
  simpa using congrArg State.processed (markClause_frame s start).restore

@[simp] theorem markClause_forced (s : State) (start : Nat) : (markClause s start).forced = s.forced := by
  simpa using congrArg State.forced (markClause_frame s start).restore

end MicrosatLean.Verification.Analysis
