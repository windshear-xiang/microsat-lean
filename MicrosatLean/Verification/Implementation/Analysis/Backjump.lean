import MicrosatLean.Verification.Implementation.Representation.State

namespace MicrosatLean.Verification.Implementation.Analysis

open CDCL Representation

private def clearMany : Nat → State → Nat → Nat → State
  | 0, s, _, _ => s
  | count + 1, s, candidate, offset =>
    clearMany count (s.unassign s.trail[candidate - offset]!) candidate (offset + 1)

private def clearLoop (s : State) (candidate start count : Nat) : State := Id.run do
  let mut s := s
  for offset in [start:start + count] do
    s := s.unassign s.trail[candidate - offset]!
  return s

private theorem clearLoop_eq (count : Nat) (s : State) (candidate start : Nat) :
    clearLoop s candidate start count = clearMany count s candidate start := by
  induction count generalizing s start with
  | zero => simp [clearLoop, Std.Legacy.Range.forIn_eq_forIn_range', clearMany]
  | succ count ih =>
    simp only [clearLoop, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
    rw [show start + (count + 1) - start = count + 1 by omega]
    simp only [List.range'_succ, List.forIn_cons, clearMany]
    have tail := ih (s.unassign s.trail[candidate - start]!) (start + 1)
    simpa [clearLoop, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size] using tail

private theorem backjump_eq (s : State) (candidate : Nat) : backjump s candidate =
    let after := clearMany (candidate + 1 - s.processed) s candidate 0
    { after with assigned := after.processed } := by
  have loop := clearLoop_eq (candidate + 1 - s.processed) s candidate 0
  simp only [clearLoop, Nat.zero_add, Id.run, bind, pure] at loop
  simp only [backjump, Id.run, bind, pure, loop]

private theorem clearMany_restore (count : Nat) (s : State) (candidate offset : Nat) :
    { clearMany count s candidate offset with marks := s.marks } = s := by
  induction count generalizing s offset with
  | zero => rfl
  | succ count ih =>
    have restored := congrArg (fun after : State => { after with marks := s.marks })
      (ih (s.unassign s.trail[candidate - offset]!) (offset + 1))
    simpa only [clearMany, State.unassign, State.setMark] using restored

private theorem clearMany_marks_size (count : Nat) (s : State) (candidate offset : Nat) :
    (clearMany count s candidate offset).marks.size = s.marks.size := by
  induction count generalizing s offset with
  | zero => rfl
  | succ count ih =>
    simpa [clearMany, State.unassign, State.setMark] using
      ih (s.unassign s.trail[candidate - offset]!) (offset + 1)

private theorem unassign_preserves_zero (s : State) (clear lit : Lit) (zero : s.mark lit = 0) :
    (s.unassign clear).mark lit = 0 := by
  by_cases same : clear = lit
  · subst clear
    by_cases bound : lit < s.marks.size
    · exact unassign_mark_same bound
    · simp [State.unassign, State.setMark, State.mark, Array.setIfInBounds, bound]
  · rw [unassign_mark_other same]
    exact zero

private theorem clearMany_preserves_zero (count : Nat) (s : State) (candidate offset : Nat)
    (lit : Lit) (zero : s.mark lit = 0) : (clearMany count s candidate offset).mark lit = 0 := by
  induction count generalizing s offset with
  | zero => exact zero
  | succ count ih =>
    exact ih _ _ (unassign_preserves_zero s _ lit zero)

private theorem clearMany_mark_unchanged (count : Nat) (s : State) (candidate start : Nat)
    (lit : Lit)
    (different : ∀ offset, start ≤ offset → offset < start + count →
      s.trail[candidate - offset]! ≠ lit) :
    (clearMany count s candidate start).mark lit = s.mark lit := by
  induction count generalizing s start with
  | zero => rfl
  | succ count ih =>
    have current := different start (Nat.le_refl _) (by omega)
    have tail := ih (s.unassign s.trail[candidate - start]!) (start + 1) (by
      intro offset lower upper
      exact different offset (by omega) (by omega))
    change (clearMany count (s.unassign s.trail[candidate - start]!) candidate
      (start + 1)).mark lit = s.mark lit
    rw [tail]
    exact unassign_mark_other current

private theorem clearMany_mark_cleared (count : Nat) (s : State) (candidate start offset : Nat)
    (lower : start ≤ offset) (upper : offset < start + count)
    (bound : s.trail[candidate - offset]! < s.marks.size) :
    (clearMany count s candidate start).mark s.trail[candidate - offset]! = 0 := by
  induction count generalizing s start with
  | zero => omega
  | succ count ih =>
    by_cases first : offset = start
    · subst offset
      exact clearMany_preserves_zero count (s.unassign s.trail[candidate - start]!)
        candidate (start + 1) _ (unassign_mark_same bound)
    · apply ih (s.unassign s.trail[candidate - start]!) (start + 1) (by omega) (by omega)
      simpa [State.unassign, State.setMark] using bound

/-- Backjump changes only marks and the assignment cursor. In particular,
the fixed-capacity trail and every propagation/reason/heuristic field remain. -/
structure BackjumpFrame (before after : State) : Prop where
  restore : { after with marks := before.marks, assigned := before.assigned } = before
  marksSize : after.marks.size = before.marks.size

theorem backjump_frame (s : State) (candidate : Nat) : BackjumpFrame s (backjump s candidate) := by
  constructor
  · rw [backjump_eq]
    have restored := congrArg (fun after : State => { after with assigned := s.assigned })
      (clearMany_restore (candidate + 1 - s.processed) s candidate 0)
    exact restored
  · rw [backjump_eq]
    exact clearMany_marks_size _ _ _ _

variable {s : State} {candidate : Nat}

@[simp] theorem backjump_nVars : (backjump s candidate).nVars = s.nVars := by
  simpa using congrArg State.nVars (backjump_frame s candidate).restore

@[simp] theorem backjump_arena : (backjump s candidate).arena = s.arena := by
  simpa using congrArg State.arena (backjump_frame s candidate).restore

@[simp] theorem backjump_first : (backjump s candidate).first = s.first := by
  simpa using congrArg State.first (backjump_frame s candidate).restore

@[simp] theorem backjump_reasons : (backjump s candidate).reasons = s.reasons := by
  simpa using congrArg State.reasons (backjump_frame s candidate).restore

@[simp] theorem backjump_phases : (backjump s candidate).phases = s.phases := by
  simpa using congrArg State.phases (backjump_frame s candidate).restore

@[simp] theorem backjump_trail : (backjump s candidate).trail = s.trail := by
  simpa using congrArg State.trail (backjump_frame s candidate).restore

@[simp] theorem backjump_processed : (backjump s candidate).processed = s.processed := by
  simpa using congrArg State.processed (backjump_frame s candidate).restore

@[simp] theorem backjump_forced : (backjump s candidate).forced = s.forced := by
  simpa using congrArg State.forced (backjump_frame s candidate).restore

@[simp] theorem backjump_previous : (backjump s candidate).previous = s.previous := by
  simpa using congrArg State.previous (backjump_frame s candidate).restore

@[simp] theorem backjump_next : (backjump s candidate).next = s.next := by
  simpa using congrArg State.next (backjump_frame s candidate).restore

@[simp] theorem backjump_head : (backjump s candidate).head = s.head := by
  simpa using congrArg State.head (backjump_frame s candidate).restore

@[simp] theorem backjump_fixed : (backjump s candidate).fixed = s.fixed := by
  simpa using congrArg State.fixed (backjump_frame s candidate).restore

@[simp] theorem backjump_marks_size : (backjump s candidate).marks.size = s.marks.size :=
  (backjump_frame s candidate).marksSize

@[simp] theorem backjump_assigned : (backjump s candidate).assigned = s.processed := by
  rw [backjump_eq]
  simpa using congrArg State.processed (clearMany_restore (candidate + 1 - s.processed) s candidate 0)

theorem backjump_mark_unmarked {lit : Lit} (zero : s.mark lit = 0) :
    (backjump s candidate).mark lit = 0 := by
  rw [backjump_eq]
  exact clearMany_preserves_zero _ _ _ _ _ zero

/-- Marks outside the inclusive interval from the processed cursor to the
candidate retain their exact analysis tag. -/
theorem backjump_mark_unchanged {lit : Lit}
    (different : ∀ i, s.processed ≤ i → i ≤ candidate → s.trail[i]! ≠ lit) :
    (backjump s candidate).mark lit = s.mark lit := by
  rw [backjump_eq]
  apply clearMany_mark_unchanged
  intro offset _ upper
  exact different (candidate - offset) (by omega) (Nat.sub_le _ _)

/-- The analyzed candidate is still active while `assigned` temporarily
contains its index. Therefore the premise includes `candidate + 1` entries. -/
theorem backjump_mark_cleared (arrays : ArrayBounds s)
    (active : ActiveTrail { s with assigned := candidate + 1 }) (i : Nat)
    (lower : s.processed ≤ i) (upper : i ≤ candidate) :
    (backjump s candidate).mark s.trail[i]! = 0 := by
  rw [backjump_eq]
  have index : candidate - (candidate - i) = i := by omega
  have bound : s.trail[candidate - (candidate - i)]! < s.marks.size := by
    rw [index]
    exact (arrays.literal_index (active i (by dsimp; omega)).1).1
  have cleared := clearMany_mark_cleared (candidate + 1 - s.processed) s candidate 0
    (candidate - i) (Nat.zero_le _) (by omega) bound
  simpa only [index, State.mark] using cleared

theorem backjump_mark_prefix (cursor : s.processed ≤ candidate + 1)
    (distinct : DistinctTrailVariables { s with assigned := candidate + 1 })
    (i : Nat) (before : i < s.processed) :
    (backjump s candidate).mark s.trail[i]! = s.mark s.trail[i]! := by
  apply backjump_mark_unchanged
  intro j lower upper equal
  have same := distinct j i (by dsimp; omega) (by dsimp; omega) (congrArg Lit.var equal)
  omega

theorem backjump_mark_prefix_negate (cursor : s.processed ≤ candidate + 1)
    (distinct : DistinctTrailVariables { s with assigned := candidate + 1 })
    (i : Nat) (before : i < s.processed) :
    (backjump s candidate).mark s.trail[i]!.negate = s.mark s.trail[i]!.negate := by
  apply backjump_mark_unchanged
  intro j lower upper equal
  have variableEqual : s.trail[j]!.var = s.trail[i]!.var := by
    simpa using congrArg Lit.var equal
  have same := distinct j i (by dsimp; omega) (by dsimp; omega) variableEqual
  omega

/-- If every analysis mark is covered by the candidate-inclusive trail, every
remaining mark after backjump is covered by the retained prefix. -/
theorem backjump_marked_prefix (arrays : ArrayBounds s)
    (active : ActiveTrail { s with assigned := candidate + 1 })
    (coverage : ∀ lit, s.mark lit ≠ 0 → ∃ i, i < candidate + 1 ∧ s.trail[i]! = lit)
    (lit : Lit) (marked : (backjump s candidate).mark lit ≠ 0) :
    ∃ i, i < s.processed ∧ s.trail[i]! = lit := by
  have old : s.mark lit ≠ 0 := fun zero => marked (backjump_mark_unmarked zero)
  obtain ⟨i, before, equal⟩ := coverage lit old
  refine ⟨i, ?_, equal⟩
  by_cases retained : i < s.processed
  · exact retained
  · have cleared := backjump_mark_cleared arrays active i (by omega) (by omega)
    rw [equal] at cleared
    exact False.elim (marked cleared)

theorem backjump_arrayBounds (arrays : ArrayBounds s) : ArrayBounds (backjump s candidate) := by
  constructor <;> simp_all [arrays.firstSize, arrays.marksSize, arrays.reasonsSize,
    arrays.phasesSize, arrays.trailSize, arrays.previousSize, arrays.nextSize]

theorem backjump_trailBounds (forced : s.forced ≤ s.processed) (bound : s.processed ≤ s.nVars) :
    TrailBounds (backjump s candidate) := by
  constructor <;> simp_all

theorem backjump_trailPhases
    (phases : TrailPhases { s with assigned := candidate + 1 })
    (cursor : s.processed ≤ candidate + 1) : TrailPhases (backjump s candidate) := by
  intro i before
  rw [backjump_assigned] at before
  simpa using phases i (by dsimp; omega)

theorem backjump_distinctTrailVariables
    (distinct : DistinctTrailVariables { s with assigned := candidate + 1 })
    (cursor : s.processed ≤ candidate + 1) : DistinctTrailVariables (backjump s candidate) := by
  intro i j beforeI beforeJ same
  rw [backjump_assigned] at beforeI beforeJ
  apply distinct i j (by dsimp; omega) (by dsimp; omega)
  simpa using same

theorem backjump_activeTrail (active : ActiveTrail { s with assigned := candidate + 1 })
    (distinct : DistinctTrailVariables { s with assigned := candidate + 1 })
    (cursor : s.processed ≤ candidate + 1) : ActiveTrail (backjump s candidate) := by
  intro i before
  rw [backjump_assigned] at before
  have old := active i (by dsimp; omega)
  rw [backjump_trail]
  constructor
  · simpa using old.1
  · constructor
    · rw [backjump_mark_prefix cursor distinct i before]
      exact old.2.1
    · rw [backjump_mark_prefix_negate cursor distinct i before]
      exact old.2.2

theorem backjump_mtfOrder {order : List Nat} (ordered : MTFOrder s order) :
    MTFOrder (backjump s candidate) order := by
  simpa [MTFOrder] using ordered

theorem backjump_mtfCoverage (coverage : MTFCoverage s) : MTFCoverage (backjump s candidate) := by
  obtain ⟨order, ordered⟩ := coverage
  exact ⟨order, backjump_mtfOrder ordered⟩

end MicrosatLean.Verification.Implementation.Analysis
