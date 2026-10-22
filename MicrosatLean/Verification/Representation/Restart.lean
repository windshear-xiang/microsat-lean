import MicrosatLean.Verification.Representation.State

namespace MicrosatLean.Verification.Representation

open CDCL

private def popOne (s : State) : State :=
  { s.unassign s.trail[s.assigned - 1]! with assigned := s.assigned - 1 }

private def popMany : Nat → State → State
  | 0, s => s
  | fuel + 1, s => popMany fuel (popOne s)

private def popLoop (s : State) (start count : Nat) : State := Id.run do
  let mut s := s
  for _ in [start:start + count] do
    let idx := s.assigned - 1
    s := { s.unassign s.trail[idx]! with assigned := idx }
  return s

private theorem popLoop_eq (count : Nat) (s : State) (start : Nat) :
    popLoop s start count = popMany count s := by
  induction count generalizing s start with
  | zero => simp [popLoop, Std.Legacy.Range.forIn_eq_forIn_range', popMany]
  | succ count ih =>
    simp only [popLoop, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
    rw [show start + (count + 1) - start = count + 1 by omega]
    simp only [List.range'_succ, List.forIn_cons, popMany]
    have tail := ih (popOne s) (start + 1)
    simpa [popLoop, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, popOne] using tail

private theorem restart_eq (s : State) : s.restart =
    let after := popMany (s.assigned - s.forced) s
    { after with
      processed := after.forced
      stats := { after.stats with restarts := after.stats.restarts + 1 } } := by
  have loop := popLoop_eq (s.assigned - s.forced) s 0
  simp only [popLoop, Nat.zero_add, Id.run, bind, pure] at loop
  simp only [State.restart, Id.run, bind, pure, loop]

private theorem popMany_restore (fuel : Nat) (s : State) :
    { popMany fuel s with marks := s.marks, assigned := s.assigned } = s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    have restored := congrArg
      (fun after : State => { after with marks := s.marks, assigned := s.assigned }) (ih (popOne s))
    simpa only [popMany, popOne, State.unassign, State.setMark] using restored

private theorem popMany_marks_size (fuel : Nat) (s : State) :
    (popMany fuel s).marks.size = s.marks.size := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih => simpa [popMany, popOne, State.unassign, State.setMark] using ih (popOne s)

private theorem popMany_assigned (fuel : Nat) (s : State) :
    (popMany fuel s).assigned = s.assigned - fuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simpa [popMany, popOne, Nat.sub_sub, Nat.add_comm] using ih (popOne s)

private theorem unassign_preserves_zero (s : State) (clear lit : Lit) (zero : s.mark lit = 0) :
    (s.unassign clear).mark lit = 0 := by
  by_cases same : clear = lit
  · subst clear
    by_cases bound : lit < s.marks.size
    · exact unassign_mark_same bound
    · simp [State.unassign, State.setMark, State.mark, Array.setIfInBounds, bound]
  · rw [unassign_mark_other same]
    exact zero

private theorem popMany_preserves_zero (fuel : Nat) (s : State) (lit : Lit) (zero : s.mark lit = 0) :
    (popMany fuel s).mark lit = 0 := by
  induction fuel generalizing s with
  | zero => exact zero
  | succ fuel ih =>
    apply ih (popOne s)
    exact unassign_preserves_zero s _ lit zero

private theorem popMany_mark_unchanged (fuel : Nat) (s : State) (lit : Lit)
    (enough : fuel ≤ s.assigned)
    (different : ∀ i, s.assigned - fuel ≤ i → i < s.assigned → s.trail[i]! ≠ lit) :
    (popMany fuel s).mark lit = s.mark lit := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    have current : s.trail[s.assigned - 1]! ≠ lit :=
      different _ (by omega) (by omega)
    have tail := ih (popOne s) (by dsimp [popOne]; omega) (by
      intro i lower upper
      apply different i
      · dsimp [popOne] at lower
        omega
      · dsimp [popOne] at upper
        omega)
    change (popMany fuel (popOne s)).mark lit = s.mark lit
    rw [tail]
    exact unassign_mark_other current

private theorem popMany_mark_cleared (fuel : Nat) (s : State) (i : Nat)
    (enough : fuel ≤ s.assigned)
    (indices : ∀ j, j < s.assigned → s.trail[j]! < s.marks.size)
    (lower : s.assigned - fuel ≤ i) (upper : i < s.assigned) :
    (popMany fuel s).mark s.trail[i]! = 0 := by
  induction fuel generalizing s with
  | zero => omega
  | succ fuel ih =>
    by_cases top : i = s.assigned - 1
    · subst i
      apply popMany_preserves_zero fuel (popOne s)
      exact unassign_mark_same (indices _ upper)
    · apply ih (popOne s)
      · dsimp [popOne]
        omega
      · intro j bound
        have old : j < s.assigned := by dsimp [popOne] at bound; omega
        simpa [popOne, State.unassign, State.setMark] using indices j old
      · dsimp [popOne]
        omega
      · dsimp [popOne]
        omega

/-- Restart changes only marks, assignment/propagation cursors, and statistics.
All other fields are retained exactly, even for malformed input states. -/
structure RestartFrame (before after : State) : Prop where
  restore : { after with
    marks := before.marks
    assigned := before.assigned
    processed := before.processed
    stats := before.stats } = before
  marksSize : after.marks.size = before.marks.size

theorem restart_frame (s : State) : RestartFrame s s.restart := by
  constructor
  · rw [restart_eq]
    have restored := congrArg
      (fun after : State => { after with processed := s.processed, stats := s.stats })
      (popMany_restore (s.assigned - s.forced) s)
    exact restored
  · rw [restart_eq]
    exact popMany_marks_size _ _

variable {s : State}

@[simp] theorem restart_nVars : s.restart.nVars = s.nVars := by
  simpa using congrArg State.nVars (restart_frame s).restore

@[simp] theorem restart_arena : s.restart.arena = s.arena := by
  simpa using congrArg State.arena (restart_frame s).restore

@[simp] theorem restart_first : s.restart.first = s.first := by
  simpa using congrArg State.first (restart_frame s).restore

@[simp] theorem restart_reasons : s.restart.reasons = s.reasons := by
  simpa using congrArg State.reasons (restart_frame s).restore

@[simp] theorem restart_phases : s.restart.phases = s.phases := by
  simpa using congrArg State.phases (restart_frame s).restore

@[simp] theorem restart_trail : s.restart.trail = s.trail := by
  simpa using congrArg State.trail (restart_frame s).restore

@[simp] theorem restart_forced : s.restart.forced = s.forced := by
  simpa using congrArg State.forced (restart_frame s).restore

@[simp] theorem restart_previous : s.restart.previous = s.previous := by
  simpa using congrArg State.previous (restart_frame s).restore

@[simp] theorem restart_next : s.restart.next = s.next := by
  simpa using congrArg State.next (restart_frame s).restore

@[simp] theorem restart_head : s.restart.head = s.head := by
  simpa using congrArg State.head (restart_frame s).restore

@[simp] theorem restart_fixed : s.restart.fixed = s.fixed := by
  simpa using congrArg State.fixed (restart_frame s).restore

@[simp] theorem restart_marks_size : s.restart.marks.size = s.marks.size :=
  (restart_frame s).marksSize

@[simp] theorem restart_processed : s.restart.processed = s.forced := by
  rw [restart_eq]
  have restored := congrArg State.forced (popMany_restore (s.assigned - s.forced) s)
  simpa using restored

theorem restart_assigned (bounds : TrailBounds s) : s.restart.assigned = s.forced := by
  rw [restart_eq]
  have cursor := popMany_assigned (s.assigned - s.forced) s
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  simpa [Nat.sub_sub_self forced] using cursor

theorem restart_stats : s.restart.stats = { s.stats with restarts := s.stats.restarts + 1 } := by
  rw [restart_eq]
  have stable := congrArg State.stats (popMany_restore (s.assigned - s.forced) s)
  dsimp only at stable ⊢
  rw [stable]

theorem restart_trail_prefix (bounds : TrailBounds s) :
    s.restart.trail.extract 0 s.restart.assigned = s.trail.extract 0 s.forced := by
  rw [restart_trail, restart_assigned bounds]

theorem restart_mark_unmarked {lit : Lit} (zero : s.mark lit = 0) : s.restart.mark lit = 0 := by
  rw [restart_eq]
  exact popMany_preserves_zero _ s lit zero

theorem restart_mark_unchanged {lit : Lit} (bounds : TrailBounds s)
    (different : ∀ i, s.forced ≤ i → i < s.assigned → s.trail[i]! ≠ lit) :
    s.restart.mark lit = s.mark lit := by
  rw [restart_eq]
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  apply popMany_mark_unchanged _ s lit (Nat.sub_le _ _)
  simpa [Nat.sub_sub_self forced] using different

theorem restart_mark_cleared (arrays : ArrayBounds s) (bounds : TrailBounds s)
    (active : ActiveTrail s) (i : Nat) (nonroot : s.forced ≤ i) (before : i < s.assigned) :
    s.restart.mark s.trail[i]! = 0 := by
  rw [restart_eq]
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  apply popMany_mark_cleared _ s i (Nat.sub_le _ _)
  · exact fun j hj => (arrays.literal_index (active j hj).1).1
  · simpa [Nat.sub_sub_self forced] using nonroot
  · exact before

theorem restart_mark_root (bounds : TrailBounds s) (distinct : DistinctTrailVariables s)
    (i : Nat) (root : i < s.forced) : s.restart.mark s.trail[i]! = s.mark s.trail[i]! := by
  apply restart_mark_unchanged bounds
  intro j nonroot before equal
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  have same := distinct j i before (Nat.lt_of_lt_of_le root forced) (congrArg Lit.var equal)
  omega

theorem restart_mark_root_negate (bounds : TrailBounds s) (distinct : DistinctTrailVariables s)
    (i : Nat) (root : i < s.forced) :
    s.restart.mark s.trail[i]!.negate = s.mark s.trail[i]!.negate := by
  apply restart_mark_unchanged bounds
  intro j nonroot before equal
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  have variableEqual : s.trail[j]!.var = s.trail[i]!.var := by
    simpa using congrArg Lit.var equal
  have same := distinct j i before (Nat.lt_of_lt_of_le root forced) variableEqual
  omega

/-- Every surviving mark belongs to the old forced prefix when all old marks
were on the trail. This is the coverage counterpart of nonroot clearing. -/
theorem restart_marked_prefix (arrays : ArrayBounds s) (bounds : TrailBounds s)
    (active : ActiveTrail s)
    (coverage : ∀ lit, s.mark lit ≠ 0 → ∃ i, i < s.assigned ∧ s.trail[i]! = lit)
    (lit : Lit) (marked : s.restart.mark lit ≠ 0) :
    ∃ i, i < s.forced ∧ s.trail[i]! = lit := by
  have old : s.mark lit ≠ 0 := fun zero => marked (restart_mark_unmarked zero)
  obtain ⟨i, before, equal⟩ := coverage lit old
  refine ⟨i, ?_, equal⟩
  by_cases root : i < s.forced
  · exact root
  · have cleared := restart_mark_cleared arrays bounds active i (by omega) before
    rw [equal] at cleared
    exact False.elim (marked cleared)

theorem ArrayBounds.restart (bounds : ArrayBounds s) : ArrayBounds s.restart := by
  constructor <;> simp_all [bounds.firstSize, bounds.marksSize, bounds.reasonsSize,
    bounds.phasesSize, bounds.trailSize, bounds.previousSize, bounds.nextSize]

theorem TrailBounds.restart (bounds : TrailBounds s) : TrailBounds s.restart := by
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  constructor <;> simp [restart_assigned bounds]
  exact Nat.le_trans forced bounds.assignedVars

theorem TrailPhases.restart (phases : TrailPhases s) (bounds : TrailBounds s) :
    TrailPhases s.restart := by
  intro i before
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  rw [restart_assigned bounds] at before
  simpa using phases i (Nat.lt_of_lt_of_le before forced)

theorem DistinctTrailVariables.restart (distinct : DistinctTrailVariables s) (bounds : TrailBounds s) :
    DistinctTrailVariables s.restart := by
  intro i j beforeI beforeJ same
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  rw [restart_assigned bounds] at beforeI beforeJ
  apply distinct i j (Nat.lt_of_lt_of_le beforeI forced) (Nat.lt_of_lt_of_le beforeJ forced)
  simpa using same

theorem ActiveTrail.restart (active : ActiveTrail s) (bounds : TrailBounds s)
    (distinct : DistinctTrailVariables s) : ActiveTrail s.restart := by
  intro i before
  rw [restart_assigned bounds] at before
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  have old := active i (Nat.lt_of_lt_of_le before forced)
  rw [restart_trail]
  constructor
  · simpa using old.1
  · constructor
    · rw [restart_mark_root bounds distinct i before]
      exact old.2.1
    · rw [restart_mark_root_negate bounds distinct i before]
      exact old.2.2

end MicrosatLean.Verification.Representation
