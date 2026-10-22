import MicrosatLean.CDCL.Search
import MicrosatLean.Verification.Representation.State

namespace MicrosatLean.Verification.Search

open CDCL Representation

private def decisionForLoop (s : State) (cursor start fuel : Nat) : Nat := Id.run do
  let mut cursor := cursor
  for _ in [start : start + fuel] do
    if cursor == 0 then return 0
    let positive := 2 * cursor
    if s.mark positive == 0 && s.mark (positive + 1) == 0 then return cursor
    cursor := s.previous[cursor]!
  return 0

private theorem decisionForLoop_eq_scan (fuel : Nat) (s : State) (cursor start : Nat) :
    decisionForLoop s cursor start fuel = nextDecisionScan fuel s cursor := by
  induction fuel generalizing cursor start with
  | zero =>
    simp [decisionForLoop, Std.Legacy.Range.forIn_eq_forIn_range', nextDecisionScan]
  | succ fuel ih =>
    simp only [decisionForLoop, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
    rw [show start + (fuel + 1) - start = fuel + 1 by omega]
    simp only [List.range'_succ, List.forIn_cons, nextDecisionScan]
    split
    · simp_all
    · split
      · simp_all
      · have tail := ih s.previous[cursor]! (start + 1)
        simp only [decisionForLoop, Std.Legacy.Range.forIn_eq_forIn_range'] at tail
        simpa using tail

/-- The structural scan is exactly the previous bounded `for` implementation,
including arbitrary malformed states and budget exhaustion. -/
theorem nextDecision_eq_original_loop (s : State) (cursor : Nat) :
    nextDecision s cursor = (Id.run do
      let mut cursor := cursor
      for _ in [:s.nVars + 1] do
        if cursor == 0 then return 0
        let positive := 2 * cursor
        if s.mark positive == 0 && s.mark (positive + 1) == 0 then return cursor
        cursor := s.previous[cursor]!
      return 0) := by
  simpa only [decisionForLoop, Nat.zero_add, nextDecision] using
    (decisionForLoop_eq_scan (s.nVars + 1) s cursor 0).symm

/-- Both polarities are unset in the executable assignment. -/
def UnassignedVariable (s : State) (var : Nat) : Prop :=
  s.mark (2 * var) = 0 ∧ s.mark (2 * var + 1) = 0

instance (s : State) (var : Nat) : Decidable (UnassignedVariable s var) :=
  inferInstanceAs (Decidable (s.mark (2 * var) = 0 ∧ s.mark (2 * var + 1) = 0))

/-- At least one polarity is marked. Trail consistency separately excludes
marking both polarities of a variable. -/
def AssignedVariable (s : State) (var : Nat) : Prop :=
  s.mark (2 * var) ≠ 0 ∨ s.mark (2 * var + 1) ≠ 0

theorem assignedVariable_of_not_unassigned {s : State} {var : Nat}
    (h : ¬ UnassignedVariable s var) : AssignedVariable s var := by
  by_cases positive : s.mark (2 * var) = 0
  · exact Or.inr (fun negative => h ⟨positive, negative⟩)
  · exact Or.inl positive

private theorem nextDecisionScan_succ {s : State} {cursor fuel : Nat}
    (hCursor : cursor ≠ 0) :
    nextDecisionScan (fuel + 1) s cursor =
      if UnassignedVariable s cursor then cursor else nextDecisionScan fuel s s.previous[cursor]! := by
  simp only [nextDecisionScan, Bool.and_eq_true, beq_iff_eq, hCursor, ite_false,
    UnassignedVariable]
  rfl

theorem nextDecisionScan_nonzero_unassigned (fuel : Nat) (s : State) (cursor : Nat)
    (hResult : nextDecisionScan fuel s cursor ≠ 0) :
    UnassignedVariable s (nextDecisionScan fuel s cursor) := by
  induction fuel generalizing cursor with
  | zero => simp [nextDecisionScan] at hResult
  | succ fuel ih =>
    by_cases hCursor : cursor = 0
    · simp [nextDecisionScan, hCursor] at hResult
    · by_cases hUnset : UnassignedVariable s cursor
      · simp [nextDecisionScan, hCursor, UnassignedVariable, hUnset.1, hUnset.2]
      · have hCondition : ¬ (s.mark (2 * cursor) == 0 &&
            s.mark (2 * cursor + 1) == 0) = true := by
          simpa [UnassignedVariable] using hUnset
        simpa [nextDecisionScan, hCursor, hCondition] using
          ih s.previous[cursor]! (by simpa [nextDecisionScan, hCursor, hCondition] using hResult)

theorem nextDecision_zero_or_unassigned (s : State) (cursor : Nat) :
    nextDecision s cursor = 0 ∨
      UnassignedVariable s (nextDecision s cursor) := by
  by_cases h : nextDecision s cursor = 0
  · exact Or.inl h
  · exact Or.inr (nextDecisionScan_nonzero_unassigned _ _ _ h)

private theorem getD_eq_getElem {order : List Nat} {i : Nat} (h : i < order.length) :
    order.getD i 0 = order[i] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

private theorem getD_mem {order : List Nat} {i : Nat} (h : i < order.length) :
    order.getD i 0 ∈ order := by
  rw [getD_eq_getElem h]
  exact List.getElem_mem h

private theorem getD_mem_or_zero (order : List Nat) (i : Nat) :
    order.getD i 0 ∈ order ∨ order.getD i 0 = 0 := by
  by_cases h : i < order.length
  · exact Or.inl (getD_mem h)
  · right
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : order.length ≤ i)]

theorem mtfOrder_length_le {s : State} {order : List Nat} (hOrder : MTFOrder s order) :
    order.length ≤ s.nVars := by
  have subset : order ⊆ List.range' 1 s.nVars := by
    intro var hVar
    have bound := (hOrder.2.1 var).mp hVar
    apply List.mem_range'_1.mpr
    omega
  simpa using hOrder.1.length_le_of_subset subset

private theorem mtfOrder_getD_ne_zero {s : State} {order : List Nat}
    (hOrder : MTFOrder s order) {i : Nat} (h : i < order.length) :
    order.getD i 0 ≠ 0 := by
  have bound := (hOrder.2.1 _).mp (getD_mem h)
  omega

private theorem mtfOrder_previous_mem_or_zero {s : State} {order : List Nat}
    (hOrder : MTFOrder s order) {cursor : Nat} (hCursor : cursor ∈ order) :
    s.previous[cursor]! ∈ order ∨ s.previous[cursor]! = 0 := by
  obtain ⟨i, hI, hValue⟩ := List.getElem_of_mem hCursor
  have hGet : order.getD i 0 = cursor := by rw [getD_eq_getElem hI, hValue]
  rw [← hGet, (hOrder.2.2.2 i hI).1]
  exact getD_mem_or_zero order (i + 1)

theorem nextDecisionScan_mem_of_nonzero {s : State} {order : List Nat}
    (hOrder : MTFOrder s order) (fuel cursor : Nat)
    (hCursor : cursor ∈ order ∨ cursor = 0)
    (hResult : nextDecisionScan fuel s cursor ≠ 0) :
    nextDecisionScan fuel s cursor ∈ order := by
  induction fuel generalizing cursor with
  | zero => simp [nextDecisionScan] at hResult
  | succ fuel ih =>
    by_cases hZero : cursor = 0
    · simp [nextDecisionScan, hZero] at hResult
    · have hMember : cursor ∈ order := hCursor.resolve_right hZero
      by_cases hUnset : UnassignedVariable s cursor
      · simpa [nextDecisionScan, hZero, hUnset.1, hUnset.2] using hMember
      · have hCondition : ¬ (s.mark (2 * cursor) == 0 &&
            s.mark (2 * cursor + 1) == 0) = true := by
          simpa [UnassignedVariable] using hUnset
        simpa [nextDecisionScan, hZero, hCondition] using ih s.previous[cursor]!
          (mtfOrder_previous_mem_or_zero hOrder hMember)
          (by simpa [nextDecisionScan, hZero, hCondition] using hResult)

/-- If the concrete scan returns zero, every order entry it had enough fuel to
visit is assigned. This also supports starts inside the MTF list. -/
theorem nextDecisionScan_zero_prefix {s : State} {order : List Nat}
    (hOrder : MTFOrder s order) (fuel start : Nat)
    (hResult : nextDecisionScan fuel s (order.getD start 0) = 0) :
    ∀ i, start ≤ i → i < order.length → i < start + fuel →
      AssignedVariable s (order.getD i 0) := by
  induction fuel generalizing start with
  | zero => intro i hStart hI hFuel; omega
  | succ fuel ih =>
    intro i hStart hI hFuel
    have hStartBound : start < order.length := by omega
    have hCursor := mtfOrder_getD_ne_zero hOrder hStartBound
    have hUnset : ¬ UnassignedVariable s (order.getD start 0) := by
      intro h
      rw [nextDecisionScan_succ hCursor, ite_eq_left h] at hResult
      exact hCursor hResult
    by_cases hEqual : i = start
    · simpa [hEqual] using assignedVariable_of_not_unassigned hUnset
    · have hTail : nextDecisionScan fuel s (order.getD (start + 1) 0) = 0 := by
        rw [nextDecisionScan_succ hCursor, ite_eq_right hUnset,
          (hOrder.2.2.2 start hStartBound).1] at hResult
        exact hResult
      exact ih (start + 1) hTail i (by omega) hI (by omega)

theorem nextDecision_zero_suffix {s : State} {order : List Nat}
    (hOrder : MTFOrder s order) (start : Nat)
    (hResult : nextDecision s (order.getD start 0) = 0) :
    ∀ i, start ≤ i → i < order.length → AssignedVariable s (order.getD i 0) := by
  intro i hStart hI
  have hLength := mtfOrder_length_le hOrder
  exact nextDecisionScan_zero_prefix hOrder (s.nVars + 1) start hResult i hStart hI (by omega)

/-- Starting from the head, zero means every declared variable is assigned.
The MTF invariant already records exact `get!` link values, so this theorem is
stronger than a version also requiring `ArrayBounds`. -/
theorem nextDecision_head_zero_all_assigned {s : State} {order : List Nat}
    (hOrder : MTFOrder s order) (hResult : nextDecision s s.head = 0) :
    ∀ var, 1 ≤ var → var ≤ s.nVars → AssignedVariable s var := by
  intro var hLower hUpper
  have hMember := (hOrder.2.1 var).mpr ⟨hLower, hUpper⟩
  obtain ⟨i, hI, hValue⟩ := List.getElem_of_mem hMember
  have hHead : s.head = order.getD 0 0 := by
    rw [hOrder.2.2.1, List.headD_eq_getD]
  have hZero : nextDecision s (order.getD 0 0) = 0 := by simpa [hHead] using hResult
  have hAssigned := nextDecision_zero_suffix hOrder 0 hZero i (by omega) hI
  have hGet : order.getD i 0 = var := (getD_eq_getElem hI).trans hValue
  simpa only [hGet] using hAssigned

/-- A cursor inside the order is complete when earlier entries were already
assigned. Search must preserve this coverage when reusing a decision cursor. -/
theorem nextDecision_zero_all_assigned {s : State} {order : List Nat}
    (hOrder : MTFOrder s order) (start : Nat)
    (hPrefix : ∀ i, i < start → i < order.length → AssignedVariable s (order.getD i 0))
    (hResult : nextDecision s (order.getD start 0) = 0) :
    ∀ var, 1 ≤ var → var ≤ s.nVars → AssignedVariable s var := by
  intro var hLower hUpper
  obtain ⟨i, hI, hValue⟩ := List.getElem_of_mem ((hOrder.2.1 var).mpr ⟨hLower, hUpper⟩)
  have hAssigned : AssignedVariable s (order.getD i 0) := by
    by_cases before : i < start
    · exact hPrefix i before hI
    · exact nextDecision_zero_suffix hOrder start hResult i (by omega) hI
  simpa only [getD_eq_getElem hI, hValue] using hAssigned

theorem nextDecision_head_nonzero_bounds {s : State} {order : List Nat}
    (hOrder : MTFOrder s order) (hResult : nextDecision s s.head ≠ 0) :
    1 ≤ nextDecision s s.head ∧ nextDecision s s.head ≤ s.nVars := by
  apply (hOrder.2.1 _).mp
  apply nextDecisionScan_mem_of_nonzero hOrder (s.nVars + 1) s.head
  · rw [hOrder.2.2.1, List.headD_eq_getD]
    exact getD_mem_or_zero order 0
  · exact hResult

end MicrosatLean.Verification.Search
