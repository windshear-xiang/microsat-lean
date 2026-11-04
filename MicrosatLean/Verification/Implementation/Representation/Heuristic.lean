import MicrosatLean.Verification.Implementation.Representation.Order

namespace MicrosatLean.Verification.Implementation.Representation

open CDCL Order

/-- Bumping changes only analysis marks and the move-to-front links/head;
even their array dimensions remain fixed on arbitrary runtime states. -/
structure BumpFrame (before after : State) : Prop where
  restore : { after with
    marks := before.marks
    previous := before.previous
    next := before.next
    head := before.head } = before
  marksSize : after.marks.size = before.marks.size
  previousSize : after.previous.size = before.previous.size
  nextSize : after.next.size = before.next.size

theorem bump_frame (s : State) (lit : Lit) : BumpFrame s (s.bump lit) := by
  by_cases root : s.mark lit = 6 <;> by_cases head : lit.var = s.head <;>
    constructor <;> simp [State.bump, State.setMark, root, head]

variable {s : State} {lit other : Lit}

@[simp] theorem bump_nVars : (s.bump lit).nVars = s.nVars := by
  simpa using congrArg State.nVars (bump_frame s lit).restore

@[simp] theorem bump_arena : (s.bump lit).arena = s.arena := by
  simpa using congrArg State.arena (bump_frame s lit).restore

@[simp] theorem bump_first : (s.bump lit).first = s.first := by
  simpa using congrArg State.first (bump_frame s lit).restore

@[simp] theorem bump_reasons : (s.bump lit).reasons = s.reasons := by
  simpa using congrArg State.reasons (bump_frame s lit).restore

@[simp] theorem bump_phases : (s.bump lit).phases = s.phases := by
  simpa using congrArg State.phases (bump_frame s lit).restore

@[simp] theorem bump_trail : (s.bump lit).trail = s.trail := by
  simpa using congrArg State.trail (bump_frame s lit).restore

@[simp] theorem bump_assigned : (s.bump lit).assigned = s.assigned := by
  simpa using congrArg State.assigned (bump_frame s lit).restore

@[simp] theorem bump_processed : (s.bump lit).processed = s.processed := by
  simpa using congrArg State.processed (bump_frame s lit).restore

@[simp] theorem bump_forced : (s.bump lit).forced = s.forced := by
  simpa using congrArg State.forced (bump_frame s lit).restore

@[simp] theorem bump_marks_size : (s.bump lit).marks.size = s.marks.size :=
  (bump_frame s lit).marksSize

@[simp] theorem bump_previous_size : (s.bump lit).previous.size = s.previous.size :=
  (bump_frame s lit).previousSize

@[simp] theorem bump_next_size : (s.bump lit).next.size = s.next.size :=
  (bump_frame s lit).nextSize

theorem ArrayBounds.bump (bounds : ArrayBounds s) : ArrayBounds (s.bump lit) := by
  constructor <;> simp_all [bounds.firstSize, bounds.marksSize, bounds.reasonsSize,
    bounds.phasesSize, bounds.trailSize, bounds.previousSize, bounds.nextSize]

theorem TrailBounds.bump (bounds : TrailBounds s) : TrailBounds (s.bump lit) := by
  constructor
  · simpa using bounds.forcedProcessed
  · simpa using bounds.processedAssigned
  · simpa using bounds.assignedVars

theorem TrailPhases.bump (phases : TrailPhases s) : TrailPhases (s.bump lit) := by
  simpa [TrailPhases] using phases

theorem DistinctTrailVariables.bump (distinct : DistinctTrailVariables s) :
    DistinctTrailVariables (s.bump lit) := by
  simpa [DistinctTrailVariables] using distinct

theorem bump_eq_of_root (root : s.mark lit = 6) : s.bump lit = s := by
  simp [State.bump, root]

theorem bump_eq_of_head (root : s.mark lit ≠ 6) (head : lit.var = s.head) :
    s.bump lit = s.setMark lit 2 := by
  simp [State.bump, root, head, State.setMark]

theorem MTFOrder.bump_root {order : List Nat} (orderValid : MTFOrder s order)
    (root : s.mark lit = 6) : MTFOrder (s.bump lit) order := by
  rwa [bump_eq_of_root root]

theorem MTFOrder.bump_head {order : List Nat} (orderValid : MTFOrder s order)
    (root : s.mark lit ≠ 6) (head : lit.var = s.head) : MTFOrder (s.bump lit) order := by
  rw [bump_eq_of_head root head]
  exact orderValid

theorem bump_previous_of_move (root : s.mark lit ≠ 6) (head : lit.var ≠ s.head) :
    (s.bump lit).previous =
      (s.previous.set! s.next[lit.var]! s.previous[lit.var]!).set! lit.var s.head := by
  simp [State.bump, State.setMark, root, head]

theorem bump_next_of_move (root : s.mark lit ≠ 6) (head : lit.var ≠ s.head) :
    (s.bump lit).next =
      (s.next.set! s.previous[lit.var]! s.next[lit.var]!).set! s.head lit.var := by
  simp [State.bump, State.setMark, root, head]

theorem bump_head_of_move (root : s.mark lit ≠ 6) (head : lit.var ≠ s.head) :
    (s.bump lit).head = lit.var := by
  simp [State.bump, State.setMark, root, head]

private theorem read_set_if (array : Array Nat) (key i value : Nat) (bound : key < array.size) :
    (array.set! key value)[i]! = if key = i then value else array[i]! := by
  by_cases same : key = i
  · subst i
    rw [ite_eq_left (rfl : key = key)]
    exact Array.getElem!_set!_self _ _ _ bound
  · rw [ite_eq_right same]
    exact Array.getElem!_set!_ne _ _ _ _ same

private theorem bump_order_at {order : List Nat} {selected : Nat} (valid : MTFOrder s order)
    (arrays : ArrayBounds s) (chosen : selected < order.length) (positive : 0 < selected)
    (value : order.getD selected 0 = lit.var) (root : s.mark lit ≠ 6) (head : lit.var ≠ s.head) :
    MTFOrder (s.bump lit) (movedOrder order selected) := by
  have permutation := movedOrder_perm valid.1 chosen
  have headValue : s.head = order.getD 0 0 := valid.2.2.1.trans List.headD_eq_getD
  have previousValue : s.previous[lit.var]! = order.getD (selected + 1) 0 := by
    rw [← value]
    exact (valid.2.2.2 selected chosen).1
  have nextValue : s.next[lit.var]! = order.getD (selected - 1) 0 := by
    rw [← value]
    exact (valid.2.2.2 selected chosen).2 positive
  have previousBound (i : Nat) : order.getD i 0 < s.previous.size := by
    rw [arrays.previousSize]
    exact Nat.lt_succ_of_le (order_getD_bound valid i)
  have nextBound (i : Nat) : order.getD i 0 < s.next.size := by
    rw [arrays.nextSize]
    exact Nat.lt_succ_of_le (order_getD_bound valid i)
  have previousAt (j : Nat) (bound : j < order.length) :
      (s.bump lit).previous[order.getD j 0]! =
        if selected = j then order.getD 0 0
        else if selected - 1 = j then order.getD (selected + 1) 0
        else order.getD (j + 1) 0 := by
    rw [bump_previous_of_move root head, previousValue, nextValue, headValue, ← value]
    rw [read_set_if _ _ _ _ (by simpa using previousBound selected)]
    rw [read_set_if _ _ _ _ (previousBound (selected - 1))]
    simp only [order_getD_eq_iff valid (Nat.le_of_lt chosen) bound,
      order_getD_eq_iff valid (by omega : selected - 1 ≤ order.length) bound,
      (valid.2.2.2 j bound).1]
  have nextAt (j : Nat) (bound : j < order.length) :
      (s.bump lit).next[order.getD j 0]! =
        if 0 = j then order.getD selected 0
        else if selected + 1 = j then order.getD (selected - 1) 0
        else order.getD (j - 1) 0 := by
    rw [bump_next_of_move root head, previousValue, nextValue, headValue, ← value]
    rw [read_set_if _ _ _ _ (by simpa using nextBound 0)]
    rw [read_set_if _ _ _ _ (nextBound (selected + 1))]
    simp only [order_getD_eq_iff valid (by omega : 0 ≤ order.length) bound,
      order_getD_eq_iff valid (by omega : selected + 1 ≤ order.length) bound]
    by_cases zero : j = 0
    · simp [zero]
    · rw [(valid.2.2.2 j bound).2 (by omega)]
  refine ⟨permutation.nodup valid.1, ?_, ?_, ?_⟩
  · intro var
    rw [← permutation.mem_iff, bump_nVars]
    exact valid.2.1 var
  · rw [bump_head_of_move root head]
    exact value.symm
  · intro i bound
    have oldBound : i < order.length := by simpa only [permutation.length_eq] using bound
    have mappedBound := moveIndex_bound chosen oldBound
    simp only [movedOrder_getD]
    constructor
    · rw [previousAt _ mappedBound, moveIndex_previous _ _ positive]
      by_cases first : selected = moveIndex selected i
      · simp only [ite_eq_left first]
      · by_cases second : selected - 1 = moveIndex selected i
        · simp only [ite_eq_right first, ite_eq_left second]
        · simp only [ite_eq_right first, ite_eq_right second]
    · intro nonhead
      rw [nextAt _ mappedBound, moveIndex_next _ _ positive nonhead]
      by_cases first : 0 = moveIndex selected i
      · simp only [ite_eq_left first]
      · by_cases second : selected + 1 = moveIndex selected i
        · simp only [ite_eq_right first, ite_eq_left second]
        · simp only [ite_eq_right first, ite_eq_right second]

/-- The actual non-head bump moves precisely its variable to the front and
retains every other variable in its previous relative order. -/
theorem MTFOrder.bump_move {order : List Nat} (valid : MTFOrder s order)
    (arrays : ArrayBounds s) (literal : LiteralBound s.nVars lit)
    (root : s.mark lit ≠ 6) (head : lit.var ≠ s.head) :
    MTFOrder (s.bump lit) (lit.var :: order.erase lit.var) := by
  have member : lit.var ∈ order := (valid.2.1 _).mpr literal
  obtain ⟨selected, chosen, entry⟩ := List.getElem_of_mem member
  have value : order.getD selected 0 = lit.var := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem chosen] using entry
  have positive : 0 < selected := by
    by_cases zero : selected = 0
    · subst selected
      have first : s.head = lit.var := by
        rw [valid.2.2.1, List.headD_eq_getD, value]
      exact False.elim (head first.symm)
    · omega
  have moved := bump_order_at valid arrays chosen positive value root head
  have erased : order.erase lit.var = order.eraseIdx selected := by
    apply List.erase_eq_eraseIdx_of_idxOf
    rw [← entry]
    exact valid.1.idxOf_getElem selected chosen
  simpa only [movedOrder, value, ← erased] using moved

theorem MTFCoverage.bump (coverage : MTFCoverage s) (arrays : ArrayBounds s)
    (literal : LiteralBound s.nVars lit) : MTFCoverage (s.bump lit) := by
  obtain ⟨order, valid⟩ := coverage
  by_cases root : s.mark lit = 6
  · exact ⟨order, valid.bump_root root⟩
  · by_cases head : lit.var = s.head
    · exact ⟨order, valid.bump_head root head⟩
    · exact ⟨_, valid.bump_move arrays literal root head⟩

end MicrosatLean.Verification.Implementation.Representation
