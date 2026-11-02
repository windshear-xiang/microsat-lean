import MicrosatLean.Verification.Implementation.Representation.State

namespace MicrosatLean.Verification.Implementation.Representation

open CDCL

private theorem pushAll_eq_append (arena : Array Nat) (lits : Array Lit) :
    lits.foldl (fun acc lit => acc.push lit) arena = arena ++ lits := by
  simpa using (Array.foldl_push_eq_append (as := lits) (bs := arena) (f := id) rfl)

variable {s : State} {lits : Array Lit} {original : Bool}

@[simp] theorem addClause_id : (s.addClause lits original).2 = s.arena.size + 2 := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, h]

theorem addClause_arena_size :
    (s.addClause lits original).1.arena.size = s.arena.size + lits.size + 3 := by
  by_cases h : 1 < lits.size <;> cases original <;>
    simp [State.addClause, State.addWatch, h, pushAll_eq_append] <;> omega

@[simp] theorem addClause_nVars : (s.addClause lits original).1.nVars = s.nVars := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, State.addWatch, h]

@[simp] theorem addClause_marks : (s.addClause lits original).1.marks = s.marks := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, State.addWatch, h]

@[simp] theorem addClause_reasons : (s.addClause lits original).1.reasons = s.reasons := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, State.addWatch, h]

@[simp] theorem addClause_phases : (s.addClause lits original).1.phases = s.phases := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, State.addWatch, h]

@[simp] theorem addClause_trail : (s.addClause lits original).1.trail = s.trail := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, State.addWatch, h]

@[simp] theorem addClause_assigned : (s.addClause lits original).1.assigned = s.assigned := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, State.addWatch, h]

@[simp] theorem addClause_processed : (s.addClause lits original).1.processed = s.processed := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, State.addWatch, h]

@[simp] theorem addClause_forced : (s.addClause lits original).1.forced = s.forced := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, State.addWatch, h]

theorem ArrayBounds.addClause (bounds : ArrayBounds s) :
    ArrayBounds (s.addClause lits original).1 := by
  rcases bounds with ⟨hf, hm, hr, hp, ht, hprev, hn⟩
  constructor <;> by_cases h : 1 < lits.size <;> cases original <;>
    simp [State.addClause, State.addWatch, h, hf, hm, hr, hp, ht, hprev, hn]

theorem TrailBounds.addClause (bounds : TrailBounds s) :
    TrailBounds (s.addClause lits original).1 := by
  constructor
  · simpa using bounds.forcedProcessed
  · simpa using bounds.processedAssigned
  · simpa using bounds.assignedVars

theorem ActiveTrail.addClause (active : ActiveTrail s) :
    ActiveTrail (s.addClause lits original).1 := by
  simpa [ActiveTrail, FalseAssignment, State.mark] using active

theorem DistinctTrailVariables.addClause (distinct : DistinctTrailVariables s) :
    DistinctTrailVariables (s.addClause lits original).1 := by
  simpa [DistinctTrailVariables] using distinct

theorem TrailPhases.addClause (phases : TrailPhases s) :
    TrailPhases (s.addClause lits original).1 := by
  simpa [TrailPhases] using phases

@[simp] theorem watchLinkPos_even (clauseId : Nat) :
    watchLinkPos (2 * clauseId) = clauseId - 2 := by
  unfold watchLinkPos
  omega

@[simp] theorem watchLinkPos_odd (clauseId : Nat) (lower : 2 ≤ clauseId) :
    watchLinkPos (2 * clauseId + 1) = clauseId - 1 := by
  unfold watchLinkPos
  omega

private theorem read_setIfInBounds_other (arena : Array Nat) (i j value : Nat)
    (different : i ≠ j) : (arena.setIfInBounds i value)[j]! = arena[j]! := by
  simpa only [← Array.set!_eq_setIfInBounds] using
    Array.getElem!_set!_ne arena i j value different

private theorem read_append_right (left right : Array Nat) (i : Nat) :
    (left ++ right)[left.size + i]! = right[i]! := by
  have notBefore : ¬left.size + i < left.size := by omega
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append, notBefore]

private theorem read_append_left (left right : Array Nat) (i : Nat) (before : i < left.size) :
    (left ++ right)[i]! = left[i]! := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_append, before]

private theorem read_push_before (arena : Array Nat) (value i : Nat) (before : i < arena.size) :
    (arena.push value)[i]! = arena[i]! := by
  simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push, Nat.ne_of_lt before]

/-- Allocation changes only its two new link cells in addition to appending the
literal slice. Reads at every other index agree with the explicit allocation. -/
theorem addClause_db_of_ne_links (i : Nat) (notFirst : s.arena.size ≠ i)
    (notSecond : s.arena.size + 1 ≠ i) :
    (s.addClause lits original).1.db i = (((s.arena.push 0).push 0 ++ lits).push 0)[i]! := by
  have firstLink : watchLinkPos (2 * (s.arena.size + 2)) = s.arena.size := by
    simp
  by_cases h : 1 < lits.size <;> cases original <;>
    simp [State.addClause, State.addWatch, State.db, h, pushAll_eq_append,
      firstLink, read_setIfInBounds_other, notFirst, notSecond]

theorem addClause_db_before (i : Nat) (before : i < s.arena.size) :
    (s.addClause lits original).1.db i = s.db i := by
  rw [addClause_db_of_ne_links _ (by omega) (by omega)]
  rw [read_push_before _ _ _ (by simp only [Array.size_append, Array.size_push]; omega)]
  rw [read_append_left _ _ _ (by simp only [Array.size_push]; omega)]
  rw [read_push_before _ _ _ (by simp only [Array.size_push]; omega)]
  rw [read_push_before _ _ _ before]
  rfl

theorem PackedClause.start_index (clause : PackedClause s clauseId lits) :
    clauseId < s.arena.size := by
  have := clause.endBound
  omega

theorem PackedClause.link_indices (clause : PackedClause s clauseId lits) :
    clauseId - 2 < s.arena.size ∧ clauseId - 1 < s.arena.size := by
  have := clause.start_index
  omega

theorem PackedClause.literal_index (clause : PackedClause s clauseId lits)
    (i : Nat) (bound : i < lits.size) : clauseId + i < s.arena.size := by
  have := clause.endBound
  omega

/-- The allocator really writes the requested packed clause, including its
terminator, under only the literal-range and reserved-prefix preconditions. -/
theorem addClause_packed (reserved : 2 ≤ s.arena.size)
    (wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit) :
    PackedClause (s.addClause lits original).1 (s.addClause lits original).2 lits := by
  rw [addClause_id]
  constructor
  · omega
  · rw [addClause_arena_size]
    omega
  · intro i bound
    rw [addClause_db_of_ne_links _ (by omega) (by omega)]
    have before : s.arena.size + 2 + i < ((s.arena.push 0).push 0 ++ lits).size := by
      simp only [Array.size_append, Array.size_push]
      omega
    rw [read_push_before _ _ _ before]
    have index : s.arena.size + 2 + i = ((s.arena.push 0).push 0).size + i := by simp
    rw [index, read_append_right]
  · rw [addClause_db_of_ne_links _ (by omega) (by omega)]
    have index : s.arena.size + 2 + lits.size = ((s.arena.push 0).push 0 ++ lits).size := by
      simp only [Array.size_append, Array.size_push]
    rw [index]
    simp
  · simpa using wellFormed

theorem PackedClause.addClause (clause : PackedClause s clauseId lits) (newLits : Array Lit) :
    PackedClause (s.addClause newLits original).1 clauseId lits := by
  constructor
  · exact clause.startLower
  · rw [addClause_arena_size]
    have := clause.endBound
    omega
  · intro i bound
    rw [addClause_db_before _ (clause.literal_index i bound)]
    exact clause.literals i bound
  · rw [addClause_db_before _ clause.endBound]
    exact clause.terminator
  · simpa using clause.wellFormed

theorem addClause_fixed : (s.addClause lits original).1.fixed =
    if original then (s.addClause lits original).1.arena.size else s.fixed := by
  by_cases h : 1 < lits.size <;> cases original <;> simp [State.addClause, State.addWatch, h]

theorem ArenaBounds.addClause (bounds : ArenaBounds s) :
    ArenaBounds (s.addClause lits original).1 := by
  have size := addClause_arena_size (s := s) (lits := lits) (original := original)
  have reserved := bounds.reserved
  have fixedLower := bounds.fixedLower
  have fixedUpper := bounds.fixedUpper
  constructor
  · omega
  · rw [addClause_fixed]
    cases original <;> simp_all <;> omega
  · rw [addClause_fixed]
    cases original <;> simp_all <;> omega

end MicrosatLean.Verification.Implementation.Representation
