import MicrosatLean.Verification.Transitions

namespace MicrosatLean.Verification.Implementation.Logic

private theorem append_read {α : Type} [Inhabited α] (xs : List α) (x : α)
    {i : Nat} (before : i < xs.length) : (xs ++ [x])[i]! = xs[i]! := by
  rw [getElem!_pos (xs ++ [x]) i (by simp; omega), getElem!_pos xs i before,
    List.getElem_append_left]

private theorem append_last {α : Type} [Inhabited α] (xs : List α) (x : α) :
    (xs ++ [x])[xs.length]! = x := by
  rw [getElem!_pos (xs ++ [x]) xs.length (by simp)]
  simp

theorem prefix_append (a : LogicalState) (entry : TrailEntry) {count : Nat}
    (bound : count ≤ a.trail.length) :
    prefixLiterals { a with trail := a.trail ++ [entry] } count = prefixLiterals a count := by
  simp only [prefixLiterals, List.take_append_of_le_length bound]

theorem prefix_take (a : LogicalState) {keep count : Nat} (bound : count ≤ keep) :
    prefixLiterals { a with trail := a.trail.take keep } count = prefixLiterals a count := by
  simp only [prefixLiterals, List.take_take, Nat.min_eq_left bound]

private theorem append_distinct {input : CNF} {a : LogicalState} (valid : SemanticInv input a)
    {lit : Literal} (fresh : Unassigned a.trueTrail lit.1) :
    ((a.trueTrail ++ [lit]).map Prod.fst).Nodup := by
  simp only [List.map_append, List.map_singleton, List.nodup_append]
  refine ⟨valid.distinct, by simp, ?_⟩
  intro var member other last
  have same : other = lit.1 := by simpa using last
  subst other
  obtain ⟨old, contained, rfl⟩ := List.mem_map.mp member
  exact fresh old contained

/-- Distinct declared variables plus one fresh variable leave trail capacity.
This is a consequence of finite coverage, not an additional caller premise. -/
theorem append_capacity {input : CNF} {a : LogicalState} (valid : SemanticInv input a)
    {lit : Literal} (declared : LiteralBound a.numVars lit)
    (fresh : Unassigned a.trueTrail lit.1) : a.trail.length + 1 ≤ a.numVars := by
  have unique := append_distinct valid fresh
  have bounded : (a.trueTrail ++ [lit]).map Prod.fst ⊆ List.range' 1 a.numVars := by
    intro var member
    obtain ⟨entry, contained, rfl⟩ := List.mem_map.mp member
    have bound : LiteralBound a.numVars entry := by
      rcases List.mem_append.mp contained with old | added
      · exact valid.declaredTrail entry old
      · have same : entry = lit := by simpa using added
        simpa only [same] using declared
    simp only [List.mem_range'_1]
    exact ⟨by have := bound.1; omega, by have := bound.2; omega⟩
  have capacity := unique.length_le_of_subset bounded
  simpa [LogicalState.trueTrail] using capacity

/-- Append either a decision or a propagated literal. Only the new reason
needs justification; all older ordered reason edges retain their prefixes. -/
theorem append_preserves {input : CNF} {a : LogicalState} (valid : SemanticInv input a)
    (entry : TrailEntry) (declared : LiteralBound a.numVars entry.literal)
    (fresh : Unassigned a.trueTrail entry.literal.1)
    (reason : ∀ clause, entry.reason = some clause →
      Std.Sat.CNF.EntailsClause input clause ∧ clause.literals.head? = some entry.literal ∧
        ∀ lit ∈ clause.literals.tail, FalseIn a.trueTrail lit) :
    SemanticInv input { a with trail := a.trail ++ [entry] } := by
  refine ⟨valid.original, valid.learned, ?_, ?_,
    ?_, ?_, valid.declaredClauses, valid.nonempty, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton]
    have := valid.rootBound
    omega
  · simpa only [List.length_append, List.length_singleton] using append_capacity valid declared fresh
  · intro lit member
    simp only [LogicalState.trueTrail, List.map_append, List.map_singleton,
      List.mem_append, List.mem_singleton] at member
    rcases member with old | rfl
    · exact valid.declaredTrail lit old
    · exact declared
  · simpa only [LogicalState.trueTrail, List.map_append, List.map_singleton] using
      append_distinct valid fresh
  · intro i before clause stored
    have index : i ≤ a.trail.length := by
      simp only [List.length_append, List.length_singleton] at before
      omega
    by_cases old : i < a.trail.length
    · rw [append_read a.trail entry old] at stored
      have facts := valid.reasons i old clause stored
      rw [prefix_append a entry (Nat.le_of_lt old)]
      change _ ∧ _ = some (a.trail ++ [entry])[i]!.literal ∧ _
      rw [append_read a.trail entry old]
      exact facts
    · have last : i = a.trail.length := by omega
      subst i
      rw [append_last] at stored
      have facts := reason clause stored
      rw [prefix_append a entry (Nat.le_refl _)]
      change _ ∧ _ = some (a.trail ++ [entry])[a.trail.length]!.literal ∧ _
      rw [append_last]
      simpa only [prefixLiterals, List.take_length, LogicalState.trueTrail] using facts
  · rw [prefix_append a entry valid.rootBound]
    exact valid.roots

/-- Taking a prefix keeps every reason parent, since parents occur earlier.
Root assignments are protected by the explicit lower bound. -/
theorem take_preserves {input : CNF} {a : LogicalState} (valid : SemanticInv input a)
    {keep : Nat} (roots : a.rootSize ≤ keep) (bound : keep ≤ a.trail.length) :
    SemanticInv input { a with trail := a.trail.take keep } := by
  have length : (a.trail.take keep).length = keep := by simp [Nat.min_eq_left bound]
  refine ⟨valid.original, valid.learned, ?_, ?_, ?_, ?_,
    valid.declaredClauses, valid.nonempty, ?_, ?_⟩
  · simpa only [length] using roots
  · rw [length]
    exact Nat.le_trans bound valid.trailBound
  · intro lit member
    apply valid.declaredTrail lit
    simp only [LogicalState.trueTrail, List.map_take] at member
    exact List.mem_of_mem_take member
  · have sub : List.Sublist ((a.trail.take keep).map TrailEntry.literal) a.trueTrail :=
      (List.take_sublist keep a.trail).map _
    exact (sub.map Prod.fst).nodup valid.distinct
  · intro i before clause stored
    have old : i < a.trail.length := by rw [length] at before; omega
    have read : (a.trail.take keep)[i]! = a.trail[i]! := by
      rw [getElem!_pos (a.trail.take keep) i before, List.getElem_take, getElem!_pos a.trail i old]
    rw [read] at stored
    rw [prefix_take a (by rw [length] at before; omega)]
    change _ ∧ _ = some (a.trail.take keep)[i]!.literal ∧ _
    rw [read]
    exact valid.reasons i old clause stored
  · rw [prefix_take a roots]
    exact valid.roots

end MicrosatLean.Verification.Implementation.Logic
