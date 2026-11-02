import MicrosatLean.Verification.Implementation.Representation.Arena

namespace MicrosatLean.Verification.Implementation.Representation

open CDCL

private theorem pushAll_eq_append (arena : Array Nat) (lits : Array Lit) :
    lits.foldl (fun acc lit => acc.push lit) arena = arena ++ lits := by
  simpa using (Array.foldl_push_eq_append (as := lits) (bs := arena) (f := id) rfl)

variable {s : State} {lits : Array Lit} {original : Bool} {clauseId ref : Nat} {lit : Lit}

theorem PackedClause.watchEntry_first (clause : PackedClause s clauseId lits) (wide : 1 < lits.size) :
    WatchEntry s lits[0]! (2 * clauseId) := by
  have decoded : watchClause (2 * clauseId) = clauseId := by unfold watchClause; omega
  unfold WatchEntry
  rw [decoded, watchLinkPos_even]
  refine ⟨clause.startLower, ?_, clause.link_indices.1, Or.inl ?_⟩
  · have := clause.endBound
    omega
  · simpa using clause.literals 0 (by omega)

theorem PackedClause.watchEntry_second (clause : PackedClause s clauseId lits) (wide : 1 < lits.size) :
    WatchEntry s lits[1]! (2 * clauseId + 1) := by
  have decoded : watchClause (2 * clauseId + 1) = clauseId := by unfold watchClause; omega
  have lower := clause.startLower
  unfold WatchEntry
  rw [decoded, watchLinkPos_odd _ (by omega)]
  refine ⟨lower, ?_, clause.link_indices.2, Or.inr ?_⟩
  · have := clause.endBound
    omega
  · exact clause.literals 1 wide

theorem WatchEntry.addClause (entry : WatchEntry s lit ref) (newLits : Array Lit) :
    WatchEntry (s.addClause newLits original).1 lit ref := by
  rcases entry with ⟨lower, upper, link, watched⟩
  refine ⟨lower, ?_, ?_, ?_⟩
  · rw [addClause_arena_size]
    omega
  · rw [addClause_arena_size]
    omega
  · rwa [addClause_db_before _ (by omega), addClause_db_before _ upper]

theorem addClause_first_array (wide : 1 < lits.size) :
    (s.addClause lits original).1.first =
      (s.first.set! lits[0]! (2 * (s.arena.size + 2))).set! lits[1]! (2 * (s.arena.size + 2) + 1) := by
  cases original <;> simp [State.addClause, State.addWatch, wide]

theorem addClause_first_short (short : lits.size ≤ 1) :
    (s.addClause lits original).1.first = s.first := by
  have notWide : ¬1 < lits.size := by omega
  cases original <;> simp [State.addClause, notWide]

private theorem addClause_watched_arena (wide : 1 < lits.size) :
    (s.addClause lits original).1.arena =
      ((((s.arena.push 0).push 0 ++ lits).push 0).set! s.arena.size s.first[lits[0]!]!).set!
        (s.arena.size + 1) (s.first.set! lits[0]! (2 * (s.arena.size + 2)))[lits[1]!]! := by
  cases original <;> simp [State.addClause, State.addWatch, wide, pushAll_eq_append]

theorem addClause_first_link (wide : 1 < lits.size) :
    (s.addClause lits original).1.db s.arena.size = s.first[lits[0]!]! := by
  unfold State.db
  rw [addClause_watched_arena wide, Array.getElem!_set!_ne _ _ _ _ (by omega)]
  apply Array.getElem!_set!_self
  simp only [Array.size_push, Array.size_append]
  omega

theorem addClause_second_link (wide : 1 < lits.size) (distinct : lits[0]! ≠ lits[1]!) :
    (s.addClause lits original).1.db (s.arena.size + 1) = s.first[lits[1]!]! := by
  unfold State.db
  rw [addClause_watched_arena wide, Array.getElem!_set!_self]
  · exact Array.getElem!_set!_ne _ _ _ _ distinct
  · simp only [Array.size_set!, Array.size_push, Array.size_append]
    omega

theorem addClause_first_head (wide : 1 < lits.size) (distinct : lits[0]! ≠ lits[1]!)
    (bound : lits[0]! < s.first.size) :
    (s.addClause lits original).1.first[lits[0]!]! = 2 * (s.arena.size + 2) := by
  rw [addClause_first_array wide, Array.getElem!_set!_ne _ _ _ _ (Ne.symm distinct)]
  exact Array.getElem!_set!_self _ _ _ bound

theorem addClause_second_head (wide : 1 < lits.size) (bound : lits[1]! < s.first.size) :
    (s.addClause lits original).1.first[lits[1]!]! = 2 * (s.arena.size + 2) + 1 := by
  rw [addClause_first_array wide]
  apply Array.getElem!_set!_self
  simpa using bound

theorem addClause_other_head (wide : 1 < lits.size) (first : lits[0]! ≠ lit) (second : lits[1]! ≠ lit) :
    (s.addClause lits original).1.first[lit]! = s.first[lit]! := by
  rw [addClause_first_array wide, Array.getElem!_set!_ne _ _ _ _ second,
    Array.getElem!_set!_ne _ _ _ _ first]

theorem WatchList.newRef_not_mem {refs : List Nat} (list : WatchList s lit refs)
    (slot : Nat) (slotBound : slot ≤ 1) : 2 * (s.arena.size + 2) + slot ∉ refs := by
  intro member
  obtain ⟨i, before, value⟩ := List.getElem_of_mem member
  have atIndex : refs.getD i 0 = 2 * (s.arena.size + 2) + slot := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem before] using value
  have entry := (list.2.2 i before).1
  rw [atIndex] at entry
  have upper := entry.2.1
  unfold watchClause at upper
  omega

/-- Existing references keep their entries and next links after allocation. -/
theorem WatchList.addClause_other {refs : List Nat} (list : WatchList s lit refs)
    (wide : 1 < lits.size) (first : lits[0]! ≠ lit) (second : lits[1]! ≠ lit) :
    WatchList (s.addClause lits original).1 lit refs := by
  refine ⟨list.1, ?_, ?_⟩
  · rw [addClause_other_head wide first second]
    exact list.2.1
  · intro i bound
    have old := list.2.2 i bound
    refine ⟨old.1.addClause lits, ?_⟩
    rw [addClause_db_before _ old.1.2.2.1]
    exact old.2

theorem WatchList.addClause_short {refs : List Nat} (list : WatchList s lit refs)
    (short : lits.size ≤ 1) : WatchList (s.addClause lits original).1 lit refs := by
  refine ⟨list.1, ?_, ?_⟩
  · rw [addClause_first_short short]
    exact list.2.1
  · intro i bound
    have old := list.2.2 i bound
    refine ⟨old.1.addClause lits, ?_⟩
    rw [addClause_db_before _ old.1.2.2.1]
    exact old.2

private theorem clause_watchList_prepend {refs : List Nat} (list : WatchList s lit refs)
    (entry : WatchEntry (s.addClause lits original).1 lit ref)
    (head : (s.addClause lits original).1.first[lit]! = ref)
    (link : (s.addClause lits original).1.db (watchLinkPos ref) = s.first[lit]!)
    (fresh : ref ∉ refs) : WatchList (s.addClause lits original).1 lit (ref :: refs) := by
  refine ⟨List.nodup_cons.mpr ⟨fresh, list.1⟩, ?_, ?_⟩
  · simpa using head
  · intro i bound
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      refine ⟨entry, ?_⟩
      rw [link, list.2.1, List.headD_eq_getD]
    | succ i =>
      have before : i < refs.length := by simpa using bound
      have old := list.2.2 i before
      simp only [List.getD_cons_succ]
      refine ⟨old.1.addClause lits, ?_⟩
      rw [addClause_db_before _ old.1.2.2.1]
      exact old.2

private theorem literal_at_bound (wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit)
    (i : Nat) (bound : i < lits.size) : LiteralBound s.nVars lits[i]! := by
  apply wellFormed
  simpa only [getElem!_pos lits i bound] using Array.getElem_mem bound

theorem WatchList.addClause_first {refs : List Nat} (list : WatchList s lits[0]! refs)
    (arrays : ArrayBounds s) (reserved : 2 ≤ s.arena.size)
    (wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit)
    (wide : 1 < lits.size) (distinct : lits[0]! ≠ lits[1]!) :
    WatchList (s.addClause lits original).1 lits[0]! (2 * (s.arena.size + 2) :: refs) := by
  have packed := addClause_packed (original := original) reserved wellFormed
  rw [addClause_id] at packed
  apply clause_watchList_prepend list (packed.watchEntry_first wide)
  · exact addClause_first_head wide distinct (arrays.literal_index (literal_at_bound wellFormed 0 (by omega))).2
  · simpa using addClause_first_link (s := s) (original := original) wide
  · simpa using list.newRef_not_mem 0 (by decide)

theorem WatchList.addClause_second {refs : List Nat} (list : WatchList s lits[1]! refs)
    (arrays : ArrayBounds s) (reserved : 2 ≤ s.arena.size)
    (wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit)
    (wide : 1 < lits.size) (distinct : lits[0]! ≠ lits[1]!) :
    WatchList (s.addClause lits original).1 lits[1]! ((2 * (s.arena.size + 2) + 1) :: refs) := by
  have packed := addClause_packed (original := original) reserved wellFormed
  rw [addClause_id] at packed
  apply clause_watchList_prepend list (packed.watchEntry_second wide)
  · exact addClause_second_head wide (arrays.literal_index (literal_at_bound wellFormed 1 wide)).2
  · have lower : 2 ≤ s.arena.size + 2 := by omega
    rw [watchLinkPos_odd _ lower]
    simpa using addClause_second_link (s := s) (original := original) wide distinct
  · exact list.newRef_not_mem 1 (by decide)

/-- The mathematical lists represented by inserting the two new clause refs
at distinct literal heads; the runtime stores their first cells and links. -/
def clauseWatchHeads (heads : Nat → List Nat) (clauseId first second lit : Nat) : List Nat :=
  if lit = first then 2 * clauseId :: heads lit
  else if lit = second then (2 * clauseId + 1) :: heads lit
  else heads lit

theorem clauseWatchHeads_source_head {heads : Nat → List Nat} {id first second lit ref : Nat}
    (member : ref ∈ clauseWatchHeads heads id first second lit) :
    ref ∈ heads lit ∨ (ref = 2 * id ∧ lit = first) ∨ (ref = 2 * id + 1 ∧ lit = second) := by
  unfold clauseWatchHeads at member
  split at member
  · rcases List.mem_cons.mp member with same | old
    · exact Or.inr (Or.inl ⟨same, by assumption⟩)
    · exact Or.inl old
  · split at member
    · rcases List.mem_cons.mp member with same | old
      · exact Or.inr (Or.inr ⟨same, by assumption⟩)
      · exact Or.inl old
    · exact Or.inl member

theorem clauseWatchHeads_unique {s : State} {heads : Nat → List Nat}
    (lists : ∀ lit, WatchList s lit (heads lit))
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    (first second : Lit) :
    ∀ lit other ref,
      ref ∈ clauseWatchHeads heads (s.arena.size + 2) first second lit →
      ref ∈ clauseWatchHeads heads (s.arena.size + 2) first second other → lit = other := by
  intro lit other ref left right
  rcases clauseWatchHeads_source_head left with oldLeft | firstLeft | secondLeft
  · rcases clauseWatchHeads_source_head right with oldRight | firstRight | secondRight
    · exact unique lit other ref oldLeft oldRight
    · exact False.elim ((lists lit).newRef_not_mem 0 (by decide) (firstRight.1 ▸ oldLeft))
    · exact False.elim ((lists lit).newRef_not_mem 1 (by decide) (secondRight.1 ▸ oldLeft))
  · rcases clauseWatchHeads_source_head right with oldRight | firstRight | secondRight
    · exact False.elim ((lists other).newRef_not_mem 0 (by decide) (firstLeft.1 ▸ oldRight))
    · exact firstLeft.2.trans firstRight.2.symm
    · omega
  · rcases clauseWatchHeads_source_head right with oldRight | firstRight | secondRight
    · exact False.elim ((lists other).newRef_not_mem 1 (by decide) (secondLeft.1 ▸ oldRight))
    · omega
    · exact secondLeft.2.trans secondRight.2.symm

theorem clauseWatchHeads_mem {heads : Nat → List Nat} {clauseId first second lit ref : Nat}
    (member : ref ∈ heads lit) : ref ∈ clauseWatchHeads heads clauseId first second lit := by
  unfold clauseWatchHeads
  split
  · simp_all
  · split <;> simp_all

theorem ClauseWatches.clauseWatchHeads {heads : Nat → List Nat} {clauseId first second : Nat}
    (watched : ClauseWatches heads clauseId first second) (newId newFirst newSecond : Nat) :
    ClauseWatches (clauseWatchHeads heads newId newFirst newSecond) clauseId first second := by
  refine ⟨watched.1, ?_⟩
  rcases watched.2 with forward | backward
  · exact Or.inl ⟨clauseWatchHeads_mem forward.1, clauseWatchHeads_mem forward.2⟩
  · exact Or.inr ⟨clauseWatchHeads_mem backward.1, clauseWatchHeads_mem backward.2⟩

/-- Actual clause allocation preserves every linked watch list and installs
exactly its two new references at the two distinct watched literal heads. -/
theorem addClause_watchLists (heads : Nat → List Nat) (lists : ∀ lit, WatchList s lit (heads lit))
    (arrays : ArrayBounds s) (reserved : 2 ≤ s.arena.size)
    (wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit)
    (wide : 1 < lits.size) (distinct : lits[0]! ≠ lits[1]!) :
    let updated := clauseWatchHeads heads (s.arena.size + 2) lits[0]! lits[1]!
    (∀ lit, WatchList (s.addClause lits original).1 lit (updated lit)) ∧
      ClauseWatches updated (s.arena.size + 2) lits[0]! lits[1]! := by
  constructor
  · intro lit
    by_cases first : lit = lits[0]!
    · subst lit
      simpa only [clauseWatchHeads, ite_eq_left rfl, ite_true] using
        (lists lits[0]!).addClause_first arrays reserved wellFormed wide distinct
    · by_cases second : lit = lits[1]!
      · subst lit
        simpa only [clauseWatchHeads, ite_eq_right (Ne.symm distinct), ite_eq_left rfl, ite_true] using
          (lists lits[1]!).addClause_second arrays reserved wellFormed wide distinct
      · simpa only [clauseWatchHeads, ite_eq_right first, ite_eq_right second] using
          (lists lit).addClause_other wide (Ne.symm first) (Ne.symm second)
  · refine ⟨distinct, Or.inl ?_⟩
    simp [clauseWatchHeads, Ne.symm distinct]

/-- Unit and empty allocations add no watches. This single statement covers
all widths while the long-clause theorem also supplies the new coverage pair. -/
theorem addClause_watchLists_all (heads : Nat → List Nat) (lists : ∀ lit, WatchList s lit (heads lit))
    (arrays : ArrayBounds s) (reserved : 2 ≤ s.arena.size)
    (wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit)
    (distinct : 1 < lits.size → lits[0]! ≠ lits[1]!) :
    ∀ lit, WatchList (s.addClause lits original).1 lit
      (if 1 < lits.size then clauseWatchHeads heads (s.arena.size + 2) lits[0]! lits[1]! lit else heads lit) := by
  by_cases wide : 1 < lits.size
  · simpa only [ite_eq_left wide] using
      (addClause_watchLists heads lists arrays reserved wellFormed wide (distinct wide)).1
  · intro lit
    rw [ite_eq_right wide]
    exact (lists lit).addClause_short (by omega)

end MicrosatLean.Verification.Implementation.Representation
