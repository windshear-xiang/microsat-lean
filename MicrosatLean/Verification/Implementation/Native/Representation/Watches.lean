import MicrosatLean.Verification.Implementation.Native.Representation.Arena

namespace MicrosatLean.Verification.Implementation.Native.Representation

open CDCL

/-- A link-cell write misses every link and watched-literal cell used by a
list. This is automatic for a fresh clause header beyond the old arena. -/
def WatchWriteDisjoint (position : Nat) (refs : List Nat) : Prop :=
  ∀ ref ∈ refs, position ≠ watchLinkPos ref ∧
    position ≠ watchClause ref ∧ position ≠ watchClause ref + 1

variable {s : State} {lit other : Lit} {ref oldRef position : Nat} {refs : List Nat}

@[simp] theorem addWatch_head (bound : lit < s.first.size) :
    (s.addWatch lit ref).first[lit]! = ref := by
  exact Array.getElem!_set!_self s.first lit ref bound

theorem addWatch_other_head (different : lit ≠ other) :
    (s.addWatch lit ref).first[other]! = s.first[other]! := by
  exact Array.getElem!_set!_ne s.first lit other ref different

theorem addWatch_link (bound : watchLinkPos ref < s.arena.size) :
    (s.addWatch lit ref).db (watchLinkPos ref) = s.first[lit]! := by
  exact Array.getElem!_set!_self s.arena _ _ bound

theorem addWatch_db_other (different : watchLinkPos ref ≠ position) :
    (s.addWatch lit ref).db position = s.db position := by
  exact Array.getElem!_set!_ne s.arena _ _ _ different

private theorem watchLinkPos_before_clause (ref : Nat) (lower : 4 ≤ watchClause ref) :
    watchLinkPos ref < watchClause ref := by
  unfold watchLinkPos watchClause at *
  omega

theorem WatchEntry.addWatch (entry : WatchEntry s other oldRef)
    (first : watchLinkPos ref ≠ watchClause oldRef)
    (second : watchLinkPos ref ≠ watchClause oldRef + 1) :
    WatchEntry (s.addWatch lit ref) other oldRef := by
  rcases entry with ⟨lower, upper, link, watched⟩
  refine ⟨lower, ?_, ?_, ?_⟩
  · simpa [State.addWatch] using upper
  · simpa [State.addWatch] using link
  · rwa [addWatch_db_other first, addWatch_db_other second]

theorem WatchEntry.addWatch_self (entry : WatchEntry s lit ref) :
    WatchEntry (s.addWatch lit ref) lit ref := by
  have before := watchLinkPos_before_clause ref entry.1
  apply entry.addWatch <;> omega

private theorem getD_mem (refs : List Nat) (i : Nat) (bound : i < refs.length) :
    refs.getD i 0 ∈ refs := by
  have value : refs.getD i 0 = refs[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
  rw [value]
  exact List.getElem_mem bound

theorem WatchList.addWatch (list : WatchList s lit refs)
    (headBound : lit < s.first.size) (linkBound : watchLinkPos ref < s.arena.size)
    (entry : WatchEntry s lit ref) (disjoint : WatchWriteDisjoint (watchLinkPos ref) refs) :
    WatchList (s.addWatch lit ref) lit (ref :: refs) := by
  have fresh : ref ∉ refs := fun member => (disjoint ref member).1 rfl
  refine ⟨List.nodup_cons.mpr ⟨fresh, list.1⟩, ?_, ?_⟩
  · simpa using addWatch_head headBound (ref := ref)
  · intro i bound
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, List.getD_cons_succ]
      refine ⟨entry.addWatch_self, ?_⟩
      rw [addWatch_link linkBound, list.2.1, List.headD_eq_getD]
    | succ i =>
      have before : i < refs.length := by simpa using bound
      have old := list.2.2 i before
      have safe := disjoint _ (getD_mem refs i before)
      simp only [List.getD_cons_succ]
      refine ⟨old.1.addWatch safe.2.1 safe.2.2, ?_⟩
      rw [addWatch_db_other safe.1]
      exact old.2

theorem WatchList.addWatch_other (list : WatchList s other refs) (different : lit ≠ other)
    (disjoint : WatchWriteDisjoint (watchLinkPos ref) refs) :
    WatchList (s.addWatch lit ref) other refs := by
  refine ⟨list.1, ?_, ?_⟩
  · rw [addWatch_other_head different]
    exact list.2.1
  · intro i bound
    have old := list.2.2 i bound
    have safe := disjoint _ (getD_mem refs i bound)
    refine ⟨old.1.addWatch safe.2.1 safe.2.2, ?_⟩
    rw [addWatch_db_other safe.1]
    exact old.2

/-- No cell read by an existing watch entry reaches a newly appended header. -/
theorem WatchList.writeDisjoint_after (list : WatchList s lit refs) (fresh : s.arena.size ≤ position) :
    WatchWriteDisjoint position refs := by
  intro ref member
  obtain ⟨i, bound, value⟩ := List.getElem_of_mem member
  have atIndex : refs.getD i 0 = ref := by
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound] using value
  have entry := (list.2.2 i bound).1
  rw [atIndex] at entry
  rcases entry with ⟨_, upper, link, _⟩
  exact ⟨by omega, by omega, by omega⟩

end MicrosatLean.Verification.Implementation.Native.Representation
