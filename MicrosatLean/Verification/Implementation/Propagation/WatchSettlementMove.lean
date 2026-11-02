import MicrosatLean.Verification.Implementation.Propagation.WatchSettlement

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL Representation Analysis

theorem falseBefore_marked {s : State} (active : ActiveTrail s) {count : Nat}
    (bound : count ≤ s.assigned) {lit : Lit} (falseLit : FalseBefore s count lit) :
    s.mark lit ≠ 0 := by
  obtain ⟨i, before, value⟩ := falseLit
  simpa only [value] using (active i (Nat.lt_of_lt_of_le before bound)).2.1

theorem trueBefore_unmarked {s : State} (active : ActiveTrail s) {lit : Lit}
    (truth : TrueBefore s s.assigned lit) : s.mark lit = 0 := by
  obtain ⟨i, before, value⟩ := truth
  simpa only [value, negate_negate] using (active i before).2.2

/-- A clause's two distinct watch slots cannot share a literal head. -/
theorem watch_same_head_ref_eq {heads : Nat → List Nat}
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    {id first second lit left right : Nat} (covered : ClauseWatches heads id first second)
    (leftId : watchClause left = id) (rightId : watchClause right = id)
    (leftMember : left ∈ heads lit) (rightMember : right ∈ heads lit) : left = right := by
  have leftEncoding : left = 2 * id ∨ left = 2 * id + 1 := by
    simp only [watchClause] at leftId; omega
  have rightEncoding : right = 2 * id ∨ right = 2 * id + 1 := by
    simp only [watchClause] at rightId; omega
  have distinctHeads : ¬ (2 * id ∈ heads lit ∧ 2 * id + 1 ∈ heads lit) := by
    rintro ⟨even, odd⟩
    rcases covered.2 with forward | backward
    · exact covered.1 ((unique lit first _ even forward.1).symm.trans
        (unique lit second _ odd forward.2))
    · exact covered.1 ((unique lit first _ odd backward.2).symm.trans
        (unique lit second _ even backward.1))
  rcases leftEncoding with rfl | rfl <;> rcases rightEncoding with rfl | rfl
  · rfl
  · exact False.elim (distinctHeads ⟨leftMember, rightMember⟩)
  · exact False.elim (distinctHeads ⟨rightMember, leftMember⟩)
  · rfl

theorem otherWatch_opposite {lits : Array Lit} {lit query : Lit}
    (distinct : lits[0]! ≠ lits[1]!)
    (watched : lit = lits[0]! ∨ lit = lits[1]!)
    (queried : query = lits[0]! ∨ query = lits[1]!) (different : query ≠ lit) :
    otherWatch lits query = lit := by
  rcases watched with rfl | rfl
  · rcases queried with rfl | rfl
    · exact False.elim (different rfl)
    · simp [otherWatch, distinct]
  · rcases queried with rfl | rfl
    · simp [otherWatch]
    · exact False.elim (different rfl)

/-- Every retained settled reference survives an actual move. A retained slot
of the moved clause itself would claim that the current false literal is true,
so that case is ruled out by the active trail rather than a postcondition. -/
theorem SettledWatch.move_other {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (active : ActiveTrail s)
    {target : StoredClause} (targetMember : target ∈ original ++ learned)
    {lit : Lit} {moved : Nat} (current : moved ∈ heads lit)
    (movedId : watchClause moved = target.id) (wide : 2 ≤ target.lits.size)
    (falseLit : s.mark lit ≠ 0)
    {query : Lit} {ref : Nat} (member : ref ∈ heads query) (different : ref ≠ moved)
    (settled : SettledWatch s (original ++ learned) s.assigned query ref)
    (offset : Nat) (first : Bool) (arena firstHeads : Array Nat) :
    SettledWatch (restoreWatchArrays s arena firstHeads)
      ((original ++ learned).map (moveWatchEntry target.id offset first)) s.assigned query ref := by
  intro changed changedMember id
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp changedMember
  have oldId : watchClause ref = old.id := by simpa only [moveWatchEntry_id] using id
  have truth := settled old oldMember oldId
  by_cases same : old.id = target.id
  · have equal := database.layout.entry_eq_of_id oldMember targetMember same
    subst old
    have queried := watch_ref_literals database certificate targetMember member oldId wide
    have watched := watch_ref_literals database certificate targetMember current movedId wide
    have queryDifferent : query ≠ lit := by
      intro equal
      subst query
      exact different (watch_same_head_ref_eq certificate.unique
        (certificate.covered target targetMember wide) oldId movedId member current)
    have trueLit : TrueBefore s s.assigned lit := by
      simpa only [otherWatch_opposite (certificate.covered target targetMember wide).1 watched queried queryDifferent] using truth
    exact False.elim (falseLit (trueBefore_unmarked active trueLit))
  · rw [moveWatchEntry_of_ne _ _ _ _ same]
    exact truth

theorem SettledPrefix.move {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (active : ActiveTrail s)
    {target : StoredClause} (targetMember : target ∈ original ++ learned)
    {lit newLit : Lit} {moved : Nat} (current : moved ∈ heads lit)
    (movedId : watchClause moved = target.id) (wide : 2 ≤ target.lits.size)
    (falseLit : s.mark lit ≠ 0) (unmarked : s.mark newLit = 0)
    {count : Nat} (bound : count ≤ s.assigned)
    (settled : SettledPrefix s (original ++ learned) heads count)
    (offset : Nat) (first : Bool) (arena firstHeads : Array Nat) :
    SettledPrefix (restoreWatchArrays s arena firstHeads)
      ((original ++ learned).map (moveWatchEntry target.id offset first))
      (moveHeads heads newLit moved) count := by
  intro query falseQuery ref member
  have queryDifferent : query ≠ newLit := by
    intro equal
    exact falseBefore_marked active bound falseQuery ((congrArg s.mark equal).trans unmarked)
  have retained : ref ≠ moved ∧ ref ∈ heads query := by
    rcases (moveHeads_mem_iff (fun lit => (certificate.links lit).1) _ _ _ _).mp member with new | old
    · exact False.elim (queryDifferent new.2)
    · exact old
  exact (settled query falseQuery ref retained.2).move_other database certificate active targetMember
    current movedId wide falseLit retained.2 retained.1 offset first arena firstHeads

theorem SettledCursor.move {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (active : ActiveTrail s)
    {target : StoredClause} (targetMember : target ∈ original ++ learned)
    {lit newLit : Lit} {moved : Nat} {rest : List Nat} (current : moved ∈ heads lit)
    (movedId : watchClause moved = target.id) (wide : 2 ≤ target.lits.size)
    (falseLit : s.mark lit ≠ 0) (unmarked : s.mark newLit = 0)
    (settled : SettledCursor s (original ++ learned) heads lit (moved :: rest))
    (offset : Nat) (first : Bool) (arena firstHeads : Array Nat) :
    SettledCursor (restoreWatchArrays s arena firstHeads)
      ((original ++ learned).map (moveWatchEntry target.id offset first))
      (moveHeads heads newLit moved) lit rest := by
  intro ref member absent
  have different : lit ≠ newLit := fun equal => falseLit ((congrArg s.mark equal).trans unmarked)
  have retained : ref ≠ moved ∧ ref ∈ heads lit := by
    rcases (moveHeads_mem_iff (fun lit => (certificate.links lit).1) _ _ _ _).mp member with new | old
    · exact False.elim (different new.2)
    · exact old
  have visited := settled ref retained.2 (by
    simp only [List.mem_cons, retained.1, false_or]
    exact absent)
  exact visited.move_other database certificate active targetMember current movedId wide falseLit
    retained.2 retained.1 offset first arena firstHeads

end MicrosatLean.Verification.Implementation.Propagation
