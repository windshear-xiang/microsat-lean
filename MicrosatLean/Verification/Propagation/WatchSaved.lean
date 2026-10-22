import MicrosatLean.Verification.Analysis.WatchHistory
import MicrosatLean.Verification.Propagation.WatchSettlementMove

namespace MicrosatLean.Verification.Propagation

open CDCL Representation Analysis

theorem settledWatch_retain_at {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    {target : StoredClause} (targetMember : target ∈ original ++ learned)
    {count : Nat} {query : Lit} {ref : Nat} (current : ref ∈ heads query)
    (settled : SettledWatch s (original ++ learned) count query ref)
    (first : Bool) (arena : Array Nat) :
    SettledWatch { s with arena := arena }
      ((original ++ learned).map (retainWatchEntry target.id first)) count query ref := by
  intro changed changedMember id
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp changedMember
  have oldId : watchClause ref = old.id := by simpa only [retainWatchEntry_id] using id
  have truth := settled old member oldId
  by_cases same : old.id = target.id
  · have equal := database.layout.entry_eq_of_id member targetMember same
    subst old
    obtain ⟨proper, properMember, properId, wide⟩ := certificate.references query ref current
    have equal := database.layout.entry_eq_of_id properMember targetMember (properId.symm.trans oldId)
    subst proper
    rw [otherWatch_retainWatchEntry target first wide (certificate.covered target targetMember wide).1
      (watch_ref_literals database certificate targetMember current oldId wide)]
    exact truth
  · rw [retainWatchEntry_of_ne _ _ _ same]
    exact truth

theorem settledWatches_retain {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    {target : StoredClause} (targetMember : target ∈ original ++ learned) {count : Nat}
    (settled : SettledWatches s (original ++ learned) heads count) (first : Bool) (arena : Array Nat) :
    SettledWatches { s with arena := arena }
      ((original ++ learned).map (retainWatchEntry target.id first)) heads count := by
  intro lit falseLit ref member
  exact settledWatch_retain_at database certificate targetMember member (settled lit falseLit ref member) first arena

theorem settledWatch_move_other_at {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (active : ActiveTrail s)
    {target : StoredClause} (targetMember : target ∈ original ++ learned)
    {lit : Lit} {moved : Nat} (current : moved ∈ heads lit)
    (movedId : watchClause moved = target.id) (wide : 2 ≤ target.lits.size) (falseLit : s.mark lit ≠ 0)
    {count : Nat} (bound : count ≤ s.assigned)
    {query : Lit} {ref : Nat} (member : ref ∈ heads query) (different : ref ≠ moved)
    (settled : SettledWatch s (original ++ learned) count query ref)
    (offset : Nat) (first : Bool) (arena firstHeads : Array Nat) :
    SettledWatch (restoreWatchArrays s arena firstHeads)
      ((original ++ learned).map (moveWatchEntry target.id offset first)) count query ref := by
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
    have trueLit : TrueBefore s count lit := by
      simpa only [otherWatch_opposite (certificate.covered target targetMember wide).1 watched queried queryDifferent] using truth
    obtain ⟨i, before, value⟩ := trueLit
    exact False.elim (falseLit (trueBefore_unmarked active ⟨i, Nat.lt_of_lt_of_le before bound, value⟩))
  · rw [moveWatchEntry_of_ne _ _ _ _ same]
    exact truth

theorem settledWatches_move {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (active : ActiveTrail s)
    {target : StoredClause} (targetMember : target ∈ original ++ learned)
    {lit newLit : Lit} {moved : Nat} (current : moved ∈ heads lit)
    (movedId : watchClause moved = target.id) (wide : 2 ≤ target.lits.size)
    (falseLit : s.mark lit ≠ 0) (unmarked : s.mark newLit = 0)
    {count : Nat} (bound : count ≤ s.assigned) (settled : SettledWatches s (original ++ learned) heads count)
    (offset : Nat) (first : Bool) (arena firstHeads : Array Nat) :
    SettledWatches (restoreWatchArrays s arena firstHeads)
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
  exact settledWatch_move_other_at database certificate active targetMember current movedId wide falseLit bound
    retained.2 retained.1 (settled query falseQuery ref retained.2) offset first arena firstHeads

end MicrosatLean.Verification.Propagation
