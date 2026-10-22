import MicrosatLean.Verification.Propagation.WatchChain

namespace MicrosatLean.Verification.Propagation

open CDCL Representation

/-- The actual nonhead update removes the ref after `previous`, preserves
the preceding chain, and prepends that ref to the replacement literal list. -/
theorem rewireWatch_nonhead_links {s : State} {lit newLit : Lit} {previous ref : Nat}
    {initial rest target : List Nat} (current : WatchLinks s lit (initial ++ previous :: ref :: rest))
    (destination : WatchLinks s newLit target) (nonzero : previous ≠ 0)
    (different : lit ≠ newLit) (fresh : ref ∉ target) (targetBound : newLit < s.first.size)
    (previousBound : watchLinkPos previous < s.arena.size) (refBound : watchLinkPos ref < s.arena.size)
    (separate : watchLinkPos ref ≠ watchLinkPos previous)
    (disjoint : ∀ old ∈ (initial ++ rest) ++ target,
      watchLinkPos previous ≠ watchLinkPos old ∧ watchLinkPos ref ≠ watchLinkPos old) :
    let arrays := rewireWatch s.arena s.first lit newLit ref previous
    let after := restoreWatchArrays s arrays.1 arrays.2
    WatchLinks after lit (initial ++ previous :: rest) ∧ WatchLinks after newLit (ref :: target) := by
  let arrays := rewireWatch s.arena s.first lit newLit ref previous
  let after := restoreWatchArrays s arrays.1 arrays.2
  have tail := current.chain.suffix initial (previous :: ref :: rest)
  have nextArray : s.arena[watchLinkPos ref]! = rest.headD 0 := tail.2.1
  have arraysEq : arrays = ((s.arena.set! (watchLinkPos previous) (rest.headD 0)).set!
      (watchLinkPos ref) s.first[newLit]!, s.first.set! newLit ref) := by
    simp only [arrays, rewireWatch, beq_iff_eq, nonzero, ite_false, nextArray]
  have arenaEq : after.arena = (s.arena.set! (watchLinkPos previous) (rest.headD 0)).set!
      (watchLinkPos ref) s.first[newLit]! := by simp only [after, arraysEq, restoreWatchArrays]
  have firstEq : after.first = s.first.set! newLit ref := by simp only [after, arraysEq, restoreWatchArrays]
  have keep (old : Nat) (member : old ∈ (initial ++ rest) ++ target) :
      after.db (watchLinkPos old) = s.db (watchLinkPos old) := by
    change after.arena[watchLinkPos old]! = _
    rw [arenaEq, Array.getElem!_set!_ne _ _ _ _ (disjoint old member).2,
      Array.getElem!_set!_ne _ _ _ _ (disjoint old member).1]
    rfl
  have predecessor : after.db (watchLinkPos previous) = rest.headD 0 := by
    change after.arena[watchLinkPos previous]! = _
    rw [arenaEq, Array.getElem!_set!_ne _ _ _ _ separate,
      Array.getElem!_set!_self _ _ _ previousBound]
  constructor
  · have retained : (initial ++ previous :: rest).Sublist (initial ++ previous :: ref :: rest) :=
      (List.Sublist.cons_cons previous (List.Sublist.cons ref (List.Sublist.refl rest))).append_left initial
    refine ⟨retained.nodup current.1, ?_, ?_⟩
    · rw [firstEq, Array.getElem!_set!_ne _ _ _ _ (Ne.symm different), current.2.1]
      cases initial <;> rfl
    · apply (watchChain_iff _).mp
      apply current.chain.splice initial previous ref rest predecessor
      intro old member
      exact keep old (List.mem_append_left _ member)
  · refine ⟨List.nodup_cons.mpr ⟨fresh, destination.1⟩, ?_, ?_⟩
    · rw [firstEq]
      exact Array.getElem!_set!_self _ _ _ targetBound
    · apply (watchChain_iff _).mp
      constructor
      · change after.arena[watchLinkPos ref]! = _
        rw [arenaEq, Array.getElem!_set!_self _ _ _ (by simpa using refBound), destination.2.1]
      · exact destination.chain.frame (fun old member => keep old (List.mem_append_right _ member))

/-- For genuine database refs, list uniqueness and absence from the target
head discharge every header noncollision obligation of the concrete splice. -/
theorem rewireWatch_nonhead_links_proper {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {lit newLit : Lit} {previous ref : Nat}
    {initial rest target : List Nat} (current : WatchLinks s lit (initial ++ previous :: ref :: rest))
    (destination : WatchLinks s newLit target)
    (proper : ∀ old ∈ (initial ++ previous :: ref :: rest) ++ target,
      StoredWatchRef (original ++ learned) old)
    (different : lit ≠ newLit) (fresh : ref ∉ target) (previousFresh : previous ∉ target)
    (targetBound : newLit < s.first.size) :
    let arrays := rewireWatch s.arena s.first lit newLit ref previous
    let after := restoreWatchArrays s arrays.1 arrays.2
    WatchLinks after lit (initial ++ previous :: rest) ∧ WatchLinks after newLit (ref :: target) := by
  have previousMember : previous ∈ (initial ++ previous :: ref :: rest) ++ target := by simp
  have refMember : ref ∈ (initial ++ previous :: ref :: rest) ++ target := by simp
  have previousProper := proper previous previousMember
  have refProper := proper ref refMember
  have nonzero : previous ≠ 0 := by
    obtain ⟨entry, member, id, _⟩ := previousProper
    have lower := (database.layout.packed member).startLower
    simp only [watchClause] at id
    omega
  have parts := List.nodup_append.mp current.1
  have tail := List.nodup_cons.mp parts.2.1
  have last := List.nodup_cons.mp tail.2
  have previousDifferent : previous ≠ ref := fun same => tail.1 (by simp [same])
  have previousNot : previous ∉ initial ++ rest := by
    intro member
    rcases List.mem_append.mp member with before | after
    · exact parts.2.2 previous before previous (by simp) rfl
    · exact tail.1 (by simp [after])
  have refNot : ref ∉ initial ++ rest := by
    intro member
    rcases List.mem_append.mp member with before | after
    · exact parts.2.2 ref before ref (by simp) rfl
    · exact last.1 after
  apply rewireWatch_nonhead_links current destination nonzero different fresh targetBound
    (storedWatchRef_link_bound database previousProper) (storedWatchRef_link_bound database refProper)
  · intro equal
    exact previousDifferent (storedWatchRef_link_injective database refProper previousProper equal).symm
  · intro old member
    have oldProper : StoredWatchRef (original ++ learned) old := by
      apply proper old
      simp only [List.mem_append, List.mem_cons] at member ⊢
      rcases member with (before | after) | destination
      · exact Or.inl (Or.inl before)
      · exact Or.inl (Or.inr (Or.inr (Or.inr after)))
      · exact Or.inr destination
    have previousNe : previous ≠ old := by
      intro equal
      subst old
      exact (List.mem_append.mp member).elim previousNot previousFresh
    have refNe : ref ≠ old := by
      intro equal
      subst old
      exact (List.mem_append.mp member).elim refNot fresh
    exact ⟨fun equal => previousNe (storedWatchRef_link_injective database previousProper oldProper equal),
      fun equal => refNe (storedWatchRef_link_injective database refProper oldProper equal)⟩

theorem rewireWatch_nonhead_other_links {s : State} {lit newLit other : Lit} {previous ref : Nat}
    {refs : List Nat} (links : WatchLinks s other refs) (nonzero : previous ≠ 0)
    (targetDifferent : newLit ≠ other)
    (disjoint : ∀ old ∈ refs, watchLinkPos previous ≠ watchLinkPos old ∧ watchLinkPos ref ≠ watchLinkPos old) :
    let arrays := rewireWatch s.arena s.first lit newLit ref previous
    WatchLinks (restoreWatchArrays s arrays.1 arrays.2) other refs := by
  apply links.frame
  · simp only [restoreWatchArrays, rewireWatch, beq_iff_eq, nonzero, ite_false]
    exact Array.getElem!_set!_ne _ _ _ _ targetDifferent
  · intro old member
    simp only [restoreWatchArrays, rewireWatch, beq_iff_eq, nonzero, ite_false, State.db]
    rw [Array.getElem!_set!_ne _ _ _ _ (disjoint old member).2,
      Array.getElem!_set!_ne _ _ _ _ (disjoint old member).1]

end MicrosatLean.Verification.Propagation
