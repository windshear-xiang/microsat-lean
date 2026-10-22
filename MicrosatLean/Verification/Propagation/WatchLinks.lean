import MicrosatLean.Verification.Propagation.WatchStep

namespace MicrosatLean.Verification.Propagation

open CDCL Representation

/-- Distinct genuine watch references address distinct header cells. The
arithmetic is false for arbitrary clause suffixes, hence the database premise. -/
theorem storedWatchRef_link_injective {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {left right : Nat}
    (leftProper : StoredWatchRef (original ++ learned) left)
    (rightProper : StoredWatchRef (original ++ learned) right)
    (equal : watchLinkPos left = watchLinkPos right) : left = right := by
  obtain ⟨leftEntry, leftMember, leftId, _⟩ := leftProper
  obtain ⟨rightEntry, rightMember, rightId, _⟩ := rightProper
  have leftLower := (database.layout.packed leftMember).startLower
  have rightLower := (database.layout.packed rightMember).startLower
  simp only [watchClause] at leftId rightId
  unfold watchLinkPos at equal
  by_cases same : leftEntry.id = rightEntry.id
  · omega
  · rcases database.layout.separated leftMember rightMember same with forward | backward <;> omega

theorem storedWatchRef_link_bound {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {ref : Nat}
    (proper : StoredWatchRef (original ++ learned) ref) : watchLinkPos ref < s.arena.size := by
  obtain ⟨entry, member, id, _⟩ := proper
  have packed := database.layout.packed member
  have lower := packed.startLower
  have upper := packed.endBound
  simp only [watchClause] at id
  unfold watchLinkPos
  omega

/-- The pointer component of WatchList, separated from clause membership
while literal cells are temporarily being reoriented by propagation. -/
def WatchLinks (s : State) (lit : Lit) (refs : List Nat) : Prop :=
  refs.Nodup ∧ s.first[lit]! = refs.headD 0 ∧
    ∀ i, i < refs.length → s.db (watchLinkPos (refs.getD i 0)) = refs.getD (i + 1) 0

theorem WatchList.links {s : State} {lit : Lit} {refs : List Nat}
    (list : WatchList s lit refs) : WatchLinks s lit refs :=
  ⟨list.1, list.2.1, fun i bound => (list.2.2 i bound).2⟩

private theorem getD_mem (refs : List Nat) (i : Nat) (bound : i < refs.length) : refs.getD i 0 ∈ refs := by
  have value : refs.getD i 0 = refs[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
  rw [value]
  exact List.getElem_mem bound

theorem WatchLinks.frame {before after : State} {lit : Lit} {refs : List Nat}
    (links : WatchLinks before lit refs) (head : after.first[lit]! = before.first[lit]!)
    (cells : ∀ ref ∈ refs, after.db (watchLinkPos ref) = before.db (watchLinkPos ref)) :
    WatchLinks after lit refs := by
  refine ⟨links.1, head.trans links.2.1, ?_⟩
  intro i within
  rw [cells _ (getD_mem refs i within)]
  exact links.2.2 i within

/-- The actual head-removal/insertion rewiring splices the current ref out of
one finite list and prepends it to the replacement literal's list. Proper
database refs discharge the explicit noncollision premise by injectivity. -/
theorem rewireWatch_head_links {s : State} {lit newLit : Lit} {ref : Nat} {rest target : List Nat}
    (current : WatchLinks s lit (ref :: rest)) (destination : WatchLinks s newLit target)
    (different : lit ≠ newLit) (fresh : ref ∉ target)
    (headBound : lit < s.first.size) (targetBound : newLit < s.first.size)
    (linkBound : watchLinkPos ref < s.arena.size)
    (disjoint : ∀ other ∈ rest ++ target, watchLinkPos ref ≠ watchLinkPos other) :
    let arrays := rewireWatch s.arena s.first lit newLit ref 0
    let after := restoreWatchArrays s arrays.1 arrays.2
    WatchLinks after lit rest ∧ WatchLinks after newLit (ref :: target) := by
  let arrays := rewireWatch s.arena s.first lit newLit ref 0
  let after := restoreWatchArrays s arrays.1 arrays.2
  have next : s.db (watchLinkPos ref) = rest.headD 0 := by
    simpa only [List.getD_cons_zero, List.getD_cons_succ, List.headD_eq_getD] using
      current.2.2 0 (by simp)
  have nextArray : s.arena[watchLinkPos ref]! = rest.headD 0 := next
  have arraysEq : arrays = (s.arena.set! (watchLinkPos ref) s.first[newLit]!,
      (s.first.set! lit (rest.headD 0)).set! newLit ref) := by
    simp only [arrays, rewireWatch, beq_self_eq_true, ite_true,
      Array.getElem!_set!_ne _ _ _ _ different, nextArray]
  have arenaEq : after.arena = s.arena.set! (watchLinkPos ref) s.first[newLit]! := by
    simp only [after, arraysEq, restoreWatchArrays]
  have firstEq : after.first = (s.first.set! lit (rest.headD 0)).set! newLit ref := by
    simp only [after, arraysEq, restoreWatchArrays]
  have keep (other : Nat) (member : other ∈ rest ++ target) :
      after.db (watchLinkPos other) = s.db (watchLinkPos other) := by
    exact (congrArg (fun arena : Array Nat => arena[watchLinkPos other]!) arenaEq).trans
      (Array.getElem!_set!_ne _ _ _ _ (disjoint other member))
  constructor
  · refine ⟨(List.nodup_cons.mp current.1).2, ?_, ?_⟩
    · rw [firstEq, Array.getElem!_set!_ne _ _ _ _ (Ne.symm different)]
      exact Array.getElem!_set!_self _ _ _ headBound
    · intro i within
      rw [keep _ (List.mem_append_left _ (getD_mem rest i within))]
      simpa only [List.getD_cons_succ, Nat.add_assoc] using current.2.2 (i + 1) (by simp; omega)
  · refine ⟨List.nodup_cons.mpr ⟨fresh, destination.1⟩, ?_, ?_⟩
    · rw [firstEq]
      exact Array.getElem!_set!_self _ _ _ (by simpa using targetBound)
    · intro i within
      cases i with
      | zero =>
        simp only [List.getD_cons_zero, List.getD_cons_succ]
        change after.arena[watchLinkPos ref]! = _
        rw [arenaEq, Array.getElem!_set!_self _ _ _ linkBound, destination.2.1, List.headD_eq_getD]
      | succ i =>
        have before : i < target.length := by simpa using within
        simp only [List.getD_cons_succ]
        rw [keep _ (List.mem_append_right _ (getD_mem target i before))]
        exact destination.2.2 i before

theorem rewireWatch_head_links_proper {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {lit newLit : Lit} {ref : Nat} {rest target : List Nat}
    (current : WatchLinks s lit (ref :: rest)) (destination : WatchLinks s newLit target)
    (proper : ∀ other ∈ ref :: (rest ++ target), StoredWatchRef (original ++ learned) other)
    (different : lit ≠ newLit) (fresh : ref ∉ target)
    (headBound : lit < s.first.size) (targetBound : newLit < s.first.size) :
    let arrays := rewireWatch s.arena s.first lit newLit ref 0
    let after := restoreWatchArrays s arrays.1 arrays.2
    WatchLinks after lit rest ∧ WatchLinks after newLit (ref :: target) := by
  have currentProper := proper ref (by simp)
  apply rewireWatch_head_links current destination different fresh headBound targetBound
    (storedWatchRef_link_bound database currentProper)
  intro other member equal
  have same := storedWatchRef_link_injective database currentProper (proper other (by simp [member])) equal
  subst other
  rcases List.mem_append.mp member with inRest | inTarget
  · exact (List.nodup_cons.mp current.1).1 inRest
  · exact fresh inTarget

/-- Every other head and every link on its list are retained by head-splice
rewiring. Cross-head uniqueness plus proper-ref injectivity supplies safety. -/
theorem rewireWatch_head_other_links {s : State} {lit newLit other : Lit} {ref : Nat} {refs : List Nat}
    (links : WatchLinks s other refs) (sourceDifferent : lit ≠ other) (targetDifferent : newLit ≠ other)
    (disjoint : ∀ old ∈ refs, watchLinkPos ref ≠ watchLinkPos old) :
    let arrays := rewireWatch s.arena s.first lit newLit ref 0
    WatchLinks (restoreWatchArrays s arrays.1 arrays.2) other refs := by
  apply links.frame
  · simp only [restoreWatchArrays, rewireWatch, beq_self_eq_true, ite_true]
    rw [Array.getElem!_set!_ne _ _ _ _ targetDifferent,
      Array.getElem!_set!_ne _ _ _ _ sourceDifferent]
  · intro old member
    simp only [restoreWatchArrays, rewireWatch, beq_self_eq_true, ite_true, State.db]
    exact Array.getElem!_set!_ne _ _ _ _ (disjoint old member)

end MicrosatLean.Verification.Propagation
