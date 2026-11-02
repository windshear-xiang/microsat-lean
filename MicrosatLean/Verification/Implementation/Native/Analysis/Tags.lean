import MicrosatLean.Verification.Implementation.Native.Analysis.Resolution

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation
open Std.Sat

def ValidMarkTags (snapshot : State) (count : Nat) (s : State) : Prop :=
  ∀ lit, TrailMember snapshot count lit →
    s.mark lit = 0 ∨ s.mark lit = 1 ∨ s.mark lit = 2 ∨ s.mark lit = 5 ∨ s.mark lit = 6

/-- An original root entry either retains tag six or has already been popped
and cleared. The cursor condition prevents a later reason from marking a
cleared root again: all reason tails precede the current candidate. -/
def RootTagBoundary (snapshot : State) (count roots : Nat) (s : State) : Prop :=
  ∀ i, i < roots → i < count → s.mark snapshot.trail[i]! = 6 ∨
    (s.assigned ≤ i ∧ s.mark snapshot.trail[i]! = 0)

theorem RootTagBoundary.not_mark_two {snapshot s : State} {count roots i : Nat}
    (boundary : RootTagBoundary snapshot count roots s) (root : i < roots) (before : i < count) :
    s.mark snapshot.trail[i]! ≠ 2 := by
  rcases boundary i root before with six | ⟨_, zero⟩ <;> omega

theorem markClause_validTags {snapshot s : State} {count clauseId : Nat} {lits : Array Lit}
    (tags : ValidMarkTags snapshot count s) (packed : PackedClause s clauseId lits)
    (arrays : ArrayBounds s) (offset : Nat) (inside : offset ≤ lits.size) :
    ValidMarkTags snapshot count (markClause s (clauseId + offset)) := by
  intro lit member
  rw [markClause_mark_suffix packed arrays offset inside]
  split
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact tags lit member

private theorem unassign_mark_self (s : State) (lit : Lit) : (s.unassign lit).mark lit = 0 := by
  by_cases bound : lit < s.marks.size
  · exact unassign_mark_same bound
  · simp [State.unassign, State.setMark, State.mark, Array.setIfInBounds, bound]

private theorem unassign_validTags {snapshot s : State} {count : Nat}
    (tags : ValidMarkTags snapshot count s) (target : Lit) :
    ValidMarkTags snapshot count (s.unassign target) := by
  intro lit member
  by_cases same : target = lit
  · subst lit
    exact Or.inl (unassign_mark_self s target)
  · rw [unassign_mark_other same]
    exact tags lit member

private structure TagFacts (snapshot : State) (count roots : Nat) (s : State) : Prop where
  storage : ReasonStorage snapshot s
  trail : s.trail = snapshot.trail
  vars : s.nVars = snapshot.nVars
  arrays : ArrayBounds s
  tags : ValidMarkTags snapshot count s
  boundary : RootTagBoundary snapshot count roots s

private theorem TagFacts.transport {snapshot before after : State} {count roots : Nat}
    (facts : TagFacts snapshot count roots before) (frame : ResolutionFrame before after)
    (tags : ValidMarkTags snapshot count after) (boundary : RootTagBoundary snapshot count roots after) :
    TagFacts snapshot count roots after :=
  ⟨frame.reasonStorage facts.storage, frame.trail.trans facts.trail, frame.nVars.trans facts.vars,
    frame.arrayBounds facts.arrays, tags, boundary⟩

private theorem TagFacts.setAssigned {snapshot s : State} {count roots : Nat}
    (facts : TagFacts snapshot count roots s) (p : Nat) (earlier : p ≤ s.assigned) :
    TagFacts snapshot count roots { s with assigned := p } := by
  apply facts.transport (resolutionFrame_setAssigned s p) facts.tags
  intro i root before
  rcases facts.boundary i root before with six | ⟨popped, zero⟩
  · exact Or.inl six
  · exact Or.inr ⟨Nat.le_trans earlier popped, zero⟩

private theorem TagFacts.unassign {formula : Std.Sat.CNF Nat} {snapshot s : State} {count roots : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (facts : TagFacts snapshot count roots s) (p : Nat) (before : p < count)
    (candidate : s.assigned = p) : TagFacts snapshot count roots (s.unassign snapshot.trail[p]!) := by
  apply facts.transport (resolutionFrame_setMark s _ 0) (unassign_validTags facts.tags _)
  intro i root inRange
  change (s.unassign snapshot.trail[p]!).mark snapshot.trail[i]! = 6 ∨
    (s.unassign snapshot.trail[p]!).assigned ≤ i ∧ (s.unassign snapshot.trail[p]!).mark snapshot.trail[i]! = 0
  by_cases same : snapshot.trail[p]! = snapshot.trail[i]!
  · have positions : p = i := by
      have h := congrArg rank same
      rw [graph.ranks p before, graph.ranks i inRange] at h
      exact h
    exact Or.inr ⟨by simpa only [State.unassign, State.setMark, candidate, positions] using Nat.le_refl i,
      by rw [← same]; exact unassign_mark_self s _⟩
  · rw [unassign_mark_other same]
    exact facts.boundary i root inRange

private theorem TagFacts.expandReason {formula : Std.Sat.CNF Nat} {snapshot s : State} {count roots : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (facts : TagFacts snapshot count roots s) (p : Nat) (before : p < count)
    (candidate : s.assigned = p) (nondecision : s.reason snapshot.trail[p]! ≠ 0) :
    TagFacts snapshot count roots (markClause s (s.reason snapshot.trail[p]! + 1)) := by
  let lit := snapshot.trail[p]!
  have known : TrailMember snapshot count lit := ⟨p, before, rfl⟩
  have reasonId := facts.storage.reason lit
  have snapshotReason : snapshot.reason lit ≠ 0 := by rw [← reasonId]; exact nondecision
  obtain ⟨lits, packed, nonempty, _, _, tails⟩ := graph.clause_of_member known snapshotReason
  have packedCurrent : PackedClause s (s.reason lit) lits := by
    rw [reasonId]
    exact facts.storage.packed facts.vars packed
  have inside : 1 ≤ lits.size := by omega
  apply facts.transport (resolutionFrame_markClause s _) (markClause_validTags facts.tags packedCurrent facts.arrays 1 inside)
  intro i root inRange
  rcases facts.boundary i root inRange with six | ⟨popped, zero⟩
  · exact Or.inl (markClause_mark_root packedCurrent facts.arrays 1 inside six)
  · have outside : snapshot.trail[i]! ∉ lits.toList.drop 1 := by
      intro member
      obtain ⟨j, bound, value⟩ := List.mem_drop_iff_getElem.mp member
      have tailBound : 1 + j < lits.size := by simpa only [Array.length_toList, Nat.add_comm] using bound
      have equal : lits[1 + j]! = snapshot.trail[i]! := by
        simpa only [Array.getElem_toList, getElem!_pos lits (1 + j) tailBound] using value
      have earlier := (tails (1 + j) (by omega) tailBound).2
      rw [equal, graph.ranks i inRange, graph.ranks p before] at earlier
      rw [candidate] at popped
      omega
    refine Or.inr ⟨by simpa only [markClause_assigned] using popped, ?_⟩
    rw [markClause_mark_outside packedCurrent facts.arrays 1 inside outside]
    exact zero

private theorem resolutionBody_tags {formula : Std.Sat.CNF Nat} {snapshot s : State} {count roots : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (facts : TagFacts snapshot count roots s) (positive : 0 < s.assigned) (bound : s.assigned ≤ count) :
    TagFacts snapshot count roots (resolutionBody s).value := by
  let p := s.assigned - 1
  let popped := { s with assigned := p }
  let lit := s.trail[p]!
  have read : lit = snapshot.trail[p]! := by simp only [lit, facts.trail]
  have pBound : p < count := by dsimp only [p]; omega
  have popFacts : TagFacts snapshot count roots popped := facts.setAssigned p (Nat.sub_le _ _)
  simp only [resolutionBody, Id.run, pure]
  change TagFacts snapshot count roots
    (if popped.reason lit == 0 then ForInStep.done popped
    else if popped.mark lit == 2 then
      if firstUIP popped p then ForInStep.done popped
      else ForInStep.yield ((markClause popped (popped.reason lit + 1)).unassign lit)
    else ForInStep.yield (popped.unassign lit)).value
  split
  · exact popFacts
  · have nondecision : popped.reason snapshot.trail[p]! ≠ 0 := by
      simpa only [← read, beq_iff_eq] using ‹¬ (popped.reason lit == 0) = true›
    split
    · split
      · exact popFacts
      · have expanded := popFacts.expandReason graph p pBound rfl nondecision
        have cleared := expanded.unassign graph p pBound (by simp only [markClause_assigned]; rfl)
        simpa only [← read, ForInStep.value_yield] using cleared
    · simpa only [← read, ForInStep.value_yield] using popFacts.unassign graph p pBound rfl

private theorem resolutionScan_tags {formula : Std.Sat.CNF Nat} {snapshot : State} {count roots : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank) (fuel : Nat) (s : State)
    (facts : TagFacts snapshot count roots s) (assigned : s.assigned = fuel) (bound : fuel ≤ count) :
    TagFacts snapshot count roots (resolutionScan fuel s) := by
  induction fuel generalizing s with
  | zero => exact facts
  | succ fuel ih =>
    have step := resolutionBody_tags graph facts (by omega) (by omega)
    have cursor := resolutionBody_assigned s
    cases result : resolutionBody s with
    | done next => simpa only [resolutionScan, result, ForInStep.value_done] using step
    | yield next =>
      have after : TagFacts snapshot count roots next := by simpa only [result, ForInStep.value_yield] using step
      have nextCursor : next.assigned = fuel := by
        simpa only [result, ForInStep.value_yield, assigned, Nat.add_sub_cancel] using cursor
      simpa only [resolutionScan, result] using ih next after nextCursor (by omega)

/-- Actual resolution preserves legal mark tags. An original root can only
keep tag six or be cleared after it is popped; it never becomes a MARK leaf. -/
theorem resolveToUIP_tags {formula : Std.Sat.CNF Nat} {snapshot : State} {count roots : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (s : State)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (vars : s.nVars = snapshot.nVars) (arrays : ArrayBounds s)
    (tags : ValidMarkTags snapshot count s) (boundary : RootTagBoundary snapshot count roots s)
    (bound : s.assigned ≤ count) :
    ValidMarkTags snapshot count (resolveToUIP s) ∧ RootTagBoundary snapshot count roots (resolveToUIP s) := by
  have after := resolutionScan_tags graph s.assigned s ⟨storage, trail, vars, arrays, tags, boundary⟩ rfl bound
  rw [resolveToUIP_eq_scan]
  exact ⟨after.tags, after.boundary⟩

/-- Unconditional root consequences establish initial tag-six cache validity
for minimization, irrespective of the frozen MARK-leaf assumptions. -/
theorem RootTagConsequences.impliedCache {formula : Std.Sat.CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (root : RootTagConsequences formula snapshot count s) (tags : ValidMarkTags snapshot count s)
    (marked : ∀ lit, TrailMember snapshot count lit → s.mark lit = 2 → leaves lit) :
    ImpliedCache formula snapshot count rank leaves s := by
  refine ⟨tags, marked, ?_⟩
  intro lit member six a model _
  exact root lit member six a model

end MicrosatLean.Verification.Implementation.Native.Analysis
