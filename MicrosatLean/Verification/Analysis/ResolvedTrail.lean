import MicrosatLean.Verification.Analysis.Asserting
import MicrosatLean.Verification.Propagation.Closure

namespace MicrosatLean.Verification.Analysis

open CDCL Representation Propagation Std.Sat

theorem complement_not_trailMember {formula : CNF Nat} {snapshot s : State} {count i : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (trail : s.trail = snapshot.trail) (before : i < count) :
    ¬ TrailMember snapshot count s.trail[i]!.negate := by
  rintro ⟨j, beforeJ, equal⟩
  have sameVar : snapshot.trail[j]!.var = snapshot.trail[i]!.var := by
    simpa only [negate_var, trail] using congrArg Lit.var equal
  have same := graph.distinctVariables j i beforeJ before sameVar
  subst j
  have impossible : s.trail[i]! = s.trail[i]!.negate := by simpa only [trail] using equal
  exact negate_ne _ impossible.symm

/-- Actual clause marking keeps the existing active trail false and never
writes its opposite polarities when its suffix consists of snapshot literals. -/
theorem markClause_activeTrail {formula : CNF Nat} {snapshot s : State} {count id : Nat}
    {rank : Lit → Nat} {lits : Array Lit} (graph : ReasonGraph formula snapshot count rank)
    (trail : s.trail = snapshot.trail) (limit : Nat) (bound : limit ≤ count)
    (arrays : ArrayBounds s) (active : ActiveTrail { s with assigned := limit }) (packed : PackedClause s id lits)
    (offset : Nat) (inside : offset ≤ lits.size)
    (covered : ∀ lit ∈ lits.toList.drop offset, TrailMember snapshot count lit) :
    ActiveTrail { markClause s (id + offset) with assigned := limit } := by
  have frame := resolutionFrame_markClause s (id + offset)
  intro i before
  change i < limit at before
  have old := active i before
  rw [frame.trail]
  constructor
  · simpa only [frame.nVars] using old.1
  · constructor
    · change (markClause s (id + offset)).mark s.trail[i]! ≠ 0
      rw [markClause_mark_suffix packed arrays offset inside]
      split
      · decide
      · exact old.2.1
    · change (markClause s (id + offset)).mark s.trail[i]!.negate = 0
      rw [markClause_mark_outside packed arrays offset inside]
      · exact old.2.2
      · intro member
        exact complement_not_trailMember graph trail (Nat.lt_of_lt_of_le before bound)
          (covered _ member)

theorem markClause_markedOnTrail {s : State} {id : Nat} {lits : Array Lit}
    (arrays : ArrayBounds s) (limit : Nat) (marked : MarkedOnTrail { s with assigned := limit }) (packed : PackedClause s id lits)
    (offset : Nat) (inside : offset ≤ lits.size)
    (covered : ∀ lit ∈ lits.toList.drop offset, TrailMember s limit lit) :
    MarkedOnTrail { markClause s (id + offset) with assigned := limit } := by
  intro lit nonzero
  change (markClause s (id + offset)).mark lit ≠ 0 at nonzero
  have oldOrMember : s.mark lit ≠ 0 ∨ lit ∈ lits.toList.drop offset := by
    rw [markClause_mark_suffix packed arrays offset inside] at nonzero
    split at nonzero
    · exact Or.inr (by exact ‹lit ∈ lits.toList.drop offset ∧ _›.1)
    · exact Or.inl nonzero
  have member : TrailMember s limit lit := by
    rcases oldOrMember with old | member
    · exact marked lit old
    · exact covered lit member
  simpa only [TrailMember,
    (resolutionFrame_markClause s (id + offset)).trail] using member

private structure ResolutionTrailFacts (snapshot : State) (count : Nat) (s : State) : Prop where
  storage : ReasonStorage snapshot s
  trail : s.trail = snapshot.trail
  vars : s.nVars = snapshot.nVars
  arrays : ArrayBounds s
  active : ActiveTrail s
  marked : MarkedOnTrail s
  bound : s.assigned ≤ count
  empty : s.assigned = 0 → s.mark s.trail[0]! = 0

private theorem clear_last_active {formula : CNF Nat} {snapshot s : State} {count p : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (trail : s.trail = snapshot.trail) (bound : p < count)
    (active : ActiveTrail { s with assigned := p + 1 }) :
    ActiveTrail { s.unassign s.trail[p]! with assigned := p } := by
  intro i before
  have before' : i < p := before
  have old := active i (by dsimp; omega)
  constructor
  · exact old.1
  · constructor
    · change (s.unassign s.trail[p]!).mark s.trail[i]! ≠ 0
      rw [unassign_mark_other]
      · exact old.2.1
      · intro same
        have equal := graph.distinctVariables p i bound (by omega)
          (by simpa only [trail] using congrArg Lit.var same)
        omega
    · change (s.unassign s.trail[p]!).mark s.trail[i]!.negate = 0
      rw [unassign_mark_other]
      · exact old.2.2
      · intro same
        have equal := graph.distinctVariables p i bound (by omega)
          (by simpa only [trail, negate_var] using congrArg Lit.var same)
        omega

private theorem clear_last_marked {s : State} {p : Nat} (arrays : ArrayBounds s)
    (active : ActiveTrail { s with assigned := p + 1 })
    (marked : MarkedOnTrail { s with assigned := p + 1 }) :
    MarkedOnTrail { s.unassign s.trail[p]! with assigned := p } := by
  intro lit nonzero
  have old : s.mark lit ≠ 0 := fun zero => nonzero (by
    change (s.unassign s.trail[p]!).mark lit = 0
    by_cases same : s.trail[p]! = lit
    · subst lit
      exact unassign_mark_same (arrays.literal_index (active p (by dsimp; omega)).1).1
    · simpa only [unassign_mark_other same] using zero)
  obtain ⟨i, before, equal⟩ := marked lit old
  have notLast : i ≠ p := by
    intro same
    subst i
    apply nonzero
    change (s.unassign s.trail[p]!).mark lit = 0
    rw [← equal]
    exact unassign_mark_same (arrays.literal_index (active p (by dsimp; omega)).1).1
  exact ⟨i, by change i < p; change i < p + 1 at before; omega, equal⟩

private def TrailStep (snapshot : State) (count : Nat) (before : State) : ForInStep State → Prop
  | .done next => ActiveTrail { next with assigned := next.assigned + 1 } ∧
      MarkedOnTrail { next with assigned := next.assigned + 1 }
  | .yield next => ResolutionTrailFacts snapshot count next ∧ next.assigned + 1 = before.assigned

private theorem resolutionBody_trail {formula : CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (facts : ResolutionTrailFacts snapshot count s) (positive : 0 < s.assigned) :
    TrailStep snapshot count s (resolutionBody s) := by
  let p := s.assigned - 1
  let popped := { s with assigned := p }
  have popArrays : ArrayBounds popped :=
    ⟨facts.arrays.firstSize, facts.arrays.marksSize, facts.arrays.reasonsSize, facts.arrays.phasesSize,
      facts.arrays.trailSize, facts.arrays.previousSize, facts.arrays.nextSize⟩
  have popStorage : ReasonStorage snapshot popped := ⟨facts.storage.arena, facts.storage.reasons⟩
  have popTrail : popped.trail = snapshot.trail := facts.trail
  have popVars : popped.nVars = snapshot.nVars := facts.vars
  have before : p < count := by have := facts.bound; dsimp [p]; omega
  have inclusive : p + 1 = s.assigned := by dsimp [p]; omega
  have active : ActiveTrail { popped with assigned := p + 1 } := by simpa only [popped, inclusive] using facts.active
  have marked : MarkedOnTrail { popped with assigned := p + 1 } := by simpa only [popped, inclusive] using facts.marked
  have clear (current : State) (frame : ResolutionFrame popped current)
      (active : ActiveTrail { current with assigned := p + 1 })
      (marked : MarkedOnTrail { current with assigned := p + 1 }) (assigned : current.assigned = p) :
      TrailStep snapshot count s (.yield (current.unassign current.trail[p]!)) := by
    have currentTrail : current.trail = snapshot.trail := frame.trail.trans popTrail
    have currentArrays := frame.arrayBounds popArrays
    have literal := (active p (by dsimp; omega)).1
    have currentActive := clear_last_active graph currentTrail before active
    have currentMarked := clear_last_marked currentArrays active marked
    have sameState : current.unassign current.trail[p]! =
        { current.unassign current.trail[p]! with assigned := p } := by rw [← assigned]; rfl
    refine ⟨⟨(resolutionFrame_setMark current _ 0).reasonStorage
      (frame.reasonStorage popStorage), currentTrail, frame.nVars.trans popVars,
      (currentArrays.unassign), ?_, ?_, by simpa only [State.unassign, State.setMark, assigned] using Nat.le_of_lt before,
      ?_⟩, by simpa only [State.unassign, State.setMark, assigned] using inclusive⟩
    · exact sameState.symm ▸ currentActive
    · exact sameState.symm ▸ currentMarked
    · intro empty
      have zero : p = 0 := by simpa only [State.unassign, State.setMark, assigned] using empty
      rw [zero]
      exact unassign_mark_same (currentArrays.literal_index (by simpa only [zero] using literal)).1
  simp only [resolutionBody, Id.run, pure]
  change TrailStep snapshot count s (if popped.reason popped.trail[p]! == 0 then .done popped
    else if popped.mark popped.trail[p]! == 2 then
      if firstUIP popped p then .done popped
      else .yield ((markClause popped (popped.reason popped.trail[p]! + 1)).unassign popped.trail[p]!)
    else .yield (popped.unassign popped.trail[p]!))
  split
  · exact ⟨active, marked⟩
  · rename_i nondecision
    have nonzero : snapshot.reason popped.trail[p]! ≠ 0 := by
      rw [← popStorage.reason]
      simpa using nondecision
    split
    · split
      · exact ⟨active, marked⟩
      · have member : TrailMember snapshot count popped.trail[p]! := ⟨p, before, by rw [popTrail]⟩
        obtain ⟨lits, packed, nonempty, _, _, tails⟩ := graph.clause_of_member member nonzero
        have packedCurrent : PackedClause popped (popped.reason popped.trail[p]!) lits := by
          rw [popStorage.reason]
          exact popStorage.packed popVars packed
        have covered : ∀ lit ∈ lits.toList.drop 1, TrailMember snapshot count lit := by
          intro lit mem
          obtain ⟨j, within, equal⟩ := List.mem_drop_iff_getElem.mp mem
          have jBound : 1 + j < lits.size := by simpa only [Array.length_toList, Nat.add_comm] using within
          have equal' : lits[1 + j]! = lit := by
            simpa only [Array.getElem_toList, getElem!_pos lits (1 + j) jBound] using equal
          exact equal' ▸ (tails (1 + j) (by omega) jBound).1
        have coveredPrefix : ∀ lit ∈ lits.toList.drop 1,
            TrailMember { popped with assigned := p + 1 } (p + 1) lit := by
          intro lit mem
          obtain ⟨j, within, equal⟩ := List.mem_drop_iff_getElem.mp mem
          have jBound : 1 + j < lits.size := by simpa only [Array.length_toList, Nat.add_comm] using within
          have equal' : lits[1 + j]! = lit := by
            simpa only [Array.getElem_toList, getElem!_pos lits (1 + j) jBound] using equal
          have tail := tails (1 + j) (by omega) jBound
          obtain ⟨k, beforeK, read⟩ := tail.1
          have earlier := tail.2
          have targetRank : rank popped.trail[p]! = p := by
            rw [popTrail]
            exact graph.ranks p before
          rw [← read, graph.ranks k beforeK, targetRank] at earlier
          refine ⟨k, by omega, ?_⟩
          change popped.trail[k]! = lit
          rw [popTrail]
          exact read.trans equal'
        have markedActive := markClause_activeTrail graph popTrail (p + 1) (by omega)
          popArrays active packedCurrent 1 (by omega) covered
        have markedMarked := markClause_markedOnTrail popArrays (p + 1) marked packedCurrent 1 (by omega) coveredPrefix
        simpa only [(resolutionFrame_markClause popped _).trail] using
          clear _ (resolutionFrame_markClause popped _) markedActive markedMarked (markClause_assigned _ _)
    · exact clear popped (.refl _) active marked rfl

private theorem resolutionScan_trail {formula : CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank) (fuel : Nat) (s : State)
    (facts : ResolutionTrailFacts snapshot count s) (assigned : s.assigned = fuel)
    (marked : (resolutionScan fuel s).mark
      (resolutionScan fuel s).trail[(resolutionScan fuel s).assigned]! ≠ 0) :
    ActiveTrail { resolutionScan fuel s with assigned := (resolutionScan fuel s).assigned + 1 } ∧
      MarkedOnTrail { resolutionScan fuel s with assigned := (resolutionScan fuel s).assigned + 1 } := by
  induction fuel generalizing s with
  | zero =>
    have zero := facts.empty assigned
    exact False.elim (marked (by simpa only [resolutionScan, assigned] using zero))
  | succ fuel ih =>
    have step := resolutionBody_trail graph facts (by omega)
    cases execute : resolutionBody s with
    | done next => simpa only [resolutionScan, execute, TrailStep] using step
    | yield next =>
      have nextFacts : ResolutionTrailFacts snapshot count next ∧ next.assigned + 1 = s.assigned := by
        simpa only [execute, TrailStep] using step
      have nextMarked : (resolutionScan fuel next).mark
          (resolutionScan fuel next).trail[(resolutionScan fuel next).assigned]! ≠ 0 := by
        simpa only [resolutionScan, execute] using marked
      simpa only [resolutionScan, execute] using ih next nextFacts.1 (by omega) nextMarked

/-- The concrete MARK witness in the current decision block forces a real UIP
exit. Thus resolution retains a consistent, covered candidate-inclusive trail;
finite-loop exhaustion is excluded by that actual marked return. -/
theorem resolveToUIP_trail {formula : CNF Nat} {snapshot : State} {count decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (block : DecisionBlock snapshot decision count) (s : State)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (vars : s.nVars = snapshot.nVars) (arrays : ArrayBounds s)
    (active : ActiveTrail s) (coverage : MarkedOnTrail s) (assigned : s.assigned = count)
    (marked : ∃ i, decision ≤ i ∧ i < count ∧ s.mark snapshot.trail[i]! = 2) :
    ActiveTrail { resolveToUIP s with assigned := (resolveToUIP s).assigned + 1 } ∧
      MarkedOnTrail { resolveToUIP s with assigned := (resolveToUIP s).assigned + 1 } := by
  have uip := resolveToUIP_marked_uip graph block s storage trail vars arrays assigned marked
  have positive : 0 < count := by obtain ⟨i, _, before, _⟩ := marked; omega
  have facts : ResolutionTrailFacts snapshot count s :=
    ⟨storage, trail, vars, arrays, active, coverage, Nat.le_of_eq assigned,
      by intro zero; omega⟩
  have finalMarked : (resolveToUIP s).mark (resolveToUIP s).trail[(resolveToUIP s).assigned]! ≠ 0 := by
    rw [(resolveToUIP_frame s).trail, trail, uip.marked]
    decide
  rw [resolveToUIP_eq_scan] at finalMarked ⊢
  exact resolutionScan_trail graph s.assigned s facts rfl finalMarked

end MicrosatLean.Verification.Analysis
