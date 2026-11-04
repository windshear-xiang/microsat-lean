import MicrosatLean.Verification.Implementation.Analysis.Soundness

namespace MicrosatLean.Verification.Implementation.Analysis

open CDCL Representation Std.Sat

private theorem resolutionBody_mtf {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank) (s : State)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (vars : s.nVars = snapshot.nVars) (arrays : ArrayBounds s) (order : MTFCoverage s)
    (positive : 0 < s.assigned) (bound : s.assigned ≤ count) :
    MTFCoverage (resolutionBody s).value := by
  let p := s.assigned - 1
  let popped := { s with assigned := p }
  let lit := s.trail[p]!
  have poppedOrder : MTFCoverage popped := order
  simp only [resolutionBody, Id.run, pure]
  change MTFCoverage
    (if popped.reason lit == 0 then ForInStep.done popped
    else if popped.mark lit == 2 then
      if firstUIP popped p then ForInStep.done popped
      else ForInStep.yield ((markClause popped (popped.reason lit + 1)).unassign lit)
    else ForInStep.yield (popped.unassign lit)).value
  split
  · exact poppedOrder
  · have nondecision : snapshot.reason snapshot.trail[p]! ≠ 0 := by
      simpa only [popped, lit, State.reason, trail, storage.reasons, beq_iff_eq] using
        ‹¬ (popped.reason lit == 0) = true›
    obtain ⟨lits, packed, nonempty, _, _, _⟩ := graph.clauses p (by dsimp only [p]; omega) nondecision
    have packedCurrent : PackedClause popped (popped.reason lit) lits := by
      have read : popped.reason lit = snapshot.reason snapshot.trail[p]! := by
        simp only [popped, lit, State.reason, trail, storage.reasons]
      rw [read]
      exact (storage.packed vars packed).frame rfl rfl
    have poppedArrays : ArrayBounds popped := (resolutionFrame_setAssigned s p).arrayBounds arrays
    split
    · split
      · exact poppedOrder
      · exact markClause_mtf packedCurrent poppedArrays poppedOrder 1 (by omega)
    · exact poppedOrder

private theorem resolutionScan_mtf {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank) (fuel : Nat) (s : State)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (vars : s.nVars = snapshot.nVars) (arrays : ArrayBounds s) (order : MTFCoverage s)
    (assigned : s.assigned = fuel) (bound : fuel ≤ count) :
    MTFCoverage (resolutionScan fuel s) := by
  induction fuel generalizing s with
  | zero => exact order
  | succ fuel ih =>
    have bodyOrder := resolutionBody_mtf graph s storage trail vars arrays order (by omega) (by omega)
    have frame := resolutionBody_frame s
    have cursor := resolutionBody_assigned s
    cases result : resolutionBody s with
    | done next => simpa only [resolutionScan, result, ForInStep.value_done] using bodyOrder
    | yield next =>
      have nextFrame : ResolutionFrame s next := by simpa only [result, ForInStep.value_yield] using frame
      have nextOrder : MTFCoverage next := by simpa only [result, ForInStep.value_yield] using bodyOrder
      have nextAssigned : next.assigned = fuel := by
        simpa only [result, ForInStep.value_yield, assigned, Nat.add_sub_cancel] using cursor
      simpa only [resolutionScan, result] using ih next (nextFrame.reasonStorage storage)
        (nextFrame.trail.trans trail) (nextFrame.nVars.trans vars) (nextFrame.arrayBounds arrays)
        nextOrder nextAssigned (by omega)

/-- Actual reason expansion preserves the concrete move-to-front permutation.
Each bumped literal is supplied by a genuine bounded packed reason clause. -/
theorem resolveToUIP_mtf {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank) (s : State)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (vars : s.nVars = snapshot.nVars) (arrays : ArrayBounds s) (order : MTFCoverage s)
    (bound : s.assigned ≤ count) : MTFCoverage (resolveToUIP s) := by
  rw [resolveToUIP_eq_scan]
  exact resolutionScan_mtf graph s.assigned s storage trail vars arrays order rfl bound

theorem LearnedFrame.mtf {before after : State} (frame : LearnedFrame before after)
    (order : MTFCoverage before) : MTFCoverage after := by
  obtain ⟨words, valid⟩ := order
  refine ⟨words, valid.frame frame.nVars ?_ ?_ ?_⟩
  · simpa only using congrArg State.head frame.restore
  · simpa only using congrArg State.previous frame.restore
  · simpa only using congrArg State.next frame.restore

/-- The complete actual analyzer preserves the decision-order permutation,
including all conflict/reason bumps before the asserting clause is allocated. -/
theorem AnalysisEntry.analyze_mtf {formula : Std.Sat.CNF Nat} {s : State} {conflict : Nat}
    {lits : Array Lit} {rank : Lit → Nat} (entry : AnalysisEntry formula s conflict lits rank)
    (order : MTFCoverage s) : MTFCoverage (analyze s conflict).1 := by
  let marked := analysisMarked s conflict
  let resolved := analysisResolved s conflict
  let built := analysisBuilt s conflict
  let averaged : State := { built.1 with
    fast := built.1.fast - (built.1.fast >>> 5) + (built.2.2 <<< 15)
    slow := built.1.slow - (built.1.slow >>> 15) + (built.2.2 <<< 5) }
  have startOrder : MTFCoverage (analysisStart s) := order
  have startArrays : ArrayBounds (analysisStart s) :=
    ⟨entry.arrays.firstSize, entry.arrays.marksSize, entry.arrays.reasonsSize, entry.arrays.phasesSize,
      entry.arrays.trailSize, entry.arrays.previousSize, entry.arrays.nextSize⟩
  have packed : PackedClause (analysisStart s) conflict lits := entry.packed.frame rfl rfl
  have markedOrder : MTFCoverage marked := markClause_mtf packed startArrays startOrder 0 (Nat.zero_le _)
  have frame := resolutionFrame_markClause (analysisStart s) conflict
  have storage : ReasonStorage s marked := frame.reasonStorage ⟨rfl, rfl⟩
  have bound : marked.assigned ≤ s.assigned := Nat.le_of_eq (markClause_assigned (analysisStart s) conflict)
  have resolvedOrder : MTFCoverage resolved := resolveToUIP_mtf entry.graph marked storage
    frame.trail frame.nVars (frame.arrayBounds startArrays) markedOrder bound
  have builtOrder : MTFCoverage built.1 := (buildLearned_frame resolved resolved.assigned).mtf resolvedOrder
  have averagedOrder : MTFCoverage averaged := builtOrder
  have beforeOrder : MTFCoverage (analysisBeforeStore s conflict) := backjump_mtfCoverage averagedOrder
  rw [analyze_eq_addClause]
  exact beforeOrder.addClause _ false

end MicrosatLean.Verification.Implementation.Analysis
