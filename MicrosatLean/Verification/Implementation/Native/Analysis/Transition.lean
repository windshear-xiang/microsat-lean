import MicrosatLean.Verification.Implementation.Native.Analysis.Soundness
import MicrosatLean.Verification.Implementation.Native.Analysis.ResolvedTrail

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation Propagation Std.Sat

/-- Concrete incoming reachability conditions for a non-root analysis call.
The current-block witness is an input conflict literal, not an analyzer result. -/
structure AnalysisTransitionEntry (formula : Std.Sat.CNF Nat) (s : State) (conflict : Nat)
    (conflictLits : Array Lit) (rank : Lit → Nat) (decision : Nat) : Prop where
  semantic : AnalysisEntry formula s conflict conflictLits rank
  bounds : TrailBounds s
  phases : TrailPhases s
  marked : MarkedOnTrail s
  block : DecisionBlock s decision s.assigned
  parents : ReasonLevelParent s s.assigned decision
  forcedBefore : s.forced ≤ decision
  rootEarlier : ∀ i, i < s.assigned → s.mark s.trail[i]! = 6 → i < decision
  currentConflict : ∃ i, decision ≤ i ∧ i < s.assigned ∧
    s.trail[i]! ∈ conflictLits ∧ s.mark s.trail[i]! ≠ 6

/-- All facts needed for the real asserting assignment at the actual clause
identifier returned by analysis. Neither its graph nor its marks are assumed. -/
structure AnalysisReady (formula : Std.Sat.CNF Nat) (result : State × Nat) (learned : Array Lit) : Prop where
  packed : PackedClause result.1 result.2 learned
  nonempty : 0 < learned.size
  entailed : CNF.EntailsClause formula (clauseView learned)
  graph : ∃ rank, ReasonGraph formula result.1 result.1.assigned rank
  arrays : ArrayBounds result.1
  bounds : TrailBounds result.1
  active : ActiveTrail result.1
  distinct : DistinctTrailVariables result.1
  phases : TrailPhases result.1
  marked : MarkedOnTrail result.1
  head : result.1.mark (result.1.db result.2) = 0
  opposite : result.1.mark (Lit.negate (result.1.db result.2)) = 0
  tails : ∀ j, 0 < j → j < learned.size → TrailMember result.1 result.1.assigned learned[j]!

structure AnalysisAssigned (formula : Std.Sat.CNF Nat) (s : State) : Prop where
  graph : ∃ rank, ReasonGraph formula s s.assigned rank
  arrays : ArrayBounds s
  bounds : TrailBounds s
  active : ActiveTrail s
  distinct : DistinctTrailVariables s
  phases : TrailPhases s
  marked : MarkedOnTrail s

theorem AnalysisReady.assign {formula : Std.Sat.CNF Nat} {result : State × Nat} {learned : Array Lit}
    (ready : AnalysisReady formula result learned) (root : Bool) :
    AnalysisAssigned formula (result.1.assign result.2 root) := by
  obtain ⟨rank, graph⟩ := ready.graph
  have first : result.1.db result.2 = learned[0]! := by
    simpa using ready.packed.literals 0 ready.nonempty
  have member : result.1.db result.2 ∈ learned := by
    rw [first, getElem!_pos learned 0 ready.nonempty]
    exact Array.getElem_mem ready.nonempty
  have literal := ready.packed.wellFormed _ member
  have fresh := freshVariable_of_unmarked_literal ready.active ready.head ready.opposite
  have room := assigned_lt_of_fresh ready.active ready.distinct fresh literal.1 literal.2
  have space : result.1.assigned < result.1.trail.size := by rw [ready.arrays.trailSize]; omega
  exact ⟨⟨_, graph.assign ready.arrays ready.active ready.packed ready.nonempty ready.entailed
      ready.tails ready.head ready.opposite root⟩,
    ready.arrays.assign, ready.bounds.assign room,
    ready.active.assign ready.arrays literal space fresh ready.head,
    ready.distinct.assign fresh space, ready.phases.assign ready.arrays literal space fresh,
    ready.marked.assign space⟩

private structure ResolvedFacts (original resolved : State) : Prop where
  storage : ReasonStorage original resolved
  trail : resolved.trail = original.trail
  vars : resolved.nVars = original.nVars
  arrays : ArrayBounds resolved
  active : ActiveTrail { resolved with assigned := resolved.assigned + 1 }
  marked : MarkedOnTrail { resolved with assigned := resolved.assigned + 1 }
  phases : TrailPhases { resolved with assigned := resolved.assigned + 1 }
  forced : resolved.forced = original.forced
  lower : resolved.forced ≤ resolved.assigned
  upper : resolved.assigned < original.assigned
  nonempty : 0 < (buildLearned resolved resolved.assigned).2.1.size
  head : (buildLearned resolved resolved.assigned).2.1[0]! = resolved.trail[resolved.assigned]!

private theorem AnalysisTransitionEntry.resolved {formula : Std.Sat.CNF Nat} {s : State} {conflict : Nat}
    {lits : Array Lit} {rank : Lit → Nat} {decision : Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    ResolvedFacts s (analysisResolved s conflict) := by
  let start := analysisStart s
  let marked := analysisMarked s conflict
  let resolved := analysisResolved s conflict
  have markedEq : marked = markClause start conflict := rfl
  have resolvedEq : resolved = resolveToUIP marked := rfl
  have startArrays : ArrayBounds start :=
    ⟨entry.semantic.arrays.firstSize, entry.semantic.arrays.marksSize,
      entry.semantic.arrays.reasonsSize, entry.semantic.arrays.phasesSize,
      entry.semantic.arrays.trailSize, entry.semantic.arrays.previousSize, entry.semantic.arrays.nextSize⟩
  have packed : PackedClause start conflict lits := entry.semantic.packed.frame rfl rfl
  have markFrame := resolutionFrame_markClause start conflict
  have markStorage : ReasonStorage s marked := markFrame.reasonStorage ⟨rfl, rfl⟩
  have markTrail : marked.trail = s.trail := markFrame.trail
  have markVars : marked.nVars = s.nVars := markFrame.nVars
  have markArrays : ArrayBounds marked := markFrame.arrayBounds startArrays
  have assigned : marked.assigned = s.assigned := markClause_assigned start conflict
  have forced : marked.forced = s.forced := markClause_forced start conflict
  have startActive : ActiveTrail { start with assigned := s.assigned } := by
    simpa only [ActiveTrail, FalseAssignment, start, analysisStart, State.mark] using entry.semantic.active
  have startMarked : MarkedOnTrail { start with assigned := s.assigned } := by
    simpa only [MarkedOnTrail, start, analysisStart, State.mark] using entry.marked
  have covered : ∀ lit ∈ lits.toList.drop 0, TrailMember s s.assigned lit := by
    intro lit member
    exact entry.semantic.covered lit (by simpa using member)
  have activeMarked := markClause_activeTrail entry.semantic.graph (s := start) rfl s.assigned
    (Nat.le_refl _) startArrays startActive packed 0 (Nat.zero_le _) covered
  have coverageMarked := markClause_markedOnTrail startArrays s.assigned startMarked packed 0
    (Nat.zero_le _) (by simpa only [TrailMember, start, analysisStart] using covered)
  have override : { marked with assigned := s.assigned } = marked := by rw [← assigned]
  have actualActive : ActiveTrail marked := override ▸ activeMarked
  have actualMarked : MarkedOnTrail marked := override ▸ coverageMarked
  have witness : ∃ i, decision ≤ i ∧ i < s.assigned ∧ marked.mark s.trail[i]! = 2 := by
    obtain ⟨i, lower, before, member, nonroot⟩ := entry.currentConflict
    refine ⟨i, lower, before, ?_⟩
    exact markClause_mark_member packed startArrays 0 (Nat.zero_le _) (by simpa using member) nonroot
  have tags : ValidMarkTags s s.assigned marked := by
    simpa only [markedEq, Nat.add_zero] using
      markClause_validTags (s := start) entry.semantic.tags packed startArrays 0 (Nat.zero_le _)
  have rootEarlier : ∀ i, i < s.assigned → marked.mark s.trail[i]! = 6 → i < decision := by
    intro i before root
    exact entry.rootEarlier i before
      ((markClause_mark_six_iff packed startArrays 0 (Nat.zero_le _) _).mp root)
  have retained := resolveToUIP_retains_uip entry.semantic.graph entry.block entry.parents
    marked markStorage markTrail markVars markArrays assigned witness tags
    (by rw [forced]; exact entry.forcedBefore) rootEarlier
  have trailFacts := resolveToUIP_trail entry.semantic.graph entry.block marked markStorage markTrail
    markVars markArrays actualActive actualMarked assigned witness
  rw [← resolvedEq] at retained trailFacts
  have frame := resolveToUIP_frame marked
  have resolvedTrail : resolved.trail = s.trail := frame.trail.trans markTrail
  have resolvedVars : resolved.nVars = s.nVars := frame.nVars.trans markVars
  have resolvedForced : resolved.forced = s.forced := by
    have same : resolved.forced = marked.forced := by
      simpa only [resolvedEq] using congrArg State.forced frame.restore
    exact same.trans forced
  have resolvedPhases : resolved.phases = s.phases := by
    have same : resolved.phases = marked.phases := by
      simpa only [resolvedEq] using congrArg State.phases frame.restore
    have old : marked.phases = s.phases := by
      simpa only [markedEq, start, analysisStart] using congrArg State.phases (markClause_frame start conflict).restore
    exact same.trans old
  refine ⟨frame.reasonStorage markStorage, resolvedTrail, resolvedVars, frame.arrayBounds markArrays,
    trailFacts.1, trailFacts.2, ?_, resolvedForced, ?_, retained.1.upper, retained.2.1, ?_⟩
  · intro i before
    have within : i < s.assigned := by change i < resolved.assigned + 1 at before; have := retained.1.upper; omega
    change resolved.phases[resolved.trail[i]!.var]! = _
    rw [resolvedPhases, resolvedTrail]
    exact entry.phases i within
  · rw [resolvedForced]
    exact Nat.le_trans entry.forcedBefore retained.1.lower
  · exact retained.2.2.trans (congrArg (fun words : Array Lit => words[resolved.assigned]!) resolvedTrail).symm

private theorem backjump_averages (s : State) (candidate fast slow : Nat) :
    backjump { s with fast := fast, slow := slow } candidate =
      { backjump s candidate with fast := fast, slow := slow } := by
  let body := fun (offset : Nat) (current : State) =>
    (pure (.yield (current.unassign current.trail[candidate - offset]!)) : Id (ForInStep State))
  have loop (xs : List Nat) (initial : State) :
      forIn (m := Id) xs { initial with fast := fast, slow := slow } body =
        { forIn (m := Id) xs initial body with fast := fast, slow := slow } := by
    induction xs generalizing initial with
    | nil => rfl
    | cons offset rest ih =>
      simp only [List.forIn_cons, body, bind, pure]
      exact ih (initial.unassign initial.trail[candidate - offset]!)
  simp only [backjump, Std.Legacy.Range.forIn_eq_forIn_range', Id.run, bind, pure]
  change { forIn (m := Id) (List.range' 0 [:candidate + 1 - s.processed].size)
      { s with fast := fast, slow := slow } body with
      assigned := (forIn (m := Id) (List.range' 0 [:candidate + 1 - s.processed].size)
        { s with fast := fast, slow := slow } body).processed } = _
  rw [loop]
  rfl

/-- The actual analyzer establishes the full precondition for its subsequent
asserting assignment. UIP retention, cursor geometry, marks and the old reason
graph are derived from the concrete incoming conflict/decision invariants. -/
theorem AnalysisTransitionEntry.ready {formula : Std.Sat.CNF Nat} {s : State} {conflict : Nat}
    {lits : Array Lit} {rank : Lit → Nat} {decision : Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    AnalysisReady formula (analyze s conflict) (analysisLearned s conflict) := by
  let resolved := analysisResolved s conflict
  let candidate := resolved.assigned
  let built := buildLearned resolved candidate
  let bare := backjump built.1 candidate
  let before := analysisBeforeStore s conflict
  have facts := entry.resolved
  change ResolvedFacts s resolved at facts
  have frame : LearnedFrame resolved built.1 := buildLearned_frame resolved candidate
  have ranked : ∀ i, i ≤ candidate → rank resolved.trail[i]! = i := by
    intro i before
    rw [facts.trail]
    exact entry.semantic.graph.ranks i (by have := facts.upper; change i ≤ resolved.assigned at before; omega)
  have cursor := buildLearned_cursor resolved candidate rank facts.lower ranked
  have cursorLower : resolved.forced ≤ built.1.processed := cursor.1
  have cursorUpper : built.1.processed ≤ candidate := cursor.2.1
  have assertion := buildLearned_backjump_asserting entry.semantic.graph facts.storage facts.trail
    candidate facts.upper facts.lower facts.arrays facts.active facts.head
  have builtArrays : ArrayBounds built.1 := frame.arrayBounds facts.arrays
  have builtActive := buildLearned_activeTrail entry.semantic.graph facts.storage facts.trail
    candidate facts.upper facts.active
  have builtDistinct : DistinctTrailVariables { built.1 with assigned := candidate + 1 } := by
    intro i j beforeI beforeJ same
    apply entry.semantic.graph.distinctVariables i j
      (by change i < candidate + 1 at beforeI; have := facts.upper; dsimp [candidate] at *; omega)
      (by change j < candidate + 1 at beforeJ; have := facts.upper; dsimp [candidate] at *; omega)
    simpa only [frame.trail, facts.trail] using same
  have builtPhases : TrailPhases { built.1 with assigned := candidate + 1 } := by
    have phases : built.1.phases = resolved.phases := by simpa only using congrArg State.phases frame.restore
    simpa only [TrailPhases, frame.trail, phases] using facts.phases
  have prefixBound : candidate + 1 ≤ s.assigned := by have := facts.upper; dsimp [candidate]; omega
  have support := buildLearned_markSupport (entry.semantic.graph.prefix prefixBound)
    facts.storage facts.trail candidate (by omega)
  have builtMarked : MarkedOnTrail { built.1 with assigned := candidate + 1 } := by
    intro lit nonzero
    have member : TrailMember s (candidate + 1) lit := by
      by_cases member : TrailMember s (candidate + 1) lit
      · exact member
      · change built.1.mark lit ≠ 0 at nonzero
        have outside : built.1.mark lit = resolved.mark lit := support.1 lit member
        have old : resolved.mark lit ≠ 0 := by rwa [← outside]
        obtain ⟨i, within, equal⟩ := facts.marked lit old
        exact False.elim (member ⟨i, within, by simpa only [facts.trail] using equal⟩)
    obtain ⟨i, within, equal⟩ := member
    exact ⟨i, within, by simpa only [frame.trail, facts.trail] using equal⟩
  have bareArrays : ArrayBounds bare := backjump_arrayBounds builtArrays
  have bareActive : ActiveTrail bare := backjump_activeTrail builtActive builtDistinct (by omega)
  have bareDistinct : DistinctTrailVariables bare := backjump_distinctTrailVariables builtDistinct (by omega)
  have barePhases : TrailPhases bare := backjump_trailPhases builtPhases (by omega)
  have bareMarked : MarkedOnTrail bare := by
    intro lit nonzero
    obtain ⟨i, within, equal⟩ := backjump_marked_prefix builtArrays builtActive builtMarked lit nonzero
    exact ⟨i, by simpa only [bare, backjump_assigned] using within,
      by simpa only [bare, backjump_trail] using equal⟩
  have bareBounds : TrailBounds bare := by
    apply backjump_trailBounds
    · rw [frame.forced]
      exact cursorLower
    · have variables : built.1.nVars = s.nVars := frame.nVars.trans facts.vars
      rw [variables]
      have upper := cursorUpper
      have within := facts.upper
      have total := entry.bounds.assignedVars
      dsimp [candidate] at *
      omega
  have graphBound : bare.assigned ≤ s.assigned := by
    rw [backjump_assigned]
    have upper := cursorUpper
    have within := facts.upper
    dsimp [candidate] at *
    omega
  have bareGraph : ReasonGraph formula bare bare.assigned rank := by
    apply (entry.semantic.graph.prefix graphBound).frame
    · rw [backjump_arena]
      have same : built.1.arena = resolved.arena := by simpa only using congrArg State.arena frame.restore
      exact same.trans facts.storage.arena
    · rw [backjump_reasons]
      have same : built.1.reasons = resolved.reasons := by simpa only using congrArg State.reasons frame.restore
      exact same.trans facts.storage.reasons
    · rw [backjump_trail, frame.trail]
      exact facts.trail
    · rw [backjump_nVars, frame.nVars]
      exact facts.vars
  have beforeEq : before = { bare with
      fast := built.1.fast - (built.1.fast >>> 5) + (built.2.2 <<< 15),
      slow := built.1.slow - (built.1.slow >>> 15) + (built.2.2 <<< 5) } :=
    backjump_averages built.1 candidate _ _
  have beforeArrays : ArrayBounds before := by
    rw [beforeEq]
    exact ⟨bareArrays.firstSize, bareArrays.marksSize, bareArrays.reasonsSize, bareArrays.phasesSize,
      bareArrays.trailSize, bareArrays.previousSize, bareArrays.nextSize⟩
  have beforeBounds : TrailBounds before := by
    rw [beforeEq]
    exact ⟨bareBounds.forcedProcessed, bareBounds.processedAssigned, bareBounds.assignedVars⟩
  have beforeActive : ActiveTrail before := by
    simpa only [beforeEq, ActiveTrail, FalseAssignment, State.mark] using bareActive
  have beforeDistinct : DistinctTrailVariables before := by
    simpa only [beforeEq, DistinctTrailVariables] using bareDistinct
  have beforePhases : TrailPhases before := by simpa only [beforeEq, TrailPhases] using barePhases
  have beforeMarked : MarkedOnTrail before := by simpa only [beforeEq, MarkedOnTrail, State.mark] using bareMarked
  have beforeGraph : ReasonGraph formula before before.assigned rank := by
    rw [beforeEq]
    exact bareGraph.frame rfl rfl rfl rfl
  have beforeHead : before.mark built.2.1[0]! = 0 := by simpa only [beforeEq, State.mark] using assertion.2.1
  have beforeOpposite : before.mark built.2.1[0]!.negate = 0 := by simpa only [beforeEq, State.mark] using assertion.2.2.1
  have beforeTails : ∀ j, 0 < j → j < built.2.1.size → TrailMember before before.assigned built.2.1[j]! := by
    intro j positive within
    simpa only [beforeEq, TrailMember] using (assertion.2.2.2 j positive within).1
  have reserved : 2 ≤ before.arena.size := by
    rw [analysisBeforeStore_arena]
    have lower := entry.semantic.packed.startLower
    have upper := entry.semantic.packed.endBound
    omega
  have semantic := entry.semantic.learned_sound
  change CNF.EntailsClause formula (clauseView built.2.1) ∧
    (∀ lit ∈ built.2.1, LiteralBound s.nVars lit) at semantic
  have beforeVars : before.nVars = s.nVars := analysisBeforeStore_nVars s conflict
  have bounded : ∀ lit ∈ built.2.1, LiteralBound before.nVars lit := by
    simpa only [beforeVars] using semantic.2
  have packed := addClause_packed (original := false) reserved bounded
  have head : (before.addClause built.2.1 false).1.db (before.addClause built.2.1 false).2 = built.2.1[0]! := by
    simpa using packed.literals 0 facts.nonempty
  rw [analyze_eq_addClause]
  change AnalysisReady formula (before.addClause built.2.1 false) built.2.1
  refine ⟨packed, facts.nonempty, semantic.1, ⟨rank, ?_⟩,
    beforeArrays.addClause, beforeBounds.addClause, beforeActive.addClause,
    beforeDistinct.addClause, beforePhases.addClause, ?_, ?_, ?_, ?_⟩
  · simpa only [addClause_assigned] using beforeGraph.addClause built.2.1 false
  · simpa only [MarkedOnTrail, State.mark, addClause_marks, addClause_trail, addClause_assigned] using beforeMarked
  · rw [head]
    simpa only [State.mark, addClause_marks] using beforeHead
  · rw [head]
    simpa only [State.mark, addClause_marks] using beforeOpposite
  · simpa only [TrailMember, addClause_trail, addClause_assigned] using beforeTails

/-- End-to-end composition of actual analysis and its actual learned-clause
assignment. All resulting graph and structural facts are conclusions. -/
theorem AnalysisTransitionEntry.assign {formula : Std.Sat.CNF Nat} {s : State} {conflict : Nat}
    {lits : Array Lit} {rank : Lit → Nat} {decision : Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) (root : Bool) :
    AnalysisAssigned formula ((analyze s conflict).1.assign (analyze s conflict).2 root) :=
  entry.ready.assign root

end MicrosatLean.Verification.Implementation.Native.Analysis
