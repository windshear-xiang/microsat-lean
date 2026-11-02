import MicrosatLean.Verification.Implementation.Native.Analysis.DecisionHistory
import MicrosatLean.Verification.Implementation.Native.Analysis.Transition

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation Std.Sat

/-- The real learned birth is unit-closed at every decision retained by its
CDCL.backjump. A multiple-literal clause has two variables absent at that older
prefix. A singleton has no retained nonroot decision at all. -/
theorem buildLearned_birth_closed {formula : CNF Nat} {snapshot s : State}
    {count currentDecision : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (storage : ReasonStorage snapshot s)
    (trail : s.trail = snapshot.trail) (parents : ReasonLevelParent snapshot count currentDecision)
    (tags : ValidMarkTags snapshot count s) (uip : UIPResult snapshot count currentDecision s)
    (forcedBefore : s.forced ≤ currentDecision)
    (rootEarlier : ∀ i, i < count → s.mark snapshot.trail[i]! = 6 → i < currentDecision)
    (decision : Nat) (lower : s.forced ≤ decision)
    (retained : decision < (buildLearned s s.assigned).1.processed)
    (isDecision : s.reason s.trail[decision]! = 0) :
    PrefixUnitClosed (CDCL.backjump (buildLearned s s.assigned).1 s.assigned) decision
      (buildLearned s s.assigned).2.1 := by
  have head := buildLearned_retains_uip graph storage trail parents tags uip forcedBefore rootEarlier
  have ranked : ∀ i, i ≤ s.assigned → rank s.trail[i]! = i := by
    intro i before
    rw [trail]
    exact graph.ranks i (Nat.lt_of_le_of_lt before uip.upper)
  have resetStorage : ReasonStorage snapshot { s with processed := s.assigned } :=
    ⟨storage.arena, storage.reasons⟩
  have failed := implied_false_of_level_parent graph resetStorage parents tags uip.lower uip.upper
    uip.clear rootEarlier (s.nVars + 1)
  have marked : s.mark s.trail[s.assigned]! = 2 := by rw [trail]; exact uip.marked
  have read : s.trail[s.assigned]! = snapshot.trail[s.assigned]! :=
    congrArg (fun words : Array Lit => words[s.assigned]!) trail
  have failed' : (implied (s.nVars + 1) { s with processed := s.assigned } s.trail[s.assigned]!).2 = false := by
    rw [read]
    exact failed
  have lowerCandidate := Nat.le_trans forcedBefore uip.lower
  by_cases single : (buildLearned s s.assigned).2.1.size = 1
  · have impossible := buildLearned_single_no_retained_decision s s.assigned rank lowerCandidate
      ranked marked failed' single decision lower retained
    exact False.elim (impossible isDecision)
  · have many : 1 < (buildLearned s s.assigned).2.1.size := by omega
    have older := buildLearned_retained_decision_le_tail s s.assigned rank lowerCandidate ranked
      marked failed' many decision retained isDecision
    exact buildLearned_origin_migration graph trail s.assigned uip.upper lowerCandidate head.1 head.2
      1 (by decide) many older (fun _ _ => rfl)

/-- Actual minimization and CDCL.backjump preserve old records and insert the new
clause's concrete birth evidence. The identifier is immaterial to prefix
closure, and may already be the actual future arena identifier. -/
theorem DecisionHistory.buildLearned_birth {formula : CNF Nat} {snapshot s : State}
    {count currentDecision : Nat} {rank : Lit → Nat} {entries : List StoredClause}
    (history : DecisionHistory s entries)
    (graph : ReasonGraph formula snapshot count rank) (storage : ReasonStorage snapshot s)
    (trail : s.trail = snapshot.trail) (parents : ReasonLevelParent snapshot count currentDecision)
    (tags : ValidMarkTags snapshot count s) (uip : UIPResult snapshot count currentDecision s)
    (forcedBefore : s.forced ≤ currentDecision)
    (rootEarlier : ∀ i, i < count → s.mark snapshot.trail[i]! = 6 → i < currentDecision)
    (id : Nat) :
    DecisionHistory (CDCL.backjump (buildLearned s s.assigned).1 s.assigned)
      (entries ++ [⟨id, (buildLearned s s.assigned).2.1⟩]) := by
  let built := buildLearned s s.assigned
  have frame := buildLearned_frame s s.assigned
  have reasons : (buildLearned s s.assigned).1.reasons = s.reasons := by
    simpa only using congrArg State.reasons frame.restore
  have ranked : ∀ i, i ≤ s.assigned → rank s.trail[i]! = i := by
    intro i before
    rw [trail]
    exact graph.ranks i (Nat.lt_of_le_of_lt before uip.upper)
  have cursor := buildLearned_cursor s s.assigned rank (Nat.le_trans forcedBefore uip.lower) ranked
  have builtHistory := DecisionHistory.frame history frame.assigned frame.forced frame.trail reasons
  have jumpedHistory := DecisionHistory.backjump builtHistory s.assigned
    (by rw [frame.assigned]; exact cursor.2.1)
  apply DecisionHistory.append jumpedHistory
  intro decision lower retained zero
  have lower' : s.forced ≤ decision := by
    simpa only [backjump_forced, frame.forced] using lower
  have retained' : decision < built.1.processed := by simpa only [backjump_assigned] using retained
  have zero' : s.reason s.trail[decision]! = 0 := by
    simpa only [State.reason, backjump_reasons, backjump_trail, reasons, frame.trail] using zero
  exact buildLearned_birth_closed graph storage trail parents tags uip forcedBefore rootEarlier
    decision lower' retained' zero'

structure HistoryResolved (before resolved : State) (decision : Nat) : Prop where
  storage : ReasonStorage before resolved
  trail : resolved.trail = before.trail
  forced : resolved.forced = before.forced
  tags : ValidMarkTags before before.assigned resolved
  uip : UIPResult before before.assigned decision resolved
  rootEarlier : ∀ i, i < before.assigned → resolved.mark before.trail[i]! = 6 → i < decision

theorem DecisionAnalysisEntry.historyResolved {formula : CNF Nat} {s : State}
    {conflict decision : Nat} {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    HistoryResolved s (analysisResolved s conflict) decision := by
  let marked := markClause (analysisStart s) conflict
  let resolved := resolveToUIP marked
  have startArrays : ArrayBounds (analysisStart s) :=
    ⟨entry.arrays.firstSize, entry.arrays.marksSize, entry.arrays.reasonsSize, entry.arrays.phasesSize,
      entry.arrays.trailSize, entry.arrays.previousSize, entry.arrays.nextSize⟩
  have packed : PackedClause (analysisStart s) conflict lits := entry.packed.frame rfl rfl
  have markFrame := resolutionFrame_markClause (analysisStart s) conflict
  have storage : ReasonStorage s marked := markFrame.reasonStorage ⟨rfl, rfl⟩
  have trail : marked.trail = s.trail := markFrame.trail
  have vars : marked.nVars = s.nVars := markFrame.nVars
  have arrays : ArrayBounds marked := markFrame.arrayBounds startArrays
  have assigned : marked.assigned = s.assigned := markClause_assigned (analysisStart s) conflict
  have tags : ValidMarkTags s s.assigned marked := by
    simpa only [Nat.add_zero] using markClause_validTags (s := analysisStart s) entry.tags
      packed startArrays 0 (Nat.zero_le _)
  have witness : ∃ i, decision ≤ i ∧ i < s.assigned ∧ marked.mark s.trail[i]! = 2 := by
    obtain ⟨i, lower, before, member⟩ := entry.conflictInBlock
    refine ⟨i, lower, before, ?_⟩
    have nonroot : (analysisStart s).mark s.trail[i]! ≠ 6 := by
      intro six
      have below := entry.rootEarlier i before six
      omega
    simpa only [Nat.add_zero] using markClause_mark_member packed startArrays 0 (Nat.zero_le _)
      (by simpa using member) nonroot
  have uip := resolveToUIP_marked_uip entry.graph entry.block marked storage trail vars arrays assigned witness
  have boundary : RootTagBoundary s s.assigned 0 marked := by intro i impossible; omega
  have resolvedTags := resolveToUIP_tags entry.graph marked storage trail vars arrays tags boundary
    (Nat.le_of_eq assigned)
  have frame := resolveToUIP_frame marked
  refine ⟨frame.reasonStorage storage, frame.trail.trans trail, ?_, resolvedTags.1, uip, ?_⟩
  · have stable : resolved.forced = marked.forced := by simpa only using congrArg State.forced frame.restore
    exact stable.trans (markClause_forced (analysisStart s) conflict)
  · intro i before six
    exact entry.rootEarlier i before (markClause_sixSubset (analysisStart s) conflict _
      (resolveToUIP_no_new_six marked _ six))

/-- Full actual analysis preserves decision history while extending it with
the actual learned clause. Unit closure of the new entry is derived from its
birth; it is not an outer analysis assumption. -/
theorem DecisionHistory.analyze {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat} {entries : List StoredClause}
    (history : DecisionHistory s entries)
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    DecisionHistory (CDCL.analyze s conflict).1
      (entries ++ [⟨(CDCL.analyze s conflict).2, analysisLearned s conflict⟩]) := by
  let resolved := analysisResolved s conflict
  let built := buildLearned resolved resolved.assigned
  let birth := CDCL.backjump built.1 resolved.assigned
  let newEntry : StoredClause := ⟨(CDCL.analyze s conflict).2, analysisLearned s conflict⟩
  have facts := entry.historyResolved
  have oldHistory : DecisionHistory resolved entries := by
    apply DecisionHistory.truncate history (Nat.le_of_lt facts.uip.upper)
      (Nat.le_of_eq facts.forced.symm)
    · exact fun i _ => congrArg (fun words : Array Lit => words[i]!) facts.trail
    · intro i _
      rw [facts.trail, facts.storage.reason]
  have birthHistory : DecisionHistory birth (entries ++ [newEntry]) :=
    DecisionHistory.buildLearned_birth oldHistory entry.graph facts.storage facts.trail entry.parents facts.tags
      facts.uip (by rw [facts.forced]; exact entry.forcedBefore) facts.rootEarlier newEntry.id
  have beforeHistory : DecisionHistory (analysisBeforeStore s conflict) (entries ++ [newEntry]) := by
    apply DecisionHistory.frame birthHistory
    · simp only [analysisBeforeStore, birth, backjump_assigned]
      rfl
    · simp only [analysisBeforeStore, birth, backjump_forced]
      rfl
    · simp only [analysisBeforeStore, birth, backjump_trail]
      rfl
    · simp only [analysisBeforeStore, birth, backjump_reasons]
      rfl
  change DecisionHistory (CDCL.analyze s conflict).1 (entries ++ [newEntry])
  rw [analyze_eq_addClause]
  exact DecisionHistory.addClause beforeHistory _ _

theorem AnalysisTransitionEntry.decisionEntry {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    DecisionAnalysisEntry formula s conflict lits rank decision := by
  refine ⟨entry.semantic, entry.block, entry.parents, entry.forcedBefore, entry.rootEarlier, ?_⟩
  obtain ⟨i, lower, before, member, _⟩ := entry.currentConflict
  exact ⟨i, lower, before, member⟩

/-- Saved concrete prefixes discharge the clause-origin premise of actual
learned freshness. No origin or freshness conclusion is assumed separately. -/
theorem DecisionHistory.analyze_fresh {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat} {entries : List StoredClause}
    (history : DecisionHistory s entries)
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    ∀ old ∈ entries, ¬ SameLiterals (analysisLearned s conflict) old.lits :=
  analyze_fresh_of_origins entry (DecisionHistory.origins history decision entry.forcedBefore
    entry.block.before entry.block.decisionReason)

/-- The actual counter bound now follows from maintained prefix history,
the genuine database layout, and normalization of existing clauses. -/
theorem DecisionHistory.analyze_count_bound {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat} {original learned : List StoredClause}
    (history : DecisionHistory s (original ++ learned))
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision)
    (database : Database s original learned)
    (normalized : ∀ old ∈ original ++ learned, Logic.ClauseSpace.NoClash (viewedLiterals old.lits))
    (distinct : (learned.map fun old => canonicalKey s.nVars old.lits).Nodup) :
    (CDCL.analyze s conflict).1.nLemmas ≤ 3 ^ s.nVars :=
  analyze_learnedCount_bound entry database (DecisionHistory.origins history decision entry.forcedBefore
    entry.block.before entry.block.decisionReason) normalized distinct

/-- The actual subsequent asserting assignment also preserves history. Its
fresh head and proper reason are supplied by the checked actual transition. -/
theorem DecisionHistory.analyze_assign {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat} {entries : List StoredClause}
    (history : DecisionHistory s entries)
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) (root : Bool) :
    DecisionHistory ((CDCL.analyze s conflict).1.assign (CDCL.analyze s conflict).2 root)
      (entries ++ [⟨(CDCL.analyze s conflict).2, analysisLearned s conflict⟩]) := by
  have after := DecisionHistory.analyze history entry.decisionEntry
  have ready := entry.ready
  have fresh := freshVariable_of_unmarked_literal ready.active ready.head ready.opposite
  have first : (CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2 = (analysisLearned s conflict)[0]! := by
    simpa using ready.packed.literals 0 ready.nonempty
  have member : (CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2 ∈ analysisLearned s conflict := by
    rw [first, getElem!_pos _ 0 ready.nonempty]
    exact Array.getElem_mem ready.nonempty
  have literal := ready.packed.wellFormed _ member
  have room := assigned_lt_of_fresh ready.active ready.distinct fresh literal.1 literal.2
  apply DecisionHistory.assign after _ root (by have := ready.packed.startLower; omega)
  · rw [ready.arrays.trailSize]
    omega
  · exact (ready.arrays.variable_index literal.2).1
  · exact fresh

end MicrosatLean.Verification.Implementation.Native.Analysis
