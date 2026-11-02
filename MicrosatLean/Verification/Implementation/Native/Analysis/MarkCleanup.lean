import MicrosatLean.Verification.Implementation.Native.Analysis.LevelHistory

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation Std.Sat

/-- Restricting the actual reason DAG to the target's inclusive prefix shows
that recursive minimization cannot retag any later trail literal. -/
theorem implied_mark_later {formula : CNF Nat} {snapshot s : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (storage : ReasonStorage snapshot s)
    (fuel target query : Nat) (targetBefore : target < query) (queryBound : query < count) :
    (implied fuel s snapshot.trail[target]!).1.mark snapshot.trail[query]! = s.mark snapshot.trail[query]! := by
  have short := graph.prefix (keep := target + 1) (by omega)
  have support := implied_markSupport short fuel s snapshot.trail[target]! storage
    ⟨target, by omega, rfl⟩
  apply support.outside
  rintro ⟨i, before, equal⟩
  have same := graph.distinctVariables i query (by omega) queryBound (congrArg Lit.var equal)
  omega

theorem finishBody_mark (p : Nat) (lit : Lit) (s : State) (lits : Array Lit)
    (lbd : Nat) (used : Bool) (query : Lit) :
    (finishBody p lit s lits lbd used).value.1.mark query = (s.setMark lit 1).mark query := by
  simp only [finishBody, Id.run, pure]
  split <;> repeat first | split | rfl

private structure CleanupContext (snapshot : State) (count : Nat) where
  source : State
  candidate : Nat
  bound : candidate < count
  lower : source.forced ≤ candidate
  storage : ReasonStorage snapshot source
  trail : source.trail = snapshot.trail
  indices : ∀ i, i ≤ candidate → snapshot.trail[i]! < source.marks.size

private structure CleanInv {snapshot : State} {count : Nat}
    (c : CleanupContext snapshot count) (offset : Nat) (acc : LearnedAcc) : Prop where
  frame : LearnedFrame c.source acc.1
  clean : ∀ i, c.source.forced ≤ i → i ≤ c.candidate → c.candidate < i + offset →
    acc.1.mark snapshot.trail[i]! = 1

private theorem finish_clean {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (c : CleanupContext snapshot count)
    (offset : Nat) (within : offset ≤ c.candidate) (s : State) (frame : LearnedFrame c.source s)
    (clean : ∀ i, c.source.forced ≤ i → i ≤ c.candidate → c.candidate < i + offset →
      s.mark snapshot.trail[i]! = 1)
    (lits : Array Lit) (lbd : Nat) (used : Bool) :
    ∀ i, c.source.forced ≤ i → i ≤ c.candidate → c.candidate < i + (offset + 1) →
      (finishBody (c.candidate - offset) snapshot.trail[c.candidate - offset]! s lits lbd used).value.1.mark
        snapshot.trail[i]! = 1 := by
  intro i lower upper visited
  rw [finishBody_mark]
  by_cases current : i = c.candidate - offset
  · subst i
    apply setMark_mark_same
    rw [frame.marksSize]
    exact c.indices _ (Nat.sub_le _ _)
  · rw [setMark_mark_other (by
      intro equal
      have same := graph.distinctVariables (c.candidate - offset) i
        (by have := c.bound; omega) (by have := c.bound; omega) (congrArg Lit.var equal)
      exact current same.symm)]
    exact clean i lower upper (by omega)

private theorem clean_step {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (c : CleanupContext snapshot count)
    (offset : Nat) (acc : LearnedAcc) (inv : CleanInv c offset acc)
    (bound : offset < c.candidate + 1 - c.source.forced) :
    CleanInv c (offset + 1) (learnedBody c.candidate offset acc).value := by
  have within : offset ≤ c.candidate := by omega
  refine ⟨inv.frame.trans (learnedBody_frame c.candidate offset acc), ?_⟩
  have read : acc.1.trail[c.candidate - offset]! = snapshot.trail[c.candidate - offset]! :=
    congrArg (fun words : Array Lit => words[c.candidate - offset]!) (inv.frame.trail.trans c.trail)
  rw [learnedBody_eq]
  dsimp only
  rw [read]
  split
  · let result := implied (acc.1.nVars + 1) acc.1 snapshot.trail[c.candidate - offset]!
    have frame : LearnedFrame c.source result.1 := inv.frame.trans
      (.ofMarkFrame (implied_markFrame _ _ _))
    have clean : ∀ i, c.source.forced ≤ i → i ≤ c.candidate → c.candidate < i + offset →
        result.1.mark snapshot.trail[i]! = 1 := by
      intro i lower upper visited
      have storage : ReasonStorage snapshot acc.1 :=
        ⟨(congrArg State.arena inv.frame.restore).trans c.storage.arena,
          (congrArg State.reasons inv.frame.restore).trans c.storage.reasons⟩
      have same := implied_mark_later graph storage (acc.1.nVars + 1) (c.candidate - offset) i
        (by omega) (by have := c.bound; omega)
      exact same.trans (inv.clean i lower upper visited)
    split <;> exact finish_clean graph c offset within result.1 frame clean _ _ _
  · exact finish_clean graph c offset within acc.1 inv.frame inv.clean _ _ _

private theorem clean_loop {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (c : CleanupContext snapshot count)
    (fuel start : Nat) (acc : LearnedAcc) (bound : start + fuel ≤ c.candidate + 1 - c.source.forced)
    (inv : CleanInv c start acc) :
    CleanInv c (start + fuel) (forIn (m := Id) (List.range' start fuel) acc (learnedBody c.candidate)) := by
  induction fuel generalizing start acc with
  | zero => simpa only [List.range'_zero, List.forIn_nil, pure, Nat.add_zero] using inv
  | succ fuel ih =>
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨next, execute⟩ := learnedBody_yields c.candidate start acc
    have step := clean_step graph c start acc inv (by omega)
    rw [execute]
    simp only [bind]
    have after : CleanInv c (start + 1) next := by simpa only [execute, ForInStep.value_yield] using step
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (start + 1) next (by omega) after

/-- Every actually scanned nonroot slot is written back to tag one. Later
recursive calls cannot undo this because all reason edges point earlier. -/
theorem buildLearned_mark_one {formula : CNF Nat} {snapshot s : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (storage : ReasonStorage snapshot s)
    (trail : s.trail = snapshot.trail) (candidate : Nat) (candidateBound : candidate < count)
    (lower : s.forced ≤ candidate) (indices : ∀ i, i ≤ candidate → snapshot.trail[i]! < s.marks.size) :
    ∀ i, s.forced ≤ i → i ≤ candidate → (buildLearned s candidate).1.mark snapshot.trail[i]! = 1 := by
  let c : CleanupContext snapshot count := ⟨s, candidate, candidateBound, lower, storage, trail, indices⟩
  let initial : LearnedAcc := ({ s with processed := candidate }, #[], 0, false)
  have start : CleanInv c 0 initial := by
    refine ⟨⟨rfl, rfl⟩, ?_⟩
    intro i _ upper visited
    dsimp only [c] at upper visited
    omega
  have final := clean_loop graph c (candidate + 1 - s.forced) 0 initial (by dsimp only [c]; omega) start
  intro i above before
  have clean := final.clean i above before (by dsimp only [c]; omega)
  rw [buildLearned_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact clean

/-- Although recursive minimization creates cached six tags transiently, the
real analyzer returns with tag one at every retained nonroot trail position. -/
theorem analyze_mark_one {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    ∀ i, (CDCL.analyze s conflict).1.forced ≤ i → i < (CDCL.analyze s conflict).1.assigned →
      (CDCL.analyze s conflict).1.mark (CDCL.analyze s conflict).1.trail[i]! = 1 := by
  let resolved := analysisResolved s conflict
  let built := buildLearned resolved resolved.assigned
  let averaged : State := { built.1 with
    fast := built.1.fast - (built.1.fast >>> 5) + (built.2.2 <<< 15)
    slow := built.1.slow - (built.1.slow >>> 15) + (built.2.2 <<< 5) }
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  have frame := buildLearned_frame resolved resolved.assigned
  have markedSize := (resolutionFrame_markClause (analysisStart s) conflict).marksSize
  have resolvedSize : resolved.marks.size = s.marks.size :=
    (resolveToUIP_frame (analysisMarked s conflict)).marksSize.trans markedSize
  have lower : resolved.forced ≤ resolved.assigned := by
    rw [facts.forced]
    exact Nat.le_trans entry.forcedBefore facts.uip.lower
  have clean := buildLearned_mark_one entry.graph facts.storage facts.trail resolved.assigned upper lower
    (by
      intro i bound
      rw [resolvedSize]
      exact (entry.arrays.literal_index (entry.active i (by omega)).1).1)
  have ranked : ∀ i, i ≤ resolved.assigned → rank resolved.trail[i]! = i := by
    intro i bound
    rw [facts.trail]
    exact entry.graph.ranks i (by omega)
  have cursor := buildLearned_cursor resolved resolved.assigned rank lower ranked
  have cursorBound : built.1.processed ≤ resolved.assigned := cursor.2.1
  have beforeEq : analysisBeforeStore s conflict = CDCL.backjump averaged resolved.assigned := rfl
  have averageTrail : averaged.trail = s.trail := frame.trail.trans facts.trail
  have averageForced : averaged.forced = resolved.forced := frame.forced
  have averageProcessed : averaged.processed = built.1.processed := rfl
  have averageMarks : averaged.marks = built.1.marks := rfl
  have averageDistinct : DistinctTrailVariables { averaged with assigned := resolved.assigned + 1 } := by
    intro i j beforeI beforeJ equal
    apply entry.graph.distinctVariables i j (by dsimp at beforeI; omega) (by dsimp at beforeJ; omega)
    simpa only [averageTrail] using equal
  have normalized : ∀ i, (analysisBeforeStore s conflict).forced ≤ i →
      i < (analysisBeforeStore s conflict).assigned →
      (analysisBeforeStore s conflict).mark (analysisBeforeStore s conflict).trail[i]! = 1 := by
    intro i above before
    have above' : resolved.forced ≤ i := by
      simpa only [beforeEq, backjump_forced, averageForced] using above
    have before' : i < built.1.processed := by
      simpa only [beforeEq, backjump_assigned, averageProcessed] using before
    have preserved := backjump_mark_prefix (s := averaged) (candidate := resolved.assigned)
      (by rw [averageProcessed]; omega) averageDistinct i before'
    have retained : (analysisBeforeStore s conflict).mark (analysisBeforeStore s conflict).trail[i]! =
        built.1.mark s.trail[i]! := by
      simpa only [beforeEq, backjump_trail, averageTrail, State.mark, averageMarks] using preserved
    rw [retained]
    exact clean i above' (by omega)
  intro i above before
  rw [analyze_eq_addClause] at above before ⊢
  simpa only [State.mark, addClause_marks, addClause_trail] using
    normalized i (by simpa only [addClause_forced] using above)
      (by simpa only [addClause_assigned] using before)

/-- Stable nonroot phases have no recursive-minimization cache above the
root prefix. Root propagation is allowed to establish new root assignments
before advancing its boundary. -/
def SixBefore (s : State) : Prop :=
  ∀ i, i < s.assigned → s.mark s.trail[i]! = 6 → i < s.forced

theorem SixBefore.analyze {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) : SixBefore (CDCL.analyze s conflict).1 := by
  intro i before six
  by_cases earlier : i < (CDCL.analyze s conflict).1.forced
  · exact earlier
  · have one := analyze_mark_one entry i (by omega) before
    omega

theorem SixBefore.assign_false {s : State} (sixBefore : SixBefore s) (id : Nat)
    (space : s.assigned < s.trail.size) (markBound : Lit.negate (s.db id) < s.marks.size) :
    SixBefore (s.assign id false) := by
  intro i before six
  have limit : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [assign_trail_last space] at six
    have one : (s.assign id false).mark (Lit.negate (s.db id)) = 1 := setMark_mark_same markBound
    omega
  · have old : i < s.assigned := by omega
    rw [assign_trail_prefix old] at six
    apply sixBefore i old
    exact setMark_sixSubset s (Lit.negate (s.db id)) 1 (by decide) _ six

theorem SixBefore.decide {s : State} (sixBefore : SixBefore s) (var : Nat)
    (space : s.assigned < s.trail.size) (markBound : (decisionLiteral s var).negate < s.marks.size) :
    SixBefore (s.decide var) := by
  intro i before six
  have limit : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [decide_trail_last space] at six
    have one : (s.decide var).mark (decisionLiteral s var).negate = 1 := setMark_mark_same markBound
    omega
  · have old : i < s.assigned := by omega
    rw [decide_trail_prefix old] at six
    apply sixBefore i old
    exact setMark_sixSubset s (decisionLiteral s var).negate 1 (by decide) _ six

/-- A nonsingleton actual learned clause retains a nonroot tail, and hence
the real backjump cursor is strictly above the root boundary. -/
theorem analyze_nonroot_prefix {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision)
    (many : 1 < (analysisLearned s conflict).size) :
    (CDCL.analyze s conflict).1.forced < (CDCL.analyze s conflict).1.assigned := by
  let resolved := analysisResolved s conflict
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  have frame := buildLearned_frame resolved resolved.assigned
  have ranked : ∀ i, i ≤ resolved.assigned → rank resolved.trail[i]! = i := by
    intro i bound
    rw [facts.trail]
    exact entry.graph.ranks i (by omega)
  have cursor := buildLearned_cursor resolved resolved.assigned rank
    (by rw [facts.forced]; exact Nat.le_trans entry.forcedBefore facts.uip.lower) ranked
  have tailLower := (cursor.2.2.1 1 many).1
  have tailBefore := cursor.2.2.2.1 1 (by decide) many
  rw [analyze_eq_addClause, addClause_forced, addClause_assigned]
  simp only [analysisBeforeStore, backjump_forced, backjump_assigned]
  change (buildLearned resolved resolved.assigned).1.forced < (buildLearned resolved resolved.assigned).1.processed
  rw [frame.forced]
  exact Nat.lt_of_le_of_lt tailLower tailBefore

end MicrosatLean.Verification.Implementation.Native.Analysis
