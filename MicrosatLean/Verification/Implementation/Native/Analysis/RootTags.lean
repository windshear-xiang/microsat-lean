import MicrosatLean.Verification.Implementation.Native.Analysis.AnalyzerFacts

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation Std.Sat

private theorem list_property {α β : Type} (xs : List α) (body : α → β → Id (ForInStep β))
    (property : β → Prop) (step : ∀ x b, property b → property (body x b).value)
    (initial : β) (valid : property initial) : property (forIn (m := Id) xs initial body) := by
  induction xs generalizing initial with
  | nil => exact valid
  | cons head tail ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    have next := step head initial valid
    cases execute : body head initial with
    | done final => simpa only [execute, ForInStep.value_done] using next
    | yield after => exact ih after (by simpa only [execute, ForInStep.value_yield] using next)

private def ScanSix (kept : Lit) (acc : ImpliedScanState) : Prop :=
  acc.2.mark kept = 6 ∧ ∀ result, acc.1 = some result → result.1.mark kept = 6

private theorem scanBody_six (recurse : State → Lit → State × Bool)
    (recursive : ∀ s target kept, s.mark kept = 6 → (recurse s target).1.mark kept = 6)
    (target kept index : Nat) (different : kept ≠ target) (acc : ImpliedScanState)
    (inv : ScanSix kept acc) : ScanSix kept (impliedScanBody recurse target index acc).value := by
  simp only [impliedScanBody]
  split
  · exact ⟨inv.1, by intro result impossible; cases impossible⟩
  · split
    · have preserved := recursive acc.2 (acc.2.db index) kept inv.1
      cases execute : recurse acc.2 (acc.2.db index) with
      | mk next follows =>
        have six : next.mark kept = 6 := by simpa only [execute] using preserved
        split
        · refine ⟨six, ?_⟩
          intro result returned
          cases returned
          simpa only [setMark_mark_other (Ne.symm different)] using six
        · exact ⟨six, by intro result impossible; cases impossible⟩
    · exact ⟨inv.1, by intro result impossible; cases impossible⟩

/-- An existing cached/root six tag is never overwritten by the actual
recursive minimizer. Calling it on that very literal takes the cached branch. -/
theorem implied_preserves_mark_six (fuel : Nat) (s : State) (target kept : Lit)
    (six : s.mark kept = 6) : (implied fuel s target).1.mark kept = 6 := by
  induction fuel generalizing s target kept with
  | zero => exact six
  | succ fuel ih =>
    by_cases same : kept = target
    · subst kept
      rw [implied_cached fuel s target (by omega)]
      exact six
    · rw [implied.eq_2]
      dsimp only [Id.run]
      split
      · exact six
      · split
        · exact six
        · simp only [bind, pure]
          unfold Break.runK.match_1
          let range : Std.Legacy.Range := [s.reason target + 1 : s.arena.size]
          let result : ImpliedScanState := forIn (m := Id) range (none, s)
            (impliedScanBody (implied fuel) target)
          have valid : ScanSix kept result := by
            change ScanSix kept (forIn (m := Id) range (none, s) (impliedScanBody (implied fuel) target))
            rw [Std.Legacy.Range.forIn_eq_forIn_range']
            exact list_property _ _ (ScanSix kept) (scanBody_six _ ih target kept · same)
              (none, s) ⟨six, by intro result impossible; cases impossible⟩
          change (Option.casesOn (motive := fun _ => State × Bool) result.1
            (result.2.setMark target 6, true) (fun r => r)).1.mark kept = 6
          cases returned : result.1 with
          | none => simpa only [setMark_mark_other (Ne.symm same)] using valid.1
          | some answer => exact valid.2 answer returned

private def RootInv (s : State) (index : Nat) (acc : LearnedAcc) : Prop :=
  LearnedFrame s acc.1 ∧ acc.1.mark s.trail[index]! = 6

private theorem root_step (s : State) (candidate index offset : Nat) (lower : s.forced ≤ candidate)
    (distinct : DistinctTrailVariables { s with assigned := candidate + 1 })
    (root : index < s.forced) (acc : LearnedAcc) (inv : RootInv s index acc)
    (bound : offset < candidate + 1 - s.forced) :
    RootInv s index (learnedBody candidate offset acc).value := by
  have within : candidate - offset ≤ candidate := Nat.sub_le _ _
  have above : s.forced ≤ candidate - offset := by omega
  have different : s.trail[candidate - offset]! ≠ s.trail[index]! := by
    intro equal
    have same := distinct (candidate - offset) index (by dsimp; omega) (by dsimp; omega)
      (congrArg Lit.var equal)
    omega
  refine ⟨inv.1.trans (learnedBody_frame candidate offset acc), ?_⟩
  have read : acc.1.trail[candidate - offset]! = s.trail[candidate - offset]! :=
    congrArg (fun words : Array Lit => words[candidate - offset]!) inv.1.trail
  rw [learnedBody_eq]
  dsimp only
  rw [read]
  split
  · have preserved := implied_preserves_mark_six (acc.1.nVars + 1) acc.1 s.trail[candidate - offset]!
      s.trail[index]! inv.2
    split <;> rw [finishBody_mark, setMark_mark_other different] <;> exact preserved
  · rw [finishBody_mark, setMark_mark_other different]
    exact inv.2

private theorem root_loop (s : State) (candidate index : Nat) (lower : s.forced ≤ candidate)
    (distinct : DistinctTrailVariables { s with assigned := candidate + 1 }) (root : index < s.forced)
    (fuel start : Nat) (acc : LearnedAcc) (bound : start + fuel ≤ candidate + 1 - s.forced)
    (inv : RootInv s index acc) :
    RootInv s index (forIn (m := Id) (List.range' start fuel) acc (learnedBody candidate)) := by
  induction fuel generalizing start acc with
  | zero => simpa only [List.range'_zero, List.forIn_nil, pure] using inv
  | succ fuel ih =>
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨next, execute⟩ := learnedBody_yields candidate start acc
    have step := root_step s candidate index start lower distinct root acc inv (by omega)
    rw [execute]
    simp only [bind]
    exact ih (start + 1) next (by omega) (by simpa only [execute, ForInStep.value_yield] using step)

theorem buildLearned_root_six (s : State) (candidate index : Nat) (lower : s.forced ≤ candidate)
    (distinct : DistinctTrailVariables { s with assigned := candidate + 1 })
    (root : index < s.forced) (six : s.mark s.trail[index]! = 6) :
    (buildLearned s candidate).1.mark s.trail[index]! = 6 := by
  let initial : LearnedAcc := ({ s with processed := candidate }, #[], 0, false)
  have valid : RootInv s index initial := ⟨⟨rfl, rfl⟩, six⟩
  have final := root_loop s candidate index lower distinct root (candidate + 1 - s.forced) 0 initial
    (by omega) valid
  rw [buildLearned_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  exact final.2

theorem DecisionAnalysisEntry.resolved_rootPrefix {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    ∀ i, i < s.forced → (analysisResolved s conflict).mark s.trail[i]! = 6 := by
  let marked := markClause (analysisStart s) conflict
  have markFrame := resolutionFrame_markClause (analysisStart s) conflict
  have arrays : ArrayBounds (analysisStart s) :=
    ⟨entry.arrays.firstSize, entry.arrays.marksSize, entry.arrays.reasonsSize, entry.arrays.phasesSize,
      entry.arrays.trailSize, entry.arrays.previousSize, entry.arrays.nextSize⟩
  have packed : PackedClause (analysisStart s) conflict lits := entry.packed.frame rfl rfl
  have tags : ValidMarkTags s s.assigned marked := by
    simpa only [Nat.add_zero] using markClause_validTags (s := analysisStart s) entry.tags packed arrays 0 (Nat.zero_le _)
  have boundary : RootTagBoundary s s.assigned s.forced marked := by
    intro i root before
    apply Or.inl
    simpa only [Nat.add_zero] using markClause_mark_root packed arrays 0 (Nat.zero_le _)
      (entry.rootPrefix i root before)
  have assigned : marked.assigned = s.assigned := markClause_assigned (analysisStart s) conflict
  have final := resolveToUIP_tags entry.graph marked (markFrame.reasonStorage ⟨rfl, rfl⟩) markFrame.trail
    markFrame.nVars (markFrame.arrayBounds arrays) tags boundary (Nat.le_of_eq assigned)
  have facts := entry.historyResolved
  intro i root
  have before : i < s.assigned := by have := entry.block.before; have := entry.forcedBefore; omega
  rcases final.2 i root before with six | ⟨popped, _⟩
  · exact six
  · have lower := facts.uip.lower
    have forced := entry.forcedBefore
    change (analysisResolved s conflict).assigned ≤ i at popped
    omega

theorem analyze_rootPrefix {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    ∀ i, i < (CDCL.analyze s conflict).1.forced →
      (CDCL.analyze s conflict).1.mark (CDCL.analyze s conflict).1.trail[i]! = 6 := by
  let resolved := analysisResolved s conflict
  let built := buildLearned resolved resolved.assigned
  let averaged : State := { built.1 with
    fast := built.1.fast - (built.1.fast >>> 5) + (built.2.2 <<< 15)
    slow := built.1.slow - (built.1.slow >>> 15) + (built.2.2 <<< 5) }
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  have trail : resolved.trail = s.trail := facts.trail
  have forced : resolved.forced = s.forced := facts.forced
  have lower : resolved.forced ≤ resolved.assigned := by
    rw [facts.forced]
    exact Nat.le_trans entry.forcedBefore facts.uip.lower
  have distinct : DistinctTrailVariables { resolved with assigned := resolved.assigned + 1 } := by
    intro i j beforeI beforeJ equal
    apply entry.graph.distinctVariables i j (by dsimp at beforeI; omega) (by dsimp at beforeJ; omega)
    simpa only [trail] using equal
  have frame := buildLearned_frame resolved resolved.assigned
  have ranked : ∀ i, i ≤ resolved.assigned → rank resolved.trail[i]! = i := by
    intro i before
    rw [facts.trail]
    exact entry.graph.ranks i (by omega)
  have cursor := buildLearned_cursor resolved resolved.assigned rank lower ranked
  have beforeEq : analysisBeforeStore s conflict = CDCL.backjump averaged resolved.assigned := rfl
  have averageTrail : averaged.trail = resolved.trail := frame.trail
  have averageMarks : averaged.marks = built.1.marks := rfl
  have averageDistinct : DistinctTrailVariables { averaged with assigned := resolved.assigned + 1 } := by
    simpa only [DistinctTrailVariables, averageTrail] using distinct
  intro i root
  have root' : i < resolved.forced := by simpa only [analyze_forced, forced] using root
  have oldSix : resolved.mark resolved.trail[i]! = 6 := by
    rw [trail]
    exact entry.resolved_rootPrefix i (by simpa only [forced] using root')
  have builtSix := buildLearned_root_six resolved resolved.assigned i lower distinct root' oldSix
  have retained : i < averaged.processed := by
    change i < built.1.processed
    have rootBound : resolved.forced ≤ built.1.processed := cursor.1
    omega
  have preserved := backjump_mark_prefix (s := averaged) (candidate := resolved.assigned)
    (by change built.1.processed ≤ resolved.assigned + 1; exact Nat.le_trans cursor.2.1 (Nat.le_succ _))
    averageDistinct i retained
  rw [analyze_eq_addClause]
  simpa only [State.mark, addClause_marks, addClause_trail, beforeEq, backjump_trail, averageTrail,
    averageMarks] using preserved.trans (by simpa only [State.mark, averageMarks, averageTrail] using builtSix)

theorem analyze_root_mark_eq {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) (i : Nat) (root : i < s.forced) :
    (CDCL.analyze s conflict).1.mark s.trail[i]! = s.mark s.trail[i]! := by
  have before : i < s.assigned := by have := entry.forcedBefore; have := entry.block.before; omega
  have after := analyze_rootPrefix entry i (by simpa only [analyze_forced] using root)
  rw [analyze_trail] at after
  exact after.trans (entry.rootPrefix i root before).symm

theorem analyze_validMarkTags {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    ValidMarkTags (CDCL.analyze s conflict).1 (CDCL.analyze s conflict).1.assigned (CDCL.analyze s conflict).1 := by
  intro lit member
  obtain ⟨i, before, value⟩ := member
  by_cases root : i < (CDCL.analyze s conflict).1.forced
  · exact Or.inr (Or.inr (Or.inr (Or.inr (by simpa only [value] using analyze_rootPrefix entry i root))))
  · exact Or.inr (Or.inl (by simpa only [value] using analyze_mark_one entry i (by omega) before))

end MicrosatLean.Verification.Implementation.Native.Analysis
