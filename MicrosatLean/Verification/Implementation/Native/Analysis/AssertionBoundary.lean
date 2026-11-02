import MicrosatLean.Verification.Implementation.Native.Analysis.AnalyzerFacts

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation Std.Sat

theorem DecisionAnalysisEntry.minimizer_false {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    let resolved := analysisResolved s conflict
    (implied (resolved.nVars + 1) { resolved with processed := resolved.assigned }
      resolved.trail[resolved.assigned]!).2 = false := by
  let resolved := analysisResolved s conflict
  have facts := entry.historyResolved
  have storage : ReasonStorage s { resolved with processed := resolved.assigned } :=
    ⟨facts.storage.arena, facts.storage.reasons⟩
  have failed := implied_false_of_level_parent entry.graph storage entry.parents facts.tags
    facts.uip.lower facts.uip.upper facts.uip.clear facts.rootEarlier (resolved.nVars + 1)
  have read : resolved.trail[resolved.assigned]! = s.trail[resolved.assigned]! :=
    congrArg (fun words : Array Lit => words[resolved.assigned]!) facts.trail
  change (implied (resolved.nVars + 1) { resolved with processed := resolved.assigned }
    resolved.trail[resolved.assigned]!).2 = false
  rw [read]
  exact failed

/-- The actual backjump never stops inside the current level. A singleton
would have scanned its decision; a nonsingleton's highest tail is below the
current decision and the exact cursor gap contains no intervening decision. -/
theorem analyze_cursor_le_decision {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    (CDCL.analyze s conflict).1.assigned ≤ decision := by
  let resolved := analysisResolved s conflict
  let built := buildLearned resolved resolved.assigned
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  have forced : resolved.forced = s.forced := facts.forced
  have trail : resolved.trail = s.trail := facts.trail
  have lower : resolved.forced ≤ resolved.assigned := by
    rw [forced]
    exact Nat.le_trans entry.forcedBefore facts.uip.lower
  have ranked : ∀ i, i ≤ resolved.assigned → rank resolved.trail[i]! = i := by
    intro i before
    rw [trail]
    exact entry.graph.ranks i (by omega)
  have marked : resolved.mark resolved.trail[resolved.assigned]! = 2 := by rw [trail]; exact facts.uip.marked
  have zero : resolved.reason resolved.trail[decision]! = 0 := by
    rw [trail, facts.storage.reason]
    exact entry.block.decisionReason
  rw [analyze_eq_addClause, addClause_assigned]
  simp only [analysisBeforeStore, backjump_assigned]
  change built.1.processed ≤ decision
  by_cases after : decision < built.1.processed
  · by_cases single : built.2.1.size = 1
    · have impossible := buildLearned_single_no_retained_decision resolved resolved.assigned rank lower ranked
        marked entry.minimizer_false single decision (by rw [forced]; exact entry.forcedBefore) after
      exact False.elim (impossible zero)
    · have nonempty : 0 < built.2.1.size := entry.learned_shape.nonempty
      have many : 1 < built.2.1.size := by omega
      have older := buildLearned_retained_decision_le_tail resolved resolved.assigned rank lower ranked
        marked entry.minimizer_false many decision after zero
      obtain ⟨i, before, equal⟩ := entry.learned_shape.tails 1 (by decide) many
      have rankTail : rank built.2.1[1]! = i := by
        change rank (analysisLearned s conflict)[1]! = i
        rw [← equal]
        exact entry.graph.ranks i (Nat.lt_trans before entry.block.before)
      rw [rankTail] at older
      omega
  · omega

/-- The real retained prefix ends at a genuine old decision boundary. This
is the chronology fact needed to recover saved predecision watch witnesses. -/
theorem analyze_decision_boundary {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    s.forced ≤ (CDCL.analyze s conflict).1.assigned ∧
      (CDCL.analyze s conflict).1.assigned ≤ decision ∧
      s.reason s.trail[(CDCL.analyze s conflict).1.assigned]! = 0 := by
  let resolved := analysisResolved s conflict
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  have forced : resolved.forced = s.forced := facts.forced
  have trail : resolved.trail = s.trail := facts.trail
  have lower : resolved.forced ≤ resolved.assigned := by
    rw [forced]
    exact Nat.le_trans entry.forcedBefore facts.uip.lower
  have ranked : ∀ i, i ≤ resolved.assigned → rank resolved.trail[i]! = i := by
    intro i before
    rw [trail]
    exact entry.graph.ranks i (by omega)
  have cursor := buildLearned_cursor resolved resolved.assigned rank lower ranked
  have count : (CDCL.analyze s conflict).1.assigned = (buildLearned resolved resolved.assigned).1.processed := by
    rw [analyze_eq_addClause, addClause_assigned]
    simp only [analysisBeforeStore, backjump_assigned]
    rfl
  have below := analyze_cursor_le_decision entry
  refine ⟨by rw [count, ← forced]; exact cursor.1, below, ?_⟩
  rcases cursor.2.2.2.2.2 with unchanged | zero
  · have candidateLower : decision ≤ resolved.assigned := facts.uip.lower
    have equal : (CDCL.analyze s conflict).1.assigned = decision := by rw [count, unchanged] at below ⊢; omega
    rw [equal]
    exact entry.block.decisionReason
  · rw [trail, facts.storage.reason] at zero
    simpa only [count] using zero

/-- A singleton actual learned clause clears every nonroot level. Concrete
level cover excludes an unaccounted nondecision-only retained suffix. -/
theorem analyze_unit_root_prefix {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat} (cover : LevelCover s)
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision)
    (unit : (analysisLearned s conflict).size = 1) :
    (CDCL.analyze s conflict).1.assigned = (CDCL.analyze s conflict).1.forced := by
  let resolved := analysisResolved s conflict
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  have forced : resolved.forced = s.forced := facts.forced
  have trail : resolved.trail = s.trail := facts.trail
  have lower : resolved.forced ≤ resolved.assigned := by rw [forced]; exact Nat.le_trans entry.forcedBefore facts.uip.lower
  have ranked : ∀ i, i ≤ resolved.assigned → rank resolved.trail[i]! = i := by
    intro i before
    rw [trail]
    exact entry.graph.ranks i (by omega)
  have marked : resolved.mark resolved.trail[resolved.assigned]! = 2 := by rw [trail]; exact facts.uip.marked
  have boundary := analyze_decision_boundary entry
  rw [analyze_forced]
  by_cases empty : (CDCL.analyze s conflict).1.assigned = s.forced
  · exact empty
  · have nonempty : s.forced < (CDCL.analyze s conflict).1.assigned := by omega
    obtain ⟨decision, atRoot, before, zero⟩ := cover s.forced (Nat.le_refl _)
      (Nat.lt_trans nonempty (analyze_assigned_lt entry))
    have equal : decision = s.forced := by omega
    subst decision
    have retained : s.forced < (buildLearned resolved resolved.assigned).1.processed := by
      rw [analyze_eq_addClause, addClause_assigned] at nonempty
      change s.forced < (analysisBuilt s conflict).1.processed
      simpa only [analysisBeforeStore, backjump_assigned] using nonempty
    have impossible := buildLearned_single_no_retained_decision resolved resolved.assigned rank lower ranked
      marked entry.minimizer_false unit s.forced (Nat.le_of_eq forced) retained
    have sourceZero : resolved.reason resolved.trail[s.forced]! = 0 := by rw [trail, facts.storage.reason]; exact zero
    exact False.elim (impossible sourceZero)

/-- The highest learned tail lies at or above every decision that the real
backjump retains. Its original trail position is itself retained. -/
theorem analyze_highest_tail_after_decision {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision)
    (many : 1 < (analysisLearned s conflict).size) (older : Nat)
    (retained : older < (CDCL.analyze s conflict).1.assigned)
    (zero : s.reason s.trail[older]! = 0) :
    ∃ i, older ≤ i ∧ i < (CDCL.analyze s conflict).1.assigned ∧
      s.trail[i]! = (analysisLearned s conflict)[1]! := by
  let resolved := analysisResolved s conflict
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  have trail : resolved.trail = s.trail := facts.trail
  have lower : resolved.forced ≤ resolved.assigned := by
    rw [facts.forced]
    exact Nat.le_trans entry.forcedBefore facts.uip.lower
  have ranked : ∀ i, i ≤ resolved.assigned → rank resolved.trail[i]! = i := by
    intro i before
    rw [trail]
    exact entry.graph.ranks i (by omega)
  have count : (CDCL.analyze s conflict).1.assigned = (buildLearned resolved resolved.assigned).1.processed := by
    rw [analyze_eq_addClause, addClause_assigned]
    simp only [analysisBeforeStore, backjump_assigned]
    rfl
  have sourceZero : resolved.reason resolved.trail[older]! = 0 := by rw [trail, facts.storage.reason]; exact zero
  have marked : resolved.mark resolved.trail[resolved.assigned]! = 2 := by rw [trail]; exact facts.uip.marked
  have beforeTail := buildLearned_retained_decision_le_tail resolved resolved.assigned rank lower ranked marked
    entry.minimizer_false many older (by rw [← count]; exact retained) sourceZero
  have cursor := buildLearned_cursor resolved resolved.assigned rank lower ranked
  refine ⟨rank (analysisLearned s conflict)[1]!, beforeTail, ?_, ?_⟩
  · rw [count]
    exact cursor.2.2.2.1 1 (by decide) many
  · have value := (cursor.2.2.1 1 many).2.2
    change s.trail[rank (buildLearned resolved resolved.assigned).2.1[1]!]! =
      (buildLearned resolved resolved.assigned).2.1[1]!
    simpa only [trail] using value

end MicrosatLean.Verification.Implementation.Native.Analysis
