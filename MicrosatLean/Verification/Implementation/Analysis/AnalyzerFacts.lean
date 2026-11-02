import MicrosatLean.Verification.Implementation.Analysis.MarkCleanup

namespace MicrosatLean.Verification.Implementation.Analysis

open CDCL Representation Std.Sat

private theorem resolved_projection {α : Type} (project : State → α) (s : State) (conflict : Nat)
    (mark : ∀ before start, project (markClause before start) = project before)
    (resolve : ∀ before, project (resolveToUIP before) = project before)
    (start : project (analysisStart s) = project s) :
    project (analysisResolved s conflict) = project s :=
  (resolve _).trans ((mark _ _).trans start)

theorem analysisBeforeStore_trail (s : State) (conflict : Nat) :
    (analysisBeforeStore s conflict).trail = s.trail := by
  simp only [analysisBeforeStore, backjump_trail]
  exact (buildLearned_frame _ _).trail.trans (resolved_projection State.trail s conflict
    (fun before start => (resolutionFrame_markClause before start).trail)
    (fun before => (resolveToUIP_frame before).trail) rfl)

theorem analysisBeforeStore_reasons (s : State) (conflict : Nat) :
    (analysisBeforeStore s conflict).reasons = s.reasons := by
  simp only [analysisBeforeStore, backjump_reasons]
  exact (congrArg State.reasons (buildLearned_frame _ _).restore).trans
    (resolved_projection State.reasons s conflict
      (fun before start => (resolutionFrame_markClause before start).reasonStorage (ReasonStorage.refl before) |>.reasons)
      (fun before => (resolveToUIP_frame before).reasonStorage (ReasonStorage.refl before) |>.reasons) rfl)

theorem analysisBeforeStore_forced (s : State) (conflict : Nat) :
    (analysisBeforeStore s conflict).forced = s.forced := by
  simp only [analysisBeforeStore, backjump_forced]
  exact (buildLearned_frame _ _).forced.trans (resolved_projection State.forced s conflict
    (fun before start => by simpa only using congrArg State.forced (resolutionFrame_markClause before start).restore)
    (fun before => by simpa only using congrArg State.forced (resolveToUIP_frame before).restore) rfl)

theorem analysisBeforeStore_first (s : State) (conflict : Nat) :
    (analysisBeforeStore s conflict).first = s.first := by
  simp only [analysisBeforeStore, backjump_first]
  exact (congrArg State.first (buildLearned_frame _ _).restore).trans
    (resolved_projection State.first s conflict
      (fun before start => by simpa only using congrArg State.first (resolutionFrame_markClause before start).restore)
      (fun before => by simpa only using congrArg State.first (resolveToUIP_frame before).restore) rfl)

theorem analysisBeforeStore_arrayBounds {s : State} (arrays : ArrayBounds s) (conflict : Nat) :
    ArrayBounds (analysisBeforeStore s conflict) := by
  have start : ArrayBounds (analysisStart s) :=
    ⟨arrays.firstSize, arrays.marksSize, arrays.reasonsSize, arrays.phasesSize,
      arrays.trailSize, arrays.previousSize, arrays.nextSize⟩
  have marked := (resolutionFrame_markClause (analysisStart s) conflict).arrayBounds start
  have resolved := (resolveToUIP_frame (analysisMarked s conflict)).arrayBounds marked
  have built := (buildLearned_frame (analysisResolved s conflict) (analysisResolved s conflict).assigned).arrayBounds resolved
  apply backjump_arrayBounds
  exact ⟨built.firstSize, built.marksSize, built.reasonsSize, built.phasesSize,
    built.trailSize, built.previousSize, built.nextSize⟩

theorem analyze_trail (s : State) (conflict : Nat) : (CDCL.analyze s conflict).1.trail = s.trail := by
  rw [analyze_eq_addClause, addClause_trail, analysisBeforeStore_trail]

theorem analyze_reasons (s : State) (conflict : Nat) : (CDCL.analyze s conflict).1.reasons = s.reasons := by
  rw [analyze_eq_addClause, addClause_reasons, analysisBeforeStore_reasons]

theorem analyze_forced (s : State) (conflict : Nat) : (CDCL.analyze s conflict).1.forced = s.forced := by
  rw [analyze_eq_addClause, addClause_forced, analysisBeforeStore_forced]

theorem analyze_assigned_lt {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    (CDCL.analyze s conflict).1.assigned < s.assigned := by
  let resolved := analysisResolved s conflict
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  have ranked : ∀ i, i ≤ resolved.assigned → rank resolved.trail[i]! = i := by
    intro i bound
    rw [facts.trail]
    exact entry.graph.ranks i (by omega)
  have cursor := buildLearned_cursor resolved resolved.assigned rank
    (by rw [facts.forced]; exact Nat.le_trans entry.forcedBefore facts.uip.lower) ranked
  rw [analyze_eq_addClause, addClause_assigned]
  simp only [analysisBeforeStore, backjump_assigned]
  exact Nat.lt_of_le_of_lt cursor.2.1 upper

theorem analyze_learned_nodup {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    (analysisLearned s conflict).toList.Nodup := by
  let resolved := analysisResolved s conflict
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  apply buildLearned_nodup resolved resolved.assigned rank
    (by rw [facts.forced]; exact Nat.le_trans entry.forcedBefore facts.uip.lower)
  intro i bound
  rw [facts.trail]
  exact entry.graph.ranks i (by omega)

/-- Any actual output six tag is on an old root literal. Its falsity follows
from the input root consequence, without assuming anything about output
semantics or relying on satisfiability of the input CNF. -/
theorem analyze_rootTagConsequences {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    RootTagConsequences formula (CDCL.analyze s conflict).1 (CDCL.analyze s conflict).1.assigned
      (CDCL.analyze s conflict).1 := by
  intro lit member six
  obtain ⟨i, before, value⟩ := member
  have sixAt : (CDCL.analyze s conflict).1.mark (CDCL.analyze s conflict).1.trail[i]! = 6 := by
    rw [value]
    exact six
  have below := SixBefore.analyze entry i before sixAt
  rw [analyze_forced] at below
  have old : i < s.assigned := Nat.lt_trans before (analyze_assigned_lt entry)
  have oldValue : s.trail[i]! = lit := by simpa only [analyze_trail] using value
  apply entry.root lit ⟨i, old, oldValue⟩
  rw [← oldValue]
  exact entry.rootPrefix i below old

end MicrosatLean.Verification.Implementation.Analysis
