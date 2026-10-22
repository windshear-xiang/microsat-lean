import MicrosatLean.Verification.Search.MachineInvariant
import MicrosatLean.Verification.Search.WatchRich

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Std.Sat

private theorem watchRunning_invariant {formula : Formula} {before after : Machine}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (variables : formula.numVars ≤ before.solver.nVars)
    (facts : WatchRunningFacts (formulaView formula) after original learned heads rank)
    (sameVariables : after.solver.nVars = before.solver.nVars)
    (oldCount : after.oldLemmas ≤ after.solver.nLemmas)
    (cursor : after.solver.nLemmas ≤ after.oldLemmas → DecisionCursor after.solver after.decision) :
    MachineInvariant formula after := by
  refine ⟨original, learned, heads, rank, facts.base, ?_, facts.history, facts.saved, facts.units,
    cursor, ?_, oldCount⟩
  · rw [sameVariables]
    exact variables
  · rcases facts.phase with next | watch
    · rw [PhaseInvariant, next.1]
      exact ⟨NextMode.ofPropagationMode facts.mode, next.2.1, next.2.2.1, next.2.2.2⟩
    · rw [PhaseInvariant, watch.1]
      exact ⟨facts.mode, watch.2.1, watch.2.2.1, watch.2.2.2⟩

/-- The real finite watch traversal restores all shared facts in one ghost
package. Its conflict branch derives sound UNSAT or performs the checked
analyzer/assertion transition, including both saved histories. -/
theorem step_watch_invariant {formula : Formula} {machine : Machine}
    (invariant : MachineInvariant formula machine) (phase : machine.phase = .watch) :
    InvariantProgress formula (step machine) := by
  obtain ⟨original, learned, heads, rank, certificate⟩ := invariant
  rcases machine with ⟨s, decision, current, old, root, lit, previous⟩
  dsimp only at phase
  subst current
  have concrete := certificate.phase
  change WatchPhase s (original ++ learned) heads root lit previous at concrete
  obtain ⟨remaining, cursor, visited, prefixSettled⟩ := concrete.cursor
  have bounds : TrailBounds s := certificate.base.bounds
  have facts : WatchScanFacts (formulaView formula) s original learned heads rank
      (s.processed - 1) lit previous remaining :=
    ⟨certificate.base, certificate.history, certificate.saved, certificate.units,
      Nat.le_trans (Nat.sub_le _ _) bounds.processedAssigned, prefixSettled, visited, cursor⟩
  have processed : s.processed = s.processed - 1 + 1 := by have := concrete.positive; omega
  have outcome := step_watch_rich s decision old root lit previous remaining facts concrete.mode processed
    concrete.literal.symm certificate.oldCount certificate.cursor
  cases result : step ⟨s, decision, .watch, old, root, lit, previous⟩ with
  | running after =>
    obtain ⟨nextOriginal, nextLearned, nextHeads, nextRank, nextFacts⟩ :=
      (show WatchRichOutcome (formulaView formula) (.running after) from by rw [← result]; exact outcome.1)
    have effects := outcome.2 after result
    have oldCount : after.oldLemmas ≤ after.solver.nLemmas := by rw [effects.2.2.1]; exact effects.2.1
    have next := watchRunning_invariant (before := ⟨s, decision, .watch, old, root, lit, previous⟩)
      certificate.variables nextFacts effects.1 oldCount effects.2.2.2
    simpa only [result, InvariantProgress] using next
  | finished answer =>
    have done : WatchRichOutcome (formulaView formula) (.finished answer) := by rw [← result]; exact outcome.1
    cases answer with
    | sat model stats => exact False.elim done
    | unsat stats => simpa only [result, InvariantProgress, ValidResult, WatchRichOutcome] using done

end MicrosatLean.Verification.Search
