import MicrosatLean.Verification.Search.WatchRichConflict
import MicrosatLean.Verification.Search.DecisionCursor
import MicrosatLean.Verification.Propagation.WatchPhase

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- The complete finite source traversal preserves every concrete fact needed
by the public machine invariant, including the analyzer and root UNSAT branch. -/
theorem propagateWatches_rich {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat} {count : Nat}
    (facts : WatchScanFacts formula (restoreWatchArrays s arena first) original learned heads rank count lit previous remaining)
    (mode : PropagationMode s root) (processed : s.processed = count + 1) (value : s.trail[count]! = lit)
    (budget : remaining.length < fuel) :
    WatchRichOutcome formula (propagateWatches fuel s arena first decision oldLemmas root lit previous) := by
  have countBefore : count < s.assigned := by
    have assigned := facts.base.bounds.processedAssigned
    change s.processed ≤ s.assigned at assigned
    omega
  have literal : LiteralBound s.nVars lit := by
    simpa only [restoreWatchArrays, value] using (facts.base.active count countBefore).1
  have falseLit : s.mark lit ≠ 0 := by
    simpa only [restoreWatchArrays, State.mark, value] using (facts.base.active count countBefore).2.1
  induction remaining generalizing fuel arena first previous original learned heads rank with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have empty : currentWatchRef arena first lit previous = 0 := by
        simpa only [restoreWatchArrays, List.headD_nil] using facts.cursor.current (facts.base.watches.links lit)
      simp only [currentWatchRef, beq_iff_eq] at empty
      simp only [propagateWatches, Id.run, pure, beq_iff_eq, empty, ite_true, WatchRichOutcome]
      refine ⟨original, learned, heads, rank, facts.base, facts.history, facts.saved, facts.units,
        mode.restoreWatchArrays arena first, Or.inl ⟨rfl, rfl, rfl, ?_⟩⟩
      have settled := facts.prefixSettled.extend facts.visited.finish value
      simpa only [restoreWatchArrays, processed] using settled
  | cons ref rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have current : currentWatchRef arena first lit previous = ref := by
        simpa only [restoreWatchArrays, List.headD_cons] using facts.cursor.current (facts.base.watches.links lit)
      have nonzero := storedWatchRef_nonzero facts.base.database (facts.base.watches.references lit ref facts.cursor.member)
      have currentNonzero : currentWatchRef arena first lit previous ≠ 0 := by simpa only [current] using nonzero
      cases found : replacement (orientWatch arena (watchClause ref) lit) s.marks (watchClause ref) with
      | some pos =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = some pos := by simpa only [current] using found
        obtain ⟨nextOriginal, nextLearned, nextFacts⟩ := facts.move literal falseLit found
        have next := ih fuel (movedWatchArrays arena first lit ref previous pos).1
          (movedWatchArrays arena first lit ref previous pos).2 previous nextFacts
          (by simp only [List.length_cons] at budget; omega)
        rw [propagateWatches_replacement fuel s arena first decision oldLemmas root lit previous pos currentNonzero foundCurrent]
        simpa only [current] using next
      | none =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = none := by simpa only [current] using found
        let retained := Propagation.retainWatch arena (watchClause ref) lit
        let other : Lit := retained[watchClause ref]!
        by_cases satisfied : s.mark other.negate ≠ 0
        · have satisfiedCurrent : s.mark (Lit.negate
              ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) ≠ 0 := by simpa only [current] using satisfied
          obtain ⟨nextOriginal, nextLearned, nextFacts⟩ := facts.skip falseLit satisfied
          have next := ih fuel retained first ref nextFacts (by simp only [List.length_cons] at budget; omega)
          rw [propagateWatches_skip fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent satisfiedCurrent]
          simpa only [current] using next
        · have opposite : s.mark other.negate = 0 := by simpa using satisfied
          by_cases unmarked : s.mark other = 0
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) = 0 := by simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by simpa only [current] using opposite
            rw [propagateWatches_unit fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent headCurrent oppositeCurrent]
            simp only [current, WatchRichOutcome]
            obtain ⟨nextOriginal, nextLearned, nextRank, nextFacts⟩ := facts.unit falseLit root mode.roots found unmarked opposite
            refine ⟨nextOriginal, nextLearned, heads, nextRank, nextFacts.base, nextFacts.history, nextFacts.saved,
              nextFacts.units, facts.base.watchUnit_mode facts.cursor.member falseLit root (mode.restoreWatchArrays arena first)
                unmarked opposite, Or.inr ⟨rfl, ?_, ?_, rest, nextFacts.cursor, nextFacts.visited, ?_⟩⟩
            · change 0 < s.processed
              omega
            · change lit = ((restoreWatchArrays s retained first).assign (watchClause ref) root).trail[s.processed - 1]!
              have index : s.processed - 1 = count := by omega
              rw [index, assign_trail_prefix (s := restoreWatchArrays s retained first) countBefore]
              exact value.symm
            · change SettledPrefix _ _ _ (s.processed - 1)
              have index : s.processed - 1 = count := by omega
              rw [index]
              exact nextFacts.prefixSettled
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) ≠ 0 := by simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by simpa only [current] using opposite
            rw [propagateWatches_conflict fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent oppositeCurrent headCurrent]
            simp only [current]
            cases root with
            | false =>
              simp only [Bool.false_eq_true, ite_false]
              exact facts.conflict (mode.restoreWatchArrays arena first) falseLit found unmarked decision oldLemmas
            | true =>
              simp only [ite_true, WatchRichOutcome]
              obtain ⟨_, _, _, nextBase, _, member, _, allFalse⟩ :=
                facts.base.retainedConflict facts.cursor.member falseLit found unmarked
              exact nextBase.root_conflict_unsat (mode.roots rfl) member allFalse

/-- The public step receives a sufficient budget from the actual proper
arena. Counter/MTF facts additionally preserve the conditional decision cursor. -/
theorem step_watch_rich {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat} {count : Nat}
    (remaining : List Nat)
    (facts : WatchScanFacts formula s original learned heads rank count lit previous remaining)
    (mode : PropagationMode s root) (processed : s.processed = count + 1) (value : s.trail[count]! = lit)
    (oldBound : oldLemmas ≤ s.nLemmas) (covered : s.nLemmas ≤ oldLemmas → DecisionCursor s decision) :
    WatchRichOutcome formula (step ⟨s, decision, .watch, oldLemmas, root, lit, previous⟩) ∧
      ∀ after, step ⟨s, decision, .watch, oldLemmas, root, lit, previous⟩ = .running after →
        after.solver.nVars = s.nVars ∧ oldLemmas ≤ after.solver.nLemmas ∧ after.oldLemmas = oldLemmas ∧
        (after.solver.nLemmas ≤ after.oldLemmas → DecisionCursor after.solver after.decision) := by
  constructor
  · change WatchRichOutcome formula (propagateWatches s.arena.size { s with arena := #[], first := #[] }
      s.arena s.first decision oldLemmas root lit previous)
    have detached : PropagationMode { s with arena := #[], first := #[] } root := mode.restoreWatchArrays #[] #[]
    exact propagateWatches_rich { s with arena := #[], first := #[] } decision oldLemmas root lit
      remaining s.arena.size s.arena s.first previous facts detached processed value
      (watchCursor_length_lt_arena facts.base.database facts.base.watches facts.cursor)
  · intro after running
    have run := running
    change propagateWatches s.arena.size { s with arena := #[], first := #[] } s.arena s.first
      decision oldLemmas root lit previous = .running after at run
    have effect := propagateWatches_effects s.arena.size { s with arena := #[], first := #[] }
      s.arena s.first decision oldLemmas root lit previous
    rw [run] at effect
    have count := propagateWatches_running_count run
    have lower : oldLemmas ≤ after.solver.nLemmas := by
      change after.solver.nLemmas = s.nLemmas ∨ after.solver.nLemmas = s.nLemmas + 1 at count
      omega
    refine ⟨effect.variables, lower, effect.oldLemmas, ?_⟩
    intro stillOld
    have noAnalysis : after.solver.nLemmas = s.nLemmas := by
      rw [effect.oldLemmas] at stillOld
      change after.solver.nLemmas = s.nLemmas ∨ after.solver.nLemmas = s.nLemmas + 1 at count
      omega
    exact step_watch_decisionCursor s decision oldLemmas root lit previous
      (covered (by rw [effect.oldLemmas, noAnalysis] at stillOld; exact stillOld)) running noAnalysis

end MicrosatLean.Verification.Search
