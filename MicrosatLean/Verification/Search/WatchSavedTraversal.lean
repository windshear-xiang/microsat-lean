import MicrosatLean.Verification.Search.WatchSavedState
import MicrosatLean.Verification.Search.WatchStateTraversal
import MicrosatLean.Verification.Propagation.WatchConflict

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- Actual non-analysis traversal preserves the stronger watch facts saved
below every retained predecision boundary, including through unit appends. -/
theorem propagateWatches_saved {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula (restoreWatchArrays s arena first) original learned heads rank)
    (history : DecisionWatchHistory (restoreWatchArrays s arena first) (original ++ learned) heads)
    (rootTrail : RootWatchTrail s root) (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (cursor : WatchCursor heads lit previous remaining) (budget : remaining.length < fuel)
    {after : Machine}
    (running : propagateWatches fuel s arena first decision oldLemmas root lit previous = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) :
    ∃ nextOriginal nextLearned nextHeads nextRank,
      StateCertificate formula after.solver nextOriginal nextLearned nextHeads nextRank ∧
      DecisionWatchHistory after.solver (nextOriginal ++ nextLearned) nextHeads := by
  induction remaining generalizing fuel arena first previous original learned heads rank with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have empty : currentWatchRef arena first lit previous = 0 := by
        simpa only [restoreWatchArrays, List.headD_nil] using cursor.current (certificate.watches.links lit)
      simp only [currentWatchRef, beq_iff_eq] at empty
      simp only [propagateWatches, Id.run, pure, beq_iff_eq, empty, ite_true] at running
      cases running
      exact ⟨original, learned, heads, rank, certificate, history⟩
  | cons ref rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have current : currentWatchRef arena first lit previous = ref := by
        simpa only [restoreWatchArrays, List.headD_cons] using cursor.current (certificate.watches.links lit)
      have proper := certificate.watches.references lit ref cursor.member
      have nonzero : ref ≠ 0 := storedWatchRef_nonzero certificate.database proper
      have currentNonzero : currentWatchRef arena first lit previous ≠ 0 := by simpa only [current] using nonzero
      cases found : replacement (orientWatch arena (watchClause ref) lit) s.marks (watchClause ref) with
      | some pos =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = some pos := by simpa only [current] using found
        obtain ⟨nextOriginal, nextLearned, nextCertificate, nextCursor, nextHistory⟩ :=
          certificate.moveWatch_saved cursor literal falseLit found
        rw [propagateWatches_replacement fuel s arena first decision oldLemmas root lit previous pos currentNonzero foundCurrent] at running
        simp only [current] at running
        exact ih fuel _ _ previous nextCertificate (nextHistory history) nextCursor
          (by simp only [List.length_cons] at budget; omega) running
      | none =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = none := by simpa only [current] using found
        let retained := Propagation.retainWatch arena (watchClause ref) lit
        let other : Lit := retained[watchClause ref]!
        by_cases satisfied : s.mark other.negate ≠ 0
        · have satisfiedCurrent : s.mark (Lit.negate
              ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) ≠ 0 := by
            simpa only [current] using satisfied
          obtain ⟨nextOriginal, nextLearned, nextCertificate, nextHistory⟩ :=
            certificate.retainWatch_saved cursor.member falseLit
          rw [propagateWatches_skip fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent satisfiedCurrent] at running
          simp only [current] at running
          exact ih fuel retained first ref nextCertificate (nextHistory history) (cursor.advance nonzero)
            (by simp only [List.length_cons] at budget; omega) running
        · have opposite : s.mark other.negate = 0 := by simpa using satisfied
          by_cases unmarked : s.mark other = 0
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) = 0 := by
                simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by
                simpa only [current] using opposite
            rw [propagateWatches_unit fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent headCurrent oppositeCurrent] at running
            simp only [current] at running
            cases running
            obtain ⟨nextOriginal, nextLearned, nextRank, nextCertificate, nextHistory⟩ :=
              certificate.watchUnit_saved cursor.member falseLit root rootTrail found unmarked opposite
            exact ⟨nextOriginal, nextLearned, heads, nextRank, nextCertificate, nextHistory history⟩
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) ≠ 0 := by
                simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by
                simpa only [current] using opposite
            rw [propagateWatches_conflict fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent oppositeCurrent headCurrent] at running
            simp only [current] at running
            cases root with
            | true => simp only [ite_true] at running; cases running
            | false =>
              simp only [Bool.false_eq_true, ite_false] at running
              cases running
              have learned := analyze_nLemmas (restoreWatchArrays s retained first) (watchClause ref)
              simp only [State.assign, Id.run, pure] at noAnalysis
              have actualCount : (CDCL.analyze (restoreWatchArrays s retained first) (watchClause ref)).1.nLemmas = s.nLemmas := by
                simpa only [retained, restoreWatchArrays] using noAnalysis
              have count : (restoreWatchArrays s retained first).nLemmas = s.nLemmas := rfl
              omega

/-- Shared ghost uniqueness aligns base/history, active settlement, and saved
predecision watch witnesses for the same actual non-analysis return. -/
theorem propagateWatches_state_saved {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat} {count : Nat}
    (certificate : StateCertificate formula (restoreWatchArrays s arena first) original learned heads rank)
    (history : DecisionHistory (restoreWatchArrays s arena first) (original ++ learned))
    (saved : DecisionWatchHistory (restoreWatchArrays s arena first) (original ++ learned) heads)
    (rootTrail : RootWatchTrail s root) (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (bound : count ≤ s.assigned)
    (prefixSettled : SettledPrefix (restoreWatchArrays s arena first) (original ++ learned) heads count)
    (visited : SettledCursor (restoreWatchArrays s arena first) (original ++ learned) heads lit remaining)
    (cursor : WatchCursor heads lit previous remaining) (budget : remaining.length < fuel)
    {after : Machine}
    (running : propagateWatches fuel s arena first decision oldLemmas root lit previous = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) :
    ∃ nextOriginal nextLearned nextHeads nextRank,
      StateCertificate formula after.solver nextOriginal nextLearned nextHeads nextRank ∧
      DecisionHistory after.solver (nextOriginal ++ nextLearned) ∧
      DecisionWatchHistory after.solver (nextOriginal ++ nextLearned) nextHeads ∧
      SettledWatchReturn after (nextOriginal ++ nextLearned) nextHeads count lit := by
  obtain ⟨nextOriginal, nextLearned, nextHeads, nextRank, nextCertificate, nextHistory, settled⟩ :=
    propagateWatches_state_settled s decision oldLemmas root lit remaining fuel arena first previous certificate history
      rootTrail literal falseLit bound prefixSettled visited cursor budget running noAnalysis
  obtain ⟨savedOriginal, savedLearned, savedHeads, _, savedCertificate, nextSaved⟩ :=
    propagateWatches_saved s decision oldLemmas root lit remaining fuel arena first previous certificate saved
      rootTrail literal falseLit cursor budget running noAnalysis
  obtain ⟨sameOriginal, sameLearned⟩ := savedCertificate.database.unique nextCertificate.database
  subst savedOriginal savedLearned
  have sameHeads := savedCertificate.watches.heads_unique nextCertificate.database nextCertificate.watches
  subst savedHeads
  exact ⟨nextOriginal, nextLearned, nextHeads, nextRank, nextCertificate, nextHistory, nextSaved, settled⟩

end MicrosatLean.Verification.Search
