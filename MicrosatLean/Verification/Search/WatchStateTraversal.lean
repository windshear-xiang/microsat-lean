import MicrosatLean.Verification.Search.WatchUnitState
import MicrosatLean.Verification.Propagation.WatchIdentity
import MicrosatLean.Verification.Propagation.WatchTraversal

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- Actual watch traversal preserves the complete base certificate and saved
decision prefixes on every running return that has not invoked analysis. -/
theorem propagateWatches_state {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula (restoreWatchArrays s arena first) original learned heads rank)
    (history : DecisionHistory (restoreWatchArrays s arena first) (original ++ learned))
    (rootTrail : RootWatchTrail s root) (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (cursor : WatchCursor heads lit previous remaining) (budget : remaining.length < fuel)
    {after : Machine}
    (running : propagateWatches fuel s arena first decision oldLemmas root lit previous = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) :
    ∃ nextOriginal nextLearned nextHeads nextRank,
      StateCertificate formula after.solver nextOriginal nextLearned nextHeads nextRank ∧
      DecisionHistory after.solver (nextOriginal ++ nextLearned) := by
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
          certificate.moveWatch cursor literal falseLit found
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
            certificate.retainWatch cursor.member falseLit
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
              certificate.watchUnit cursor.member falseLit root rootTrail found unmarked opposite
            exact ⟨nextOriginal, nextLearned, heads, nextRank, nextCertificate, nextHistory history⟩
          · have nonzeroRaw := currentNonzero
            simp only [currentWatchRef, beq_iff_eq] at nonzeroRaw
            have missingRaw := foundCurrent
            simp only [currentWatchRef, orientWatch, beq_iff_eq] at missingRaw
            have oppositeRaw : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by
                simpa only [current] using opposite
            have headRaw : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) ≠ 0 := by
                simpa only [current] using unmarked
            simp only [currentWatchRef, Propagation.retainWatch, orientWatch, beq_iff_eq, ne_eq] at oppositeRaw headRaw
            cases root <;>
              simp only [propagateWatches, Id.run, pure, beq_iff_eq, nonzeroRaw, ite_false, missingRaw,
                bne_iff_ne, ne_eq, oppositeRaw, not_true_eq_false, restoreWatchArrays_mark,
                headRaw, ite_true, Bool.false_eq_true] at running
            · cases running
              have learned := analyze_nLemmas (restoreWatchArrays s
                (Propagation.retainWatch arena (watchClause ref) lit) first) (watchClause ref)
              simp only [orientWatch, Propagation.retainWatch, beq_iff_eq, restoreWatchArrays] at learned
              simp only [State.assign, Id.run, pure, restoreWatchArrays] at noAnalysis
              simp only [currentWatchRef, beq_iff_eq] at current
              rw [current] at noAnalysis
              omega
            · cases running

/-- The base certificate and concrete settlement proofs share exactly the
same ghost entries and watch lists, determined by the actual returned arrays. -/
theorem propagateWatches_state_settled {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat} {count : Nat}
    (certificate : StateCertificate formula (restoreWatchArrays s arena first) original learned heads rank)
    (history : DecisionHistory (restoreWatchArrays s arena first) (original ++ learned))
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
      SettledWatchReturn after (nextOriginal ++ nextLearned) nextHeads count lit := by
  obtain ⟨nextOriginal, nextLearned, nextHeads, nextRank, nextCertificate, nextHistory⟩ :=
    propagateWatches_state s decision oldLemmas root lit remaining fuel arena first previous certificate history
      rootTrail literal falseLit cursor budget running noAnalysis
  have detachedBounds : TrailBounds s :=
    ⟨certificate.bounds.forcedProcessed, certificate.bounds.processedAssigned, certificate.bounds.assignedVars⟩
  obtain ⟨settledOriginal, settledLearned, settledHeads, settledDatabase, _, settledWatches, _, settled⟩ :=
    propagateWatches_settled s decision oldLemmas root lit remaining fuel arena first previous
      certificate.database certificate.meaning certificate.watches certificate.nodup certificate.arrays
      certificate.active detachedBounds certificate.marked literal falseLit bound prefixSettled visited cursor budget running noAnalysis
  obtain ⟨sameOriginal, sameLearned⟩ := settledDatabase.unique nextCertificate.database
  subst settledOriginal settledLearned
  have sameHeads := settledWatches.heads_unique nextCertificate.database nextCertificate.watches
  subst settledHeads
  exact ⟨nextOriginal, nextLearned, nextHeads, nextRank, nextCertificate, nextHistory, settled⟩

end MicrosatLean.Verification.Search
