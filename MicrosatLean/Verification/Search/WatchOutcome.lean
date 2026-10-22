import MicrosatLean.Verification.Search.WatchConflictState
import MicrosatLean.Verification.Propagation.WatchConflict

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- Watch traversal returns a certified state with saved decision history or
a semantically sound UNSAT answer. The watch phase has no SAT return. -/
def WatchStateOutcome (formula : CNF Nat) : Progress → Prop
  | .running after => ∃ original learned heads rank,
      StateCertificate formula after.solver original learned heads rank ∧
      DecisionHistory after.solver (original ++ learned)
  | .finished (.unsat _) => CNF.Unsat formula
  | .finished (.sat _ _) => False

/-- Complete actual watch traversal, including analyzer/assertion and the
root UNSAT return. All clause and reason data in returned certificates are
derived from the current genuine database and concrete source branches. -/
theorem propagateWatches_outcome {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula (restoreWatchArrays s arena first) original learned heads rank)
    (history : DecisionHistory (restoreWatchArrays s arena first) (original ++ learned))
    (rootTrail : RootWatchTrail s root) (nonroot : root = false → NonrootPhase s)
    (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (cursor : WatchCursor heads lit previous remaining) (budget : remaining.length < fuel) :
    WatchStateOutcome formula (propagateWatches fuel s arena first decision oldLemmas root lit previous) := by
  induction remaining generalizing fuel arena first previous original learned heads rank with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have empty : currentWatchRef arena first lit previous = 0 := by
        simpa only [restoreWatchArrays, List.headD_nil] using cursor.current (certificate.watches.links lit)
      simp only [currentWatchRef, beq_iff_eq] at empty
      simp only [propagateWatches, Id.run, pure, beq_iff_eq, empty, ite_true, WatchStateOutcome]
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
        have next := ih fuel (movedWatchArrays arena first lit ref previous pos).1
          (movedWatchArrays arena first lit ref previous pos).2 previous nextCertificate (nextHistory history)
          nextCursor (by simp only [List.length_cons] at budget; omega)
        rw [propagateWatches_replacement fuel s arena first decision oldLemmas root lit previous pos currentNonzero foundCurrent]
        simpa only [current] using next
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
          have next := ih fuel retained first ref nextCertificate (nextHistory history) (cursor.advance nonzero)
            (by simp only [List.length_cons] at budget; omega)
          rw [propagateWatches_skip fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent satisfiedCurrent]
          simpa only [current] using next
        · have opposite : s.mark other.negate = 0 := by simpa using satisfied
          by_cases unmarked : s.mark other = 0
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) = 0 := by
                simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by
                simpa only [current] using opposite
            rw [propagateWatches_unit fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent headCurrent oppositeCurrent]
            simp only [current, WatchStateOutcome]
            obtain ⟨nextOriginal, nextLearned, nextRank, nextCertificate, nextHistory⟩ :=
              certificate.watchUnit cursor.member falseLit root rootTrail found unmarked opposite
            exact ⟨nextOriginal, nextLearned, heads, nextRank, nextCertificate, nextHistory history⟩
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) ≠ 0 := by
                simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by
                simpa only [current] using opposite
            rw [propagateWatches_conflict fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent oppositeCurrent headCurrent]
            simp only [current]
            cases root with
            | false =>
              simp only [Bool.false_eq_true, ite_false, WatchStateOutcome]
              have beforePhase := nonroot rfl
              have phase : NonrootPhase (restoreWatchArrays s arena first) :=
                ⟨beforePhase.levels, beforePhase.caches, beforePhase.nonroot⟩
              exact certificate.watchConflict history phase cursor.member falseLit found unmarked
            | true =>
              simp only [ite_true, WatchStateOutcome]
              obtain ⟨nextOriginal, nextLearned, conflict, nextCertificate, _, member, _, allFalse⟩ :=
                certificate.retainedConflict cursor.member falseLit found unmarked
              exact nextCertificate.root_conflict_unsat (rootTrail rfl) member allFalse

/-- The actual public watch step enjoys the same result guarantee; finite
proper links prove that its arena-sized traversal budget is sufficient. -/
theorem step_watch_outcome {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned))
    (rootTrail : RootWatchTrail s root) (nonroot : root = false → NonrootPhase s)
    (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (remaining : List Nat) (cursor : WatchCursor heads lit previous remaining) :
    WatchStateOutcome formula (step ⟨s, decision, .watch, oldLemmas, root, lit, previous⟩) := by
  change WatchStateOutcome formula (propagateWatches s.arena.size { s with arena := #[], first := #[] }
    s.arena s.first decision oldLemmas root lit previous)
  have detachedPhase : root = false → NonrootPhase { s with arena := #[], first := #[] } := by
    intro notRoot
    exact ⟨(nonroot notRoot).levels, (nonroot notRoot).caches, (nonroot notRoot).nonroot⟩
  exact propagateWatches_outcome { s with arena := #[], first := #[] } decision oldLemmas root lit
    remaining s.arena.size s.arena s.first previous certificate history rootTrail detachedPhase literal falseLit cursor
    (watchCursor_length_lt_arena certificate.database certificate.watches cursor)

end MicrosatLean.Verification.Search
