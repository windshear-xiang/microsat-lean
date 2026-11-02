import MicrosatLean.Verification.Implementation.Native.Propagation.WatchSettlementBranches
import MicrosatLean.Verification.Implementation.Native.Propagation.Effects

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation Analysis Std.Sat

/-- A normal list end settles every current watch; a unit return retains the
exact cursor and its already visited settled references. -/
def SettledWatchReturn (after : Machine) (entries : List StoredClause)
    (heads : Nat → List Nat) (count : Nat) (lit : Lit) : Prop :=
  SettledPrefix after.solver entries heads count ∧
    ((after.phase = .nextLiteral ∧
        ∀ ref ∈ heads lit, SettledWatch after.solver entries after.solver.assigned lit ref) ∨
      ∃ remaining, after.phase = .watch ∧ after.currentLit = lit ∧
        WatchCursor heads lit after.previousWatch remaining ∧
        SettledCursor after.solver entries heads lit remaining)

/-- Every actual watch return that does not learn a clause preserves the
genuine database/watch certificate and concretely advances settlement. The
learned counter excludes analysis here; its branch is handled separately. -/
theorem propagateWatches_settled {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {count : Nat}
    (database : Database (restoreWatchArrays s arena first) original learned)
    (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate (restoreWatchArrays s arena first) (original ++ learned) heads)
    (nodup : ∀ entry ∈ original ++ learned, entry.lits.toList.Nodup)
    (arrays : ArrayBounds (restoreWatchArrays s arena first))
    (active : ActiveTrail s) (bounds : TrailBounds s) (marked : MarkedOnTrail s)
    (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (bound : count ≤ s.assigned)
    (prefixSettled : SettledPrefix (restoreWatchArrays s arena first) (original ++ learned) heads count)
    (visited : SettledCursor (restoreWatchArrays s arena first) (original ++ learned) heads lit remaining)
    (cursor : WatchCursor heads lit previous remaining) (budget : remaining.length < fuel)
    {after : Machine}
    (running : propagateWatches fuel s arena first decision oldLemmas root lit previous = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) :
    ∃ nextOriginal nextLearned nextHeads,
      Database after.solver nextOriginal nextLearned ∧ DatabaseMeaning formula nextOriginal nextLearned ∧
      WatchCertificate after.solver (nextOriginal ++ nextLearned) nextHeads ∧
      (∀ entry ∈ nextOriginal ++ nextLearned, entry.lits.toList.Nodup) ∧
      SettledWatchReturn after (nextOriginal ++ nextLearned) nextHeads count lit := by
  induction remaining generalizing fuel arena first previous original learned heads with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have empty : currentWatchRef arena first lit previous = 0 := by
        simpa only [restoreWatchArrays, List.headD_nil] using cursor.current (certificate.links lit)
      simp only [currentWatchRef, beq_iff_eq] at empty
      simp only [propagateWatches, Id.run, pure, beq_iff_eq, empty, ite_true] at running
      cases running
      exact ⟨original, learned, heads, database, meaning, certificate, nodup,
        prefixSettled, Or.inl ⟨rfl, visited.finish⟩⟩
  | cons ref rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have current : currentWatchRef arena first lit previous = ref := by
        simpa only [restoreWatchArrays, List.headD_cons] using cursor.current (certificate.links lit)
      have proper := certificate.references lit ref cursor.member
      have nonzero : ref ≠ 0 := storedWatchRef_nonzero database proper
      have currentNonzero : currentWatchRef arena first lit previous ≠ 0 := by simpa only [current] using nonzero
      cases found : replacement (orientWatch arena (watchClause ref) lit) s.marks (watchClause ref) with
      | some pos =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = some pos := by simpa only [current] using found
        obtain ⟨nextOriginal, nextLearned, nextDatabase, nextMeaning, nextCertificate, nextNodup,
            nextCursor, nextPrefix, nextVisited⟩ :=
          replacement_branch_settlement database meaning certificate nodup arrays active bound cursor literal
            falseLit prefixSettled visited found
        have nextArrays := arrayBounds_restoreWatchArrays arrays
          (movedWatchArrays arena first lit ref previous pos).1 (movedWatchArrays arena first lit ref previous pos).2
          (movedWatchArrays_first_size _ _ _ _ _ _)
        rw [propagateWatches_replacement fuel s arena first decision oldLemmas root lit previous pos currentNonzero foundCurrent] at running
        simp only [current] at running
        exact ih fuel _ _ previous nextDatabase nextMeaning nextCertificate nextNodup nextArrays
          nextPrefix nextVisited nextCursor (by simp only [List.length_cons] at budget; omega) running
      | none =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = none := by simpa only [current] using found
        let retained := retainWatch arena (watchClause ref) lit
        let other : Lit := retained[watchClause ref]!
        by_cases satisfied : s.mark other.negate ≠ 0
        · have satisfiedCurrent : s.mark (Lit.negate
              ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) ≠ 0 := by
            simpa only [current] using satisfied
          obtain ⟨nextOriginal, nextLearned, nextDatabase, nextMeaning, nextCertificate, nextNodup,
              nextCursor, nextPrefix, nextVisited⟩ :=
            skip_branch_settlement database meaning certificate nodup marked cursor prefixSettled visited satisfied
          have nextArrays := arrayBounds_restoreWatchArrays arrays retained first rfl
          rw [propagateWatches_skip fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent satisfiedCurrent] at running
          simp only [current] at running
          exact ih fuel retained first ref nextDatabase nextMeaning nextCertificate nextNodup nextArrays
            nextPrefix nextVisited nextCursor (by simp only [List.length_cons] at budget; omega) running
        · have opposite : s.mark other.negate = 0 := by simpa using satisfied
          by_cases unmarked : s.mark other = 0
          · have headCurrent : s.mark
                ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) = 0 := by
                simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by
                simpa only [current] using opposite
            rw [propagateWatches_unit fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent headCurrent oppositeCurrent] at running
            simp only [current] at running
            cases running
            have space : s.assigned < s.trail.size := by
              have length := arrays.trailSize
              have assigned := bounds.assignedVars
              change s.trail.size = s.nVars + 1 at length
              omega
            obtain ⟨nextOriginal, nextLearned, nextDatabase, nextMeaning, nextCertificate, nextNodup,
                nextCursor, nextPrefix, nextVisited⟩ :=
              unit_branch_settlement database meaning certificate nodup bound cursor prefixSettled visited root space
            exact ⟨nextOriginal, nextLearned, heads, nextDatabase, nextMeaning, nextCertificate, nextNodup,
              nextPrefix, Or.inr ⟨rest, rfl, rfl, nextCursor, nextVisited⟩⟩
          · have nonzeroRaw := currentNonzero
            simp only [currentWatchRef, beq_iff_eq] at nonzeroRaw
            have missingRaw := foundCurrent
            simp only [currentWatchRef, orientWatch, beq_iff_eq] at missingRaw
            have oppositeRaw : s.mark (Lit.negate
                ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by
                simpa only [current] using opposite
            have headRaw : s.mark
                ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) ≠ 0 := by
                simpa only [current] using unmarked
            simp only [currentWatchRef, retainWatch, orientWatch, beq_iff_eq, ne_eq] at oppositeRaw headRaw
            cases root <;>
              simp only [propagateWatches, Id.run, pure, beq_iff_eq, nonzeroRaw, ite_false, missingRaw,
                bne_iff_ne, ne_eq, oppositeRaw, not_true_eq_false, restoreWatchArrays_mark,
                headRaw, ite_true, Bool.false_eq_true] at running
            · cases running
              have learned := Search.analyze_nLemmas (restoreWatchArrays s
                (retainWatch arena (watchClause ref) lit) first) (watchClause ref)
              simp only [orientWatch, retainWatch, beq_iff_eq, restoreWatchArrays] at learned
              simp only [State.assign, Id.run, pure, restoreWatchArrays] at noAnalysis
              simp only [currentWatchRef, beq_iff_eq] at current
              rw [current] at noAnalysis
              omega
            · cases running

end MicrosatLean.Verification.Implementation.Native.Propagation
