import MicrosatLean.Verification.Implementation.Native.Propagation.WatchRetention
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchBounds

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation Std.Sat

/-- A watch invocation reached a real list end, assignment, or conflict. The
unchanged-assignment watch result used for budget exhaustion is excluded. -/
def WatchCompleted (before : State) : Progress → Prop
  | .finished _ => True
  | .running next => next.phase = .nextLiteral ∨
      (next.phase = .watch ∧ next.solver.assigned = before.assigned + 1)

@[simp] theorem watchCompleted_restore (s : State) (arena first : Array Nat)
    (progress : Progress) :
    WatchCompleted (restoreWatchArrays s arena first) progress ↔ WatchCompleted s progress := by
  cases progress <;> rfl

theorem propagateWatches_completes {formula : Std.Sat.CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database (restoreWatchArrays s arena first) original learned)
    (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate (restoreWatchArrays s arena first) (original ++ learned) heads)
    (nodup : ∀ entry ∈ original ++ learned, entry.lits.toList.Nodup)
    (arrays : ArrayBounds (restoreWatchArrays s arena first))
    (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (cursor : WatchCursor heads lit previous remaining) (budget : remaining.length < fuel) :
    WatchCompleted (restoreWatchArrays s arena first)
      (propagateWatches fuel s arena first decision oldLemmas root lit previous) := by
  induction remaining generalizing fuel arena first previous original learned heads with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have empty : currentWatchRef arena first lit previous = 0 := by
        simpa only [restoreWatchArrays, List.headD_nil] using cursor.current (certificate.links lit)
      simp only [currentWatchRef, beq_iff_eq] at empty
      simp only [propagateWatches, Id.run, pure, beq_iff_eq, empty, ite_true, WatchCompleted, true_or]
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
        obtain ⟨nextOriginal, nextLearned, nextDatabase, nextMeaning, nextCertificate, nextNodup, nextCursor⟩ :=
          replacement_branch_certificate database meaning certificate nodup arrays cursor literal falseLit found
        have nextArrays : ArrayBounds (restoreWatchArrays s
            (movedWatchArrays arena first lit ref previous pos).1 (movedWatchArrays arena first lit ref previous pos).2) :=
          arrayBounds_restoreWatchArrays arrays _ _ (movedWatchArrays_first_size _ _ _ _ _ _)
        have next := ih fuel (movedWatchArrays arena first lit ref previous pos).1
          (movedWatchArrays arena first lit ref previous pos).2 previous nextDatabase nextMeaning nextCertificate
          nextNodup nextArrays nextCursor (by simp only [List.length_cons] at budget; omega)
        rw [propagateWatches_replacement fuel s arena first decision oldLemmas root lit previous pos currentNonzero foundCurrent]
        simpa only [current, watchCompleted_restore] using next
      | none =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = none := by simpa only [current] using found
        let retained := retainWatch arena (watchClause ref) lit
        let other : Lit := retained[watchClause ref]!
        by_cases satisfied : s.mark other.negate ≠ 0
        · obtain ⟨nextOriginal, nextLearned, nextDatabase, nextMeaning, nextCertificate, nextNodup⟩ :=
            retainWatch_certificate database meaning certificate nodup lit ref cursor.member
          have nextCursor := cursor.advance nonzero
          have nextArrays : ArrayBounds (restoreWatchArrays s retained first) :=
            arrayBounds_restoreWatchArrays arrays retained first rfl
          have next := ih fuel retained first ref nextDatabase nextMeaning nextCertificate nextNodup nextArrays nextCursor
            (by simp only [List.length_cons] at budget; omega)
          have satisfiedCurrent : s.mark (Lit.negate
              ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) ≠ 0 := by
            simpa only [current] using satisfied
          rw [propagateWatches_skip fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent satisfiedCurrent]
          simpa only [current, watchCompleted_restore] using next
        · have opposite : s.mark other.negate = 0 := by simpa using satisfied
          by_cases unmarked : s.mark other = 0
          · have headCurrent : s.mark
                ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) = 0 := by
                simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by
                simpa only [current] using opposite
            rw [propagateWatches_unit fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent headCurrent oppositeCurrent]
            simp [WatchCompleted, State.assign, restoreWatchArrays]
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
              simp only [propagateWatches, Id.run, pure, beq_iff_eq, nonzeroRaw,
                ite_false, missingRaw, bne_iff_ne, ne_eq, oppositeRaw, not_true_eq_false, restoreWatchArrays_mark,
                headRaw, ite_true, Bool.false_eq_true, WatchCompleted, true_or]

/-- The actual public-step budget suffices for every valid cursor, so a watch
continuation after this call always records a new assignment. -/
theorem propagateWatches_arena_completes {formula : Std.Sat.CNF Nat} (s : State) (arena first : Array Nat)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat) (remaining : List Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database (restoreWatchArrays s arena first) original learned)
    (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate (restoreWatchArrays s arena first) (original ++ learned) heads)
    (nodup : ∀ entry ∈ original ++ learned, entry.lits.toList.Nodup)
    (arrays : ArrayBounds (restoreWatchArrays s arena first))
    (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (cursor : WatchCursor heads lit previous remaining) :
    WatchCompleted (restoreWatchArrays s arena first)
      (propagateWatches arena.size s arena first decision oldLemmas root lit previous) :=
  propagateWatches_completes s decision oldLemmas root lit remaining arena.size arena first previous
    database meaning certificate nodup arrays literal falseLit cursor (watchCursor_length_lt_arena database certificate cursor)

end MicrosatLean.Verification.Implementation.Native.Propagation
