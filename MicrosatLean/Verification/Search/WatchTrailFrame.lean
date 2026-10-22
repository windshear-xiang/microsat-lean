import MicrosatLean.Verification.Propagation.Effects

namespace MicrosatLean.Verification.Search

open CDCL

/-- A running list-end return without analysis changed only its detached
watch arrays. Unit returns are excluded by the actual next-literal phase. -/
theorem propagateWatches_next_frame (fuel : Nat) (s : State) (arena first : Array Nat)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat) {after : Machine}
    (running : propagateWatches fuel s arena first decision oldLemmas root lit previous = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) (phase : after.phase = .nextLiteral) :
    { after.solver with arena := s.arena, first := s.first } = s := by
  induction fuel generalizing arena first previous with
  | zero =>
    simp only [propagateWatches] at running
    cases running
    cases phase
  | succ fuel ih =>
    simp only [propagateWatches, Id.run, pure] at running
    generalize refEq : (if previous == 0 then first[lit]! else arena[watchLinkPos previous]!) = ref at running
    split at running
    · cases running
      rfl
    · generalize orientedEq : (if arena[watchClause ref]! == lit then
          arena.set! (watchClause ref) arena[watchClause ref + 1]! else arena) = oriented at running
      cases found : replacement oriented s.marks (watchClause ref) with
      | some pos =>
        simp only [found] at running
        exact ih _ _ _ running
      | none =>
        simp only [found] at running
        split at running
        · exact ih _ _ _ running
        · split at running
          · cases running
            cases phase
          · split at running
            · cases running
            · cases running
              have learned := analyze_nLemmas
                (restoreWatchArrays s (oriented.set! (watchClause ref + 1) lit) first) (watchClause ref)
              simp only [State.assign, Id.run, pure, restoreWatchArrays] at noAnalysis
              simp only [restoreWatchArrays] at learned
              omega

theorem propagateWatches_next_trail (fuel : Nat) (s : State) (arena first : Array Nat)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat) {after : Machine}
    (running : propagateWatches fuel s arena first decision oldLemmas root lit previous = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) (phase : after.phase = .nextLiteral) :
    after.solver.trail = s.trail := by
  simpa only using congrArg State.trail
    (propagateWatches_next_frame fuel s arena first decision oldLemmas root lit previous running noAnalysis phase)

end MicrosatLean.Verification.Search
