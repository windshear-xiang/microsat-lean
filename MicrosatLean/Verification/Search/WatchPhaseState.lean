import MicrosatLean.Verification.Search.WatchStateTraversal
import MicrosatLean.Verification.Search.WatchTrailFrame
import MicrosatLean.Verification.Propagation.WatchPhase

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- The real public watch step preserves the complete certificate, saved
history and concrete settled cursor on each non-analysis running return. -/
theorem step_watch_state_settled {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat} {count : Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned))
    (rootTrail : RootWatchTrail s root) (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (bound : count ≤ s.assigned)
    (prefixSettled : SettledPrefix s (original ++ learned) heads count)
    (remaining : List Nat) (visited : SettledCursor s (original ++ learned) heads lit remaining)
    (cursor : WatchCursor heads lit previous remaining) {after : Machine}
    (running : step ⟨s, decision, .watch, oldLemmas, root, lit, previous⟩ = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) :
    ∃ nextOriginal nextLearned nextHeads nextRank,
      StateCertificate formula after.solver nextOriginal nextLearned nextHeads nextRank ∧
      DecisionHistory after.solver (nextOriginal ++ nextLearned) ∧
      SettledWatchReturn after (nextOriginal ++ nextLearned) nextHeads count lit ∧
      (after.phase = .nextLiteral → s.trail[count]! = lit →
        SettledPrefix after.solver (nextOriginal ++ nextLearned) nextHeads (count + 1)) := by
  change propagateWatches s.arena.size { s with arena := #[], first := #[] } s.arena s.first
    decision oldLemmas root lit previous = .running after at running
  obtain ⟨nextOriginal, nextLearned, nextHeads, nextRank, nextCertificate, nextHistory, settled⟩ :=
    propagateWatches_state_settled { s with arena := #[], first := #[] } decision oldLemmas root lit
      remaining s.arena.size s.arena s.first previous certificate history rootTrail literal falseLit bound
      prefixSettled visited cursor (watchCursor_length_lt_arena certificate.database certificate.watches cursor)
      running noAnalysis
  refine ⟨nextOriginal, nextLearned, nextHeads, nextRank, nextCertificate, nextHistory, settled, ?_⟩
  intro phase value
  have frame := propagateWatches_next_trail s.arena.size { s with arena := #[], first := #[] }
    s.arena s.first decision oldLemmas root lit previous running noAnalysis phase
  apply settled.finish_prefix phase
  simpa only [frame] using value

end MicrosatLean.Verification.Search
