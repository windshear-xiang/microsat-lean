import MicrosatLean.Verification.Implementation.Native.Search.ControlRank
import MicrosatLean.Verification.Implementation.Native.Search.Assignment
import MicrosatLean.Verification.Implementation.Native.Propagation.Effects
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchCompletion

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- At a real watch boundary, the arena budget excludes an unchanged-trail
watch continuation. Preservation of the base certificate supplies the finite
learned bound, and the actual effect classification then decreases the rank.
The global proof must still establish that certificate preservation. -/
theorem step_watch_rank {formula : CNF Nat} {before after : Machine}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (phase : before.phase = .watch) (running : step before = .running after)
    (certificate : StateCertificate formula before.solver original learned heads rank)
    (afterCertificate : HasStateCertificate formula after.solver)
    (variables : Nat) (variablesEq : before.solver.nVars = variables)
    (literal : LiteralBound before.solver.nVars before.currentLit)
    (falseLit : before.solver.mark before.currentLit ≠ 0)
    (remaining : List Nat) (cursor : WatchCursor heads before.currentLit before.previousWatch remaining) :
    ControlRankLT (controlRank (3 ^ variables) variables after)
      (controlRank (3 ^ variables) variables before) := by
  rcases before with ⟨s, decision, phase, old, root, lit, previous⟩
  simp only at phase variablesEq certificate literal falseLit cursor
  subst phase
  let detached := { s with arena := #[], first := #[] }
  have restored : restoreWatchArrays detached s.arena s.first = s := rfl
  have actual : propagateWatches s.arena.size detached s.arena s.first
      decision old root lit previous = .running after := by
    simpa only [step, Id.run, pure, detached] using running
  have completed := propagateWatches_arena_completes detached s.arena s.first
    decision old root lit previous remaining (restored.symm ▸ certificate.database)
    certificate.meaning (restored.symm ▸ certificate.watches) certificate.nodup
    (restored.symm ▸ certificate.arrays) literal falseLit cursor
  have effect := propagateWatches_effects s.arena.size detached s.arena s.first
    decision old root lit previous
  rw [actual] at completed effect
  change after.phase = .nextLiteral ∨
    (after.phase = .watch ∧ after.solver.assigned = s.assigned + 1) at completed
  obtain ⟨nextOriginal, nextLearned, nextHeads, nextRank, afterCertificate⟩ := afterCertificate
  have afterVars : after.solver.nVars = variables := effect.variables.trans variablesEq
  have countBound : after.solver.nLemmas ≤ 3 ^ variables := by
    simpa only [afterVars] using afterCertificate.learnedCount_bound
  have assignedBound : after.solver.assigned ≤ variables := by
    simpa only [afterVars] using afterCertificate.bounds.assignedVars
  have oldLemma : after.oldLemmas = old := effect.oldLemmas
  have limit : after.solver.maxLemmas = s.maxLemmas := effect.limit
  cases effect.change with
  | scan count assigned processed phase =>
    have next : after.phase = .nextLiteral := by
      rcases completed with next | ⟨_, growth⟩
      · exact next
      · change after.solver.assigned = s.assigned at assigned
        omega
    change after.solver.nLemmas = s.nLemmas at count
    change after.solver.assigned = s.assigned at assigned
    change after.solver.processed = s.processed at processed
    simp only [controlRank, learningCredit, next, oldLemma, count, limit, assigned,
      processed, clauseProgress, phaseRank]
    exact .right _ (.right _ (.right _ (Nat.lt_succ_self 1)))
  | assign count assigned processed phase =>
    change after.solver.nLemmas = s.nLemmas at count
    change after.solver.assigned = s.assigned + 1 at assigned
    change after.solver.processed = s.processed at processed
    have processedBound := certificate.bounds.processedAssigned
    have debt : 2 * variables - after.solver.assigned - after.solver.processed <
        2 * variables - s.assigned - s.processed := by omega
    simp only [controlRank, learningCredit, phase, oldLemma, count, limit,
      clauseProgress, phaseRank]
    exact .right _ (.right _ (.left _ _ debt))
  | learn count phase =>
    have progress : clauseProgress (3 ^ variables) after.solver < clauseProgress (3 ^ variables) s := by
      apply clauseProgress_lt_of_learn limit _ countBound
      change after.solver.nLemmas = s.nLemmas + 1 at count
      omega
    exact .left _ _ progress

end MicrosatLean.Verification.Implementation.Native.Search
