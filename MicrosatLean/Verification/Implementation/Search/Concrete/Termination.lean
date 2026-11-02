import MicrosatLean.Verification.Implementation.Search.Concrete.WatchRank
import MicrosatLean.Verification.Implementation.Search.Concrete.MachineInvariant
import MicrosatLean.Verification.Implementation.Search.Concrete.ChoiceOutcome

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Std.Sat

/-- The four actual control phases share one well-founded rank. Only watch
cursor evidence and reused decision-cursor declaration are phase-specific.
The finite learned bound is a consequence of preserved base certificates. -/
theorem step_rank_of_certificates {formula : Std.Sat.CNF Nat} (variables : Nat)
    {before after : Machine} {original learned : List StoredClause}
    {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula before.solver original learned heads rank)
    (afterCertificate : HasStateCertificate formula after.solver)
    (variablesEq : before.solver.nVars = variables)
    (decision : before.phase = .choose → ¬before.solver.nLemmas > before.oldLemmas →
      before.decision = 0 ∨ (1 ≤ before.decision ∧ before.decision ≤ before.solver.nVars))
    (watch : before.phase = .watch → ∃ remaining,
      LiteralBound before.solver.nVars before.currentLit ∧ before.solver.mark before.currentLit ≠ 0 ∧
      WatchCursor heads before.currentLit before.previousWatch remaining)
    (running : step before = .running after) :
    RankLT (controlRank (3 ^ variables) variables after)
      (controlRank (3 ^ variables) variables before) := by
  cases phase : before.phase with
  | beginPropagation => exact step_beginPropagation_rank _ _ phase running
  | nextLiteral => exact step_nextLiteral_rank _ _ phase running certificate.bounds variablesEq
  | choose =>
    apply step_choose_rank (3 ^ variables) variables phase running certificate
    · simpa only [variablesEq] using certificate.learnedCount_bound
    · exact variablesEq
    · exact decision phase
  | watch =>
    obtain ⟨remaining, literal, marked, cursor⟩ := watch phase
    exact step_watch_rank phase running certificate afterCertificate variables variablesEq literal marked remaining cursor

end MicrosatLean.Verification.Implementation.Search.Concrete

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Analysis Std.Sat

/-- Every actual running transition retains the declared variable count,
including malformed states. This is a source projection, not an invariant. -/
theorem step_nVars {before after : Machine} (running : step before = .running after) :
    after.solver.nVars = before.solver.nVars := by
  rcases before with ⟨s, decision, phase, old, root, lit, previous⟩
  cases phase with
  | beginPropagation =>
    simp only [step, Id.run, pure] at running
    cases running
    rfl
  | nextLiteral =>
    simp only [step, Id.run, pure] at running
    split at running
    · cases running
      rfl
    · cases root <;> simp only [Bool.false_eq_true, ↓reduceIte] at running <;> cases running <;> rfl
  | watch =>
    change propagateWatches s.arena.size { s with arena := #[], first := #[] } s.arena s.first
      decision old root lit previous = .running after at running
    have effects := propagateWatches_effects s.arena.size { s with arena := #[], first := #[] }
      s.arena s.first decision old root lit previous
    rw [running] at effects
    exact effects.variables
  | choose =>
    rw [step_choose_eq] at running
    dsimp only at running
    split at running
    · cases running
    · cases running
      exact prepareChoice_nVars s decision old

/-- Concrete machine invariants discharge every phase-specific hypothesis
of the global lexicographic rank. This theorem assumes only the two endpoint
invariants; actual one-step preservation supplies the second endpoint. -/
theorem MachineInvariant.step_rank {formula : Formula} {before after : Machine}
    (beforeInvariant : MachineInvariant formula before) (afterInvariant : MachineInvariant formula after)
    (variables : Nat) (variablesEq : before.solver.nVars = variables)
    (running : step before = .running after) :
    RankLT (controlRank (3 ^ variables) variables after)
      (controlRank (3 ^ variables) variables before) := by
  obtain ⟨original, learned, heads, rank, certificate⟩ := beforeInvariant
  obtain ⟨nextOriginal, nextLearned, nextHeads, nextRank, next⟩ := afterInvariant
  apply step_rank_of_certificates variables certificate.base
    ⟨nextOriginal, nextLearned, nextHeads, nextRank, next.base⟩ variablesEq _ _ running
  · intro _ noLearning
    exact (certificate.cursor (by omega)).declared_or_zero
  · intro phase
    have watched : WatchPhase before.solver (original ++ learned) heads before.root
        before.currentLit before.previousWatch := by
      simpa only [PhaseInvariant, phase] using certificate.phase
    obtain ⟨remaining, cursor, _, _⟩ := watched.cursor
    have beforeTrail : before.solver.processed - 1 < before.solver.assigned := by
      have := watched.positive
      have := certificate.base.bounds.processedAssigned
      omega
    have active := certificate.base.active _ beforeTrail
    exact ⟨remaining, watched.literal.symm ▸ active.1, watched.literal.symm ▸ active.2.1, cursor⟩

end MicrosatLean.Verification.Implementation.Search.Concrete
