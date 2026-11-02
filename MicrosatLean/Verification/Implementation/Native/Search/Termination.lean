import MicrosatLean.Verification.Implementation.Native.Search.MachineInvariant
import MicrosatLean.Verification.Implementation.Native.Search.StepRank
import MicrosatLean.Verification.Implementation.Native.Search.ChoiceOutcome
import MicrosatLean.Verification.Implementation.Native.Search.Execution
import MicrosatLean.Verification.Implementation.Native.Search.MachinePreservation

namespace MicrosatLean.Verification.Implementation.Native.Search

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

theorem runningReachable_nVars {initial current : Machine} (reachable : RunningReachable initial current) :
    current.solver.nVars = initial.solver.nVars := by
  induction reachable with
  | initial => rfl
  | advance _ transition ih => exact (step_nVars transition).trans ih

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

/-- The actual initialized search returns a semantically valid result after
finitely many real transitions. All preservation and strict-rank premises
are discharged for this solver; no execution budget is an input. -/
theorem initialized_search_terminates {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (initialized : initState formula config = .ok (some s)) :
    ∃ fuel result, runFor fuel { solver := s, decision := s.head } = .finished result ∧
      ValidResult formula result := by
  let initial : Machine := { solver := s, decision := s.head }
  have invariant : MachineInvariant formula initial := initState_some_machineInvariant wellFormed initialized
  have safe (machine : Machine) (valid : MachineInvariant formula machine) :
      ValidProgress (MachineInvariant formula) (ValidResult formula) (step machine) := by
    have preserved := step_preserves_invariant valid
    cases next : step machine <;> simpa only [next, InvariantProgress, ValidProgress] using preserved
  obtain ⟨fuel, result, finished⟩ := exists_runFor_finished_of_wellFounded_rank rank_wellFounded
    initial (controlRank (3 ^ s.nVars) s.nVars) (by
      intro before after reachable running
      have beforeValid := invariant_of_runningReachable (MachineInvariant formula) invariant
        (fun _ _ valid transition => step_running_invariant valid transition) reachable
      have afterValid := step_running_invariant beforeValid running
      exact MachineInvariant.step_rank beforeValid afterValid s.nVars (runningReachable_nVars reachable) running)
  refine ⟨fuel, result, finished, ?_⟩
  have valid := runFor_preserves (MachineInvariant formula) (ValidResult formula) safe fuel invariant
  simpa only [finished, ValidProgress] using valid

end MicrosatLean.Verification.Implementation.Native.Search
