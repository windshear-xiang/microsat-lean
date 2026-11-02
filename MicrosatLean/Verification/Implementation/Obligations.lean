import MicrosatLean.Verification.Contracts

namespace MicrosatLean.Verification.Implementation

/-!
ADMITTED IMPLEMENTATION OBLIGATIONS -- this is not completed verification.

Each named theorem is a replaceable leaf of the framework. Do not move these
assumptions into Inv, strengthen public input bounds, or add axioms. Future
proofs may be split into child modules while preserving these statements.
The audit in tests/Verification.lean lists every direct admission and checks
that none is hidden in a definition or in the composition proof.
-/

/-- Pure logical obligation: ordered reasons survive append/truncation,
learning/forgetting/permutation preserve meaning, and root promotion is sound. -/
theorem logical_moves : LogicalSoundness := by
  sorry

/-- Pure logical obligation: complete unit closure yields SAT; a false clause
on an input-entailed root trail yields UNSAT, using the standard CNF semantics. -/
theorem terminal : TerminalSoundness := by
  sorry

/-- Actual normalization, packed allocation, initial units and watch lists. -/
theorem initialization : InitializationCorrect := by
  sorry

/-- Actual root-mode guard, old-counter reset and unchanged state fields. -/
theorem begin_propagation : PhaseCorrect .beginPropagation := by
  sorry

/-- Actual pending-literal branch or propagation-completion/root commit. -/
theorem next_literal : PhaseCorrect .nextLiteral := by
  sorry

/-- Actual watch loops, no missed/exhausted scans, unit reasons, first-UIP,
recursive minimization, backjump/assertion, and saved-prefix recovery. -/
theorem watch : PhaseCorrect .watch := by
  sorry

/-- Actual restart/reduction, reason relocation, decision cursor, fresh
decision or genuine SAT completion. No after-closure premise is supplied. -/
theorem choose : PhaseCorrect .choose := by
  sorry

/-- Actual rank decrease, including canonical freshness, the 3^n bound,
limit growth under reduction, restart credit and finite internal scans. -/
theorem decreases : StepDecreases := by
  sorry

theorem actualFacts : ImplementationFacts :=
  ⟨logical_moves, terminal, initialization, begin_propagation,
    next_literal, watch, choose, decreases⟩

end MicrosatLean.Verification.Implementation
