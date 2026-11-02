import MicrosatLean.Verification.Contracts
import MicrosatLean.Verification.Implementation.Logic.Terminal
import MicrosatLean.Verification.Implementation.Logic.Moves
import MicrosatLean.Verification.Implementation.Search.Begin
import MicrosatLean.Verification.Implementation.Search.Next
import MicrosatLean.Verification.Implementation.Bridge.ToNativeInitialization
import MicrosatLean.Verification.Implementation.Bridge.ToNativeProgress
import MicrosatLean.Verification.Implementation.Search.Watch
import MicrosatLean.Verification.Implementation.Search.Choose

namespace MicrosatLean.Verification.Implementation

/-!
The implementation obligations are discharged by the modules imported above.
This small assembly is the only implementation package used by Correctness.
Logical rules, real phase refinement and concrete rank decrease remain separate
proofs. Their source-specific details live below Search, Bridge and Native.
-/

/-- Pure logical obligation: ordered reasons survive append/truncation,
learning/forgetting/permutation preserve meaning, and root promotion is sound. -/
theorem logical_moves : LogicalSoundness := by
  exact Logic.logical_moves

/-- Pure logical obligation: complete unit closure yields SAT; a false clause
on an input-entailed root trail yields UNSAT, using the standard CNF semantics. -/
theorem terminal : TerminalSoundness := by
  exact Logic.terminal

/-- Actual normalization, packed allocation, initial units and watch lists. -/
theorem initialization : InitializationCorrect := by
  exact Bridge.concrete_initialization

/-- Actual root-mode guard, old-counter reset and unchanged state fields. -/
theorem begin_propagation : PhaseCorrect .beginPropagation := by
  exact Search.begin_propagation

/-- Actual pending-literal branch or propagation-completion/root commit. -/
theorem next_literal : PhaseCorrect .nextLiteral := by
  exact Search.next_literal

/-- Actual watch loops, no missed/exhausted scans, unit reasons, first-UIP,
recursive minimization, backjump/assertion, and saved-prefix recovery. -/
theorem watch : PhaseCorrect .watch := by
  exact Search.watch

/-- Actual restart/reduction, reason relocation, decision cursor, fresh
decision or genuine SAT completion. No after-closure premise is supplied. -/
theorem choose : PhaseCorrect .choose := by
  exact Search.choose

/-- Actual rank decrease, including canonical freshness, the 3^n bound,
limit growth under reduction, restart credit and finite internal scans. -/
theorem decreases : StepDecreases := by
  exact Bridge.concrete_decreases

theorem actualFacts : ImplementationFacts :=
  ⟨logical_moves, terminal, initialization, begin_propagation,
    next_literal, watch, choose, decreases⟩

end MicrosatLean.Verification.Implementation
