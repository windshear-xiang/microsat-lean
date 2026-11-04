import MicrosatLean.Verification.Implementation.Logic.Terminal
import MicrosatLean.Verification.Implementation.Logic.Moves
import MicrosatLean.Verification.Implementation.Search.Begin
import MicrosatLean.Verification.Implementation.Search.Next
import MicrosatLean.Verification.Implementation.Bridge.Initialization
import MicrosatLean.Verification.Implementation.Bridge.Progress
import MicrosatLean.Verification.Implementation.Search.Watch
import MicrosatLean.Verification.Implementation.Search.Choose

namespace MicrosatLean.Verification.Implementation

/-- Assemble the eight closed contracts used by Correctness. Each field points
directly to its operation proof; the contracts are declared in Contracts.lean. -/
theorem actualFacts : ImplementationFacts where
  logicalMoves := Logic.logical_moves
  terminal := Logic.terminal
  initialization := Bridge.concrete_initialization
  beginPropagation := Search.begin_propagation
  nextLiteral := Search.next_literal
  watch := Search.watch
  choose := Search.choose
  decreases := Bridge.concrete_decreases

end MicrosatLean.Verification.Implementation
