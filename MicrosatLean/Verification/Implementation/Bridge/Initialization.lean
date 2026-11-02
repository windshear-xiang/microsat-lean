import MicrosatLean.Verification.Contracts
import MicrosatLean.Verification.Implementation.Bridge.FromConcrete

namespace MicrosatLean.Verification.Implementation.Bridge

/-- The real normalizer/allocator establishes the readable invariant, while
the real initializer's empty-clause and conflicting-unit exits prove UNSAT. -/
theorem concrete_initialization : InitializationCorrect := by
  intro formula valid config
  obtain ⟨outcome, initialized, checked⟩ :=
    Initialization.initState_outcome valid config
  refine ⟨outcome, initialized, ?_⟩
  cases outcome with
  | none => exact checked
  | some s =>
    exact of_concrete valid
      (Search.Concrete.initState_some_machineInvariant valid initialized)
      (Initialization.initState_some_variables valid initialized)

end MicrosatLean.Verification.Implementation.Bridge
