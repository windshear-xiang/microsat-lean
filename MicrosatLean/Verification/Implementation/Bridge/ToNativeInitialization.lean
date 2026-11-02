import MicrosatLean.Verification.Contracts
import MicrosatLean.Verification.Implementation.Bridge.FromNative

namespace MicrosatLean.Verification.Implementation.Bridge

/-- The real normalizer/allocator establishes the readable invariant, while
the real initializer's empty-clause and conflicting-unit exits prove UNSAT. -/
theorem concrete_initialization : InitializationCorrect := by
  intro formula valid config
  have nativeValid : MicrosatLean.Verification.WellFormed formula := valid
  obtain ⟨outcome, initialized, checked⟩ :=
    Native.Initialization.initState_outcome nativeValid config
  refine ⟨outcome, initialized, ?_⟩
  cases outcome with
  | none => exact checked
  | some s =>
    exact from_native valid
      (Native.Search.initState_some_machineInvariant nativeValid initialized)
      (Native.Initialization.initState_some_variables nativeValid initialized)

end MicrosatLean.Verification.Implementation.Bridge
