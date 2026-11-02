import MicrosatLean.Verification.Implementation.Bridge.FromNativeControl
import MicrosatLean.Verification.Implementation.Bridge.FromNativeProgress

namespace MicrosatLean.Verification.Implementation.Bridge

/-! The low-level certificate determines a single readable logical state.
All components refer to the same packed entries, true trail and watch heads. -/

theorem from_native {formula : Formula} (valid : WellFormed formula) {m : CDCL.Machine}
    (native : Native.Search.MachineInvariant formula m)
    (variables : m.solver.nVars = max 1 formula.numVars) : Inv formula m := by
  obtain ⟨original, learned, heads, rank, certificate⟩ := native
  obtain ⟨order, ordered⟩ := certificate.base.order
  exact ⟨nativeState m.solver original learned, nativeWitness original learned heads order,
    valid, variables, native_rep certificate.base ordered, native_semantic certificate.base ordered,
    native_control certificate ordered, native_progress certificate.base⟩

end MicrosatLean.Verification.Implementation.Bridge
