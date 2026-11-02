import MicrosatLean.Verification.Progress
import MicrosatLean.Verification.Implementation.Bridge.ToNative
import MicrosatLean.Verification.Implementation.Native.Search.Termination

namespace MicrosatLean.Verification.Implementation.Bridge

theorem concrete_decreases : StepDecreases := by
  intro formula before after beforeValid afterValid transition
  obtain ⟨a, w, certificate⟩ := beforeValid
  have variables : before.solver.nVars = max 1 formula.numVars :=
    certificate.representation.variables.symm.trans certificate.variables
  have decreasing := Native.Search.MachineInvariant.step_rank
    (native_of_certificate certificate) (native_of_inv afterValid)
    (max 1 formula.numVars) variables transition
  simpa only [variant] using decreasing

end MicrosatLean.Verification.Implementation.Bridge
