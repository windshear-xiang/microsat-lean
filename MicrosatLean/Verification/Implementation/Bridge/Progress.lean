import MicrosatLean.Verification.Progress
import MicrosatLean.Verification.Implementation.Bridge.ToConcrete
import MicrosatLean.Verification.Implementation.Search.Concrete.Termination

namespace MicrosatLean.Verification.Implementation.Bridge

theorem concrete_decreases : StepDecreases := by
  intro formula before after beforeValid afterValid transition
  obtain ⟨a, w, certificate⟩ := beforeValid
  have variables : before.solver.nVars = max 1 formula.numVars :=
    certificate.representation.variables.symm.trans certificate.variables
  have decreasing := Search.Concrete.MachineInvariant.step_rank
    (concrete_of_certificate certificate) (concrete_of_inv afterValid)
    (max 1 formula.numVars) variables transition
  simpa only [variant] using decreasing

end MicrosatLean.Verification.Implementation.Bridge
