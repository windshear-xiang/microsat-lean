import MicrosatLean.Verification.Progress
import MicrosatLean.Verification.Implementation.Bridge.ToNative
import MicrosatLean.Verification.Implementation.Native.Search.Termination

namespace MicrosatLean.Verification.Implementation.Bridge

/-- The public variant is exactly the checked native control rank. -/
theorem variant_eq_native (variables : Nat) (machine : CDCL.Machine) :
    variant variables machine = Native.Search.controlRank (3 ^ variables) variables machine := by
  cases phase : machine.phase <;>
    simp only [variant, Native.Search.controlRank, Native.Search.clauseProgress,
      numericProgress, Native.Search.numericProgress, Native.Search.capacityDebt,
      Native.Search.clauseDebt, learningCredit, Native.Search.learningCredit,
      phaseRank, Native.Search.phaseRank, phase]

theorem concrete_decreases : StepDecreases := by
  intro formula before after beforeValid afterValid transition
  obtain ⟨a, w, certificate⟩ := beforeValid
  have variables : before.solver.nVars = max 1 formula.numVars :=
    certificate.representation.variables.symm.trans certificate.variables
  have decreasing := Native.Search.MachineInvariant.step_rank
    (native_of_certificate certificate) (native_of_inv afterValid)
    (max 1 formula.numVars) variables transition
  simpa only [variant_eq_native, RankLT, Native.Search.ControlRankLT] using decreasing

end MicrosatLean.Verification.Implementation.Bridge
