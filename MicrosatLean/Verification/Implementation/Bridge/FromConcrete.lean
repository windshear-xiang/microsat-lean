import MicrosatLean.Verification.Implementation.Bridge.FromConcreteControl
import MicrosatLean.Verification.Implementation.Bridge.FromConcreteProgress

namespace MicrosatLean.Verification.Implementation.Bridge

/-! The low-level certificate determines a single readable logical state.
All components refer to the same packed entries, true trail and watch heads. -/

theorem of_concrete {formula : Formula} (valid : WellFormed formula) {m : CDCL.Machine}
    (concrete : Search.Concrete.MachineInvariant formula m)
    (variables : m.solver.nVars = max 1 formula.numVars) : Inv formula m := by
  obtain ⟨original, learned, heads, rank, certificate⟩ := concrete
  obtain ⟨order, ordered⟩ := certificate.base.order
  exact ⟨logicalView m.solver original learned, representationWitness original learned heads order,
    valid, variables, view_rep certificate.base ordered, view_semantic certificate.base ordered,
    view_control certificate ordered, view_progress certificate.base⟩

end MicrosatLean.Verification.Implementation.Bridge
