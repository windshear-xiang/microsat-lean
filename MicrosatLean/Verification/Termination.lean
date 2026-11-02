import MicrosatLean.Verification.Implementation.Logic.Moves
import MicrosatLean.Verification.Implementation.Search.Begin
import MicrosatLean.Verification.Implementation.Search.Next
import MicrosatLean.Verification.Implementation.Search.Concrete.MachineWatch
import MicrosatLean.Verification.Implementation.Search.Concrete.MachineChoice
import MicrosatLean.Verification.Implementation.Bridge.FromConcrete
import MicrosatLean.Verification.Implementation.Bridge.Progress

namespace MicrosatLean.Verification

/-!
The executable runner needs only initialization, preservation on running steps,
and strict rank decrease. These proofs use the existing implementation lemmas
without importing final correctness or the completed ImplementationFacts proof.
Watch and choice reuse concrete preservation; their logical execution traces
and terminal gates are needed only by the separate correctness composition.
No theorem in this module assumes validity of a returned SAT/UNSAT result.
-/

/-- Successful initialization establishes the invariant required by the runner. -/
theorem initial_invariant {formula : Formula} (valid : WellFormed formula)
    {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    Inv formula (InitialMachine s) :=
  Implementation.Bridge.of_concrete valid
    (Implementation.Search.Concrete.initState_some_machineInvariant valid initialized)
    (Implementation.Initialization.initState_some_variables valid initialized)

/-- Only running outcomes require a preserved invariant for the next call. -/
theorem step_preserves {formula : Formula} {before after : CDCL.Machine}
    (valid : Inv formula before) (transition : CDCL.step before = .running after) :
    Inv formula after := by
  obtain ⟨state, witness, certificate⟩ := valid
  have refinePhase {phase : CDCL.Phase} (correct : PhaseCorrect phase)
      (same : before.phase = phase) : Inv formula after := by
    have post : RunningPost formula state after := by
      simpa only [transition] using correct formula before state witness certificate same
    exact post.invariant Implementation.Logic.logical_moves certificate
  have recover (concrete : Implementation.Search.Concrete.MachineInvariant formula after) :
      Inv formula after :=
    Implementation.Bridge.of_concrete certificate.input concrete
      ((Implementation.Search.Concrete.step_nVars transition).trans
        (certificate.representation.variables.symm.trans certificate.variables))
  cases phase : before.phase with
  | beginPropagation => exact refinePhase Implementation.Search.begin_propagation phase
  | nextLiteral => exact refinePhase Implementation.Search.next_literal phase
  | watch =>
    apply recover
    simpa only [transition, Implementation.Search.Concrete.InvariantProgress] using
      Implementation.Search.Concrete.step_watch_invariant
        (Implementation.Bridge.concrete_of_certificate certificate) phase
  | choose =>
    apply recover
    simpa only [transition, Implementation.Search.Concrete.InvariantProgress] using
      Implementation.Search.Concrete.step_choose_invariant
        (Implementation.Bridge.concrete_of_certificate certificate) phase

/-- The shared rank strictly decreases at every recursive call. -/
theorem step_decreases {formula : Formula} {before after : CDCL.Machine}
    (valid : Inv formula before) (transition : CDCL.step before = .running after) :
    RankLT (variant (max 1 formula.numVars) after) (variant (max 1 formula.numVars) before) :=
  Implementation.Bridge.concrete_decreases formula before after valid
    (step_preserves valid transition) transition

end MicrosatLean.Verification
