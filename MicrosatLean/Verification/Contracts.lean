import MicrosatLean.Verification.Transitions
import MicrosatLean.Verification.Progress

namespace MicrosatLean.Verification

/-!
This file declares obligations as propositions, not axioms.
`Implementation/Obligations.lean` assembles their concrete proofs. The generic
correctness composition exposes this package explicitly. The executable runner
uses only the initialization, preservation and decrease proofs in Termination.

Dependencies: definitions -> contracts -> implementation proofs -> correctness.
No implementation proof may import Correctness or change this specification
merely to make a proof pass. Refining an internal invariant requires proving
initialization and preservation again.
-/

/-- Every well-formed input initializes without error. Early UNSAT is genuine;
otherwise the exact initial machine has the declared invariant. -/
def InitializationCorrect : Prop := ∀ formula,
  WellFormed formula → ∀ config : CDCL.Config,
    ∃ initialized, CDCL.initState formula config = .ok initialized ∧
      match initialized with
      | none => Std.Sat.CNF.Unsat (formulaView formula)
      | some s => Inv formula (CDCL.Machine.initial s)

/-- Output storage/control/progress facts are obligations. Semantic validity
is intentionally absent: Correctness derives it via LogicalExecution. -/
def RunningPost (formula : Formula) (before : LogicalState) (after : CDCL.Machine) : Prop :=
  ∃ next witness,
    Rep after next witness ∧ next.numVars = max 1 formula.numVars ∧
    LogicalExecution (formulaView formula) before next ∧
    ControlInv (formulaView formula) after next witness ∧ ProgressInv next

/-- A running refinement preserves the invariant through logical soundness.
This composition is shared by termination and final correctness. -/
theorem RunningPost.invariant {formula : Formula} {before after : CDCL.Machine}
    {state : LogicalState} {witness : RepresentationWitness}
    (sound : LogicalSoundness) (certificate : Certificate formula before state witness)
    (post : RunningPost formula state after) : Inv formula after := by
  obtain ⟨next, nextWitness, represented, variables, execution, control, progress⟩ := post
  exact ⟨next, nextWitness, certificate.input, variables, represented,
    execution_preserves sound certificate.semantic execution, control, progress⟩

/-- A terminal step must derive the logical SAT/UNSAT gate. It cannot assume
that its returned result already satisfies the final ValidResult predicate. -/
def FinishedPost (formula : Formula) (before : LogicalState) (result : CDCL.SolveResult) : Prop :=
  ∃ next, LogicalExecution (formulaView formula) before next ∧ Terminal formula next result

def PhaseCorrect (phase : CDCL.Phase) : Prop :=
  ∀ formula machine state witness,
    Certificate formula machine state witness → machine.phase = phase →
      match CDCL.step machine with
      | .running after => RunningPost formula state after
      | .finished result => FinishedPost formula state result

/-- All dependencies of the final composition, including pure logical rules,
are visible here. There is no assumed execution budget or correctness oracle.
The four phase obligations include allocation, normalization, watch scanning,
analysis/minimization, history recovery, restart and reduction as applicable. -/
structure ImplementationFacts : Prop where
  logicalMoves : LogicalSoundness
  terminal : TerminalSoundness
  initialization : InitializationCorrect
  beginPropagation : PhaseCorrect .beginPropagation
  nextLiteral : PhaseCorrect .nextLiteral
  watch : PhaseCorrect .watch
  choose : PhaseCorrect .choose
  decreases : StepDecreases

def InvariantProgress (formula : Formula) : CDCL.Progress → Prop
  | .running machine => Inv formula machine
  | .finished result => ValidResult formula result

theorem phase_correct (facts : ImplementationFacts) {formula : Formula}
    {machine : CDCL.Machine} {state : LogicalState} {witness : RepresentationWitness}
    (certificate : Certificate formula machine state witness) :
    match CDCL.step machine with
    | .running after => RunningPost formula state after
    | .finished result => FinishedPost formula state result := by
  cases phase : machine.phase with
  | beginPropagation => exact facts.beginPropagation _ _ _ _ certificate phase
  | nextLiteral => exact facts.nextLiteral _ _ _ _ certificate phase
  | watch => exact facts.watch _ _ _ _ certificate phase
  | choose => exact facts.choose _ _ _ _ certificate phase

end MicrosatLean.Verification
