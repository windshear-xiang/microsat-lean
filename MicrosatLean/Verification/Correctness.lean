import MicrosatLean.Verification.Implementation.Obligations

namespace MicrosatLean.Verification

/-!
Theorems ending in `_with` expose the implementation interface explicitly.
The final solver instantiates it with the closed implementation proofs. Values
are computed by the real transition; well-founded recursion supplies a total
runner, and its certificate connects the result to finite `runFor` execution.
-/

theorem step_correct_with (facts : ImplementationFacts) {formula : Formula}
    {machine : CDCL.Machine} (valid : Inv formula machine) :
    InvariantProgress formula (CDCL.step machine) := by
  obtain ⟨state, witness, certificate⟩ := valid
  have outcome := phase_correct facts certificate
  cases transition : CDCL.step machine with
  | running after =>
    obtain ⟨next, nextWitness, represented, variables, execution, control, progress⟩ :=
      (show RunningPost formula state after from by simpa only [transition] using outcome)
    exact ⟨next, nextWitness, certificate.input, variables, represented,
      execution_preserves facts.logicalMoves certificate.semantic execution, control, progress⟩
  | finished result =>
    obtain ⟨next, execution, terminal⟩ :=
      (show FinishedPost formula state result from by simpa only [transition] using outcome)
    exact facts.terminal formula next result
      (execution_preserves facts.logicalMoves certificate.semantic execution) terminal

theorem step_running_with (facts : ImplementationFacts) {formula : Formula}
    {before after : CDCL.Machine} (valid : Inv formula before)
    (transition : CDCL.step before = .running after) : Inv formula after := by
  simpa only [transition, InvariantProgress] using step_correct_with facts valid

theorem runFor_correct_with (facts : ImplementationFacts) {formula : Formula}
    (fuel : Nat) {machine : CDCL.Machine} (valid : Inv formula machine) :
    InvariantProgress formula (CDCL.runFor fuel machine) := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih =>
    have safe := step_correct_with facts valid
    cases transition : CDCL.step machine with
    | running next =>
      have nextValid : Inv formula next := by
        simpa only [transition, InvariantProgress] using safe
      simpa only [CDCL.runFor, transition] using ih nextValid
    | finished result =>
      simpa only [CDCL.runFor, transition, InvariantProgress] using safe

def TotalRunSpec (formula : Formula) (machine : CDCL.Machine) (result : CDCL.SolveResult) : Prop :=
  ValidResult formula result ∧ ∃ fuel, CDCL.runFor fuel machine = .finished result

/-- Proofs are carried separately from the logical invariant. This keeps the
termination justification available on each recursive call, without putting
future progress into Inv. Only machine contributes runtime data. -/
private structure ExecutionState (formula : Formula) where
  machine : CDCL.Machine
  valid : Inv formula machine
  facts : ImplementationFacts

/-- The recursive value uses only the real step function. Certificates and
the variant justify recursion in Prop and are erased by compilation. -/
private def runCertified (formula : Formula) (state : ExecutionState formula) :
    { result : CDCL.SolveResult // TotalRunSpec formula state.machine result } :=
  match transition : CDCL.step state.machine with
  | .finished result =>
    ⟨result, by
      have safe := step_correct_with state.facts state.valid
      exact ⟨by simpa only [transition, InvariantProgress] using safe,
        ⟨1, by simp only [CDCL.runFor, transition]⟩⟩⟩
  | .running after =>
    let afterValid := step_running_with state.facts state.valid transition
    let result := runCertified formula ⟨after, afterValid, state.facts⟩
    ⟨result.val, by
      obtain ⟨correct, fuel, finished⟩ := result.property
      exact ⟨correct, ⟨fuel + 1, by simpa only [CDCL.runFor, transition] using finished⟩⟩⟩
termination_by variant (max 1 formula.numVars) state.machine
decreasing_by
  exact state.facts.decreases formula state.machine after state.valid afterValid transition

def runCertifiedWith (facts : ImplementationFacts) (formula : Formula)
    (machine : CDCL.Machine) (valid : Inv formula machine) :
    { result : CDCL.SolveResult // TotalRunSpec formula machine result } :=
  runCertified formula ⟨machine, valid, facts⟩

theorem initialized_search_correct_with (facts : ImplementationFacts) {formula : Formula}
    (valid : WellFormed formula) {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    ∃ fuel result, CDCL.runFor fuel (InitialMachine s) = .finished result ∧ ValidResult formula result := by
  obtain ⟨outcome, actual, checked⟩ := facts.initialization formula valid config
  have same : outcome = some s := Except.ok.inj (actual.symm.trans initialized)
  subst outcome
  obtain ⟨result, correct, fuel, finished⟩ := runCertifiedWith facts formula (InitialMachine s) checked
  exact ⟨fuel, result, finished, correct⟩

theorem initialization_no_error_with (facts : ImplementationFacts) {formula : Formula}
    (valid : WellFormed formula) (config : CDCL.Config) (message : String)
    (failed : CDCL.initState formula config = .error message) : False := by
  obtain ⟨outcome, initialized, _⟩ := facts.initialization formula valid config
  rw [failed] at initialized
  cases initialized

def solveWellFormedWith (facts : ImplementationFacts) (formula : Formula)
    (valid : WellFormed formula) (config : CDCL.Config := {}) : CDCL.SolveResult :=
  match initialized : CDCL.initState formula config with
  | .error message => False.elim (initialization_no_error_with facts valid config message initialized)
  | .ok none => .unsat {}
  | .ok (some s) =>
    have initial : Inv formula (InitialMachine s) := by
      obtain ⟨outcome, actual, checked⟩ := facts.initialization formula valid config
      have same : outcome = some s := Except.ok.inj (actual.symm.trans initialized)
      simpa only [same] using checked
    (runCertifiedWith facts formula (InitialMachine s) initial).val

def solveWith (facts : ImplementationFacts) (formula : Formula) (config : CDCL.Config := {}) :
    Except String CDCL.SolveResult :=
  if valid : WellFormed formula then .ok (solveWellFormedWith facts formula valid config)
  else .error "literal outside the declared variable bounds"

theorem solveWellFormed_correct_with (facts : ImplementationFacts) (formula : Formula)
    (valid : WellFormed formula) (config : CDCL.Config := {}) :
    ValidResult formula (solveWellFormedWith facts formula valid config) := by
  unfold solveWellFormedWith
  split
  · rename_i message failed
    exact False.elim (initialization_no_error_with facts valid config message failed)
  · rename_i initialized
    obtain ⟨outcome, actual, checked⟩ := facts.initialization formula valid config
    have same : outcome = none := Except.ok.inj (actual.symm.trans initialized)
    simpa only [same, ValidResult] using checked
  · exact (runCertifiedWith facts _ _ _).property.1

theorem solve_correct_with (facts : ImplementationFacts) (formula : Formula)
    (valid : WellFormed formula) (config : CDCL.Config := {}) :
    ∃ result, solveWith facts formula config = .ok result ∧ ValidResult formula result :=
  ⟨solveWellFormedWith facts formula valid config,
    by simp only [solveWith, dite_eq_left valid],
    solveWellFormed_correct_with facts formula valid config⟩

/-- Total certified entry used by the public IO wrapper. -/
def solveCertified (formula : Formula) (config : CDCL.Config := {}) : Except String CDCL.SolveResult :=
  solveWith Implementation.actualFacts formula config

theorem solveCertified_correct (formula : Formula) (valid : WellFormed formula)
    (config : CDCL.Config := {}) :
    ∃ result, solveCertified formula config = .ok result ∧ ValidResult formula result :=
  solve_correct_with Implementation.actualFacts formula valid config

theorem solveCertified_ok_valid {formula : Formula} {config : CDCL.Config}
    {result : CDCL.SolveResult} (returned : solveCertified formula config = .ok result) :
    ValidResult formula result := by
  unfold solveCertified solveWith at returned
  split at returned
  · cases returned
    exact solveWellFormed_correct_with _ _ _ _
  · cases returned

/-- Compatibility name retained for callers of the initial framework. -/
abbrev solveScaffold (formula : Formula) (config : CDCL.Config := {}) :=
  solveCertified formula config

theorem solveScaffold_correct (formula : Formula) (valid : WellFormed formula)
    (config : CDCL.Config := {}) :
    ∃ result, solveScaffold formula config = .ok result ∧ ValidResult formula result :=
  solveCertified_correct formula valid config

theorem initialized_search_terminates {formula : Formula} (valid : WellFormed formula)
    {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    ∃ fuel result, CDCL.runFor fuel (InitialMachine s) = .finished result ∧ ValidResult formula result :=
  initialized_search_correct_with Implementation.actualFacts valid initialized

end MicrosatLean.Verification
