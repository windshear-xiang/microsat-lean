import MicrosatLean.Solver
import MicrosatLean.Verification.Implementation.Obligations

namespace MicrosatLean.Verification

/-!
The executable definitions live in CDCL/Runner and Solver. This module proves
their finite runFor correspondence and result correctness after the fact.
Theorems ending in `_with` expose the logical implementation contracts; the
public correctness theorems instantiate them with the closed actual proofs.
-/

theorem step_correct_with (facts : ImplementationFacts) {formula : Formula}
    {machine : CDCL.Machine} (valid : Inv formula machine) :
    InvariantProgress formula (CDCL.step machine) := by
  obtain ⟨state, witness, certificate⟩ := valid
  have outcome := phase_correct facts certificate
  cases transition : CDCL.step machine with
  | running after =>
    exact RunningPost.invariant facts.logicalMoves certificate
      (show RunningPost formula state after from by simpa only [transition] using outcome)
  | finished result =>
    obtain ⟨next, execution, terminal⟩ :=
      (show FinishedPost formula state result from by simpa only [transition] using outcome)
    exact facts.terminal formula next result
      (execution_preserves facts.logicalMoves certificate.semantic execution) terminal

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

/-- The plain runner follows a finite execution of the actual bounded runner. -/
theorem run_finishes (formula : Formula) (machine : CDCL.Machine)
    (valid : Inv formula machine) :
    ∃ fuel, CDCL.runFor fuel machine = .finished (CDCL.run formula machine valid) := by
  rw [CDCL.run]
  split
  · rename_i result transition
    exact ⟨1, by simp only [CDCL.runFor, transition]⟩
  · rename_i after transition
    obtain ⟨fuel, finished⟩ := run_finishes formula after (step_preserves valid transition)
    exact ⟨fuel + 1, by simpa only [CDCL.runFor, transition] using finished⟩
termination_by variant (max 1 formula.numVars) machine
decreasing_by exact step_decreases valid (by assumption)

/-- Result validity is a theorem about the plain executable runner. -/
theorem run_correct {formula : Formula} {machine : CDCL.Machine}
    (valid : Inv formula machine) : ValidResult formula (CDCL.run formula machine valid) := by
  obtain ⟨fuel, finished⟩ := run_finishes formula machine valid
  have safe := runFor_correct_with Implementation.actualFacts fuel valid
  simpa only [finished, InvariantProgress] using safe

theorem initialized_search_correct_with (facts : ImplementationFacts) {formula : Formula}
    (valid : WellFormed formula) {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    ∃ fuel result, CDCL.runFor fuel (CDCL.Machine.initial s) = .finished result ∧ ValidResult formula result := by
  have initial := initial_invariant valid initialized
  obtain ⟨fuel, finished⟩ := run_finishes formula (CDCL.Machine.initial s) initial
  have safe := runFor_correct_with facts fuel initial
  exact ⟨fuel, _, finished, by simpa only [finished, InvariantProgress] using safe⟩

/-- Compatibility name for the public pure solver; it adds no execution layer. -/
abbrev solveCertified (formula : Formula) (config : CDCL.Config := {}) :=
  CDCL.solvePure formula config

theorem solveCertified_correct (formula : Formula) (valid : WellFormed formula)
    (config : CDCL.Config := {}) :
    ∃ result, solveCertified formula config = .ok result ∧ ValidResult formula result := by
  unfold solveCertified CDCL.solvePure
  simp only [dite_eq_left valid]
  split
  · rename_i message failed
    obtain ⟨outcome, initialized, _⟩ := Implementation.actualFacts.initialization formula valid config
    rw [failed] at initialized
    cases initialized
  · rename_i initialized
    obtain ⟨outcome, actual, checked⟩ := Implementation.actualFacts.initialization formula valid config
    have same : outcome = none := Except.ok.inj (actual.symm.trans initialized)
    exact ⟨.unsat {}, rfl, by simpa only [same, ValidResult] using checked⟩
  · exact ⟨_, rfl, run_correct _⟩

theorem solveCertified_ok_valid {formula : Formula} {config : CDCL.Config}
    {result : CDCL.SolveResult} (returned : solveCertified formula config = .ok result) :
    ValidResult formula result := by
  by_cases valid : WellFormed formula
  · obtain ⟨actual, equal, correct⟩ := solveCertified_correct formula valid config
    cases Except.ok.inj (equal.symm.trans returned)
    exact correct
  · simp only [solveCertified, CDCL.solvePure, dite_eq_right valid] at returned
    cases returned

/-- Compatibility name retained for callers of the initial framework. -/
abbrev solveScaffold (formula : Formula) (config : CDCL.Config := {}) :=
  CDCL.solvePure formula config

theorem solveScaffold_correct (formula : Formula) (valid : WellFormed formula)
    (config : CDCL.Config := {}) :
    ∃ result, solveScaffold formula config = .ok result ∧ ValidResult formula result :=
  solveCertified_correct formula valid config

theorem initialized_search_terminates {formula : Formula} (valid : WellFormed formula)
    {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    ∃ fuel result, CDCL.runFor fuel (CDCL.Machine.initial s) = .finished result ∧ ValidResult formula result :=
  initialized_search_correct_with Implementation.actualFacts valid initialized

end MicrosatLean.Verification

namespace MicrosatLean.CDCL

/-- The public IO entry returns a valid result for every well-formed input. -/
theorem solve_correct (formula : Formula) (valid : Verification.WellFormed formula)
    (config : Config := {}) :
    ∃ result, solve formula config = pure (.ok result) ∧ Verification.ValidResult formula result := by
  obtain ⟨result, returned, correct⟩ := Verification.solveCertified_correct formula valid config
  exact ⟨result, by simp only [solve, returned], correct⟩

end MicrosatLean.CDCL
