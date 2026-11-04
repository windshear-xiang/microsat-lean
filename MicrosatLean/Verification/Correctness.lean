import MicrosatLean.Solver
import MicrosatLean.Verification.Implementation.Obligations

namespace MicrosatLean.Verification

/-!
The executable definitions live in CDCL/Runner and Solver. Result correctness
is proved directly along the runner's well-founded recursion. The single-step
theorem exposes the implementation contracts; the runner and solver theorems
instantiate them with the completed implementation proofs.
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

/-- Prove result validity by well-founded induction on the runner's shared rank. -/
theorem run_correct {formula : Formula} {machine : CDCL.Machine}
    (valid : Inv formula machine) : ValidResult formula (CDCL.run formula machine valid) := by
  rw [CDCL.run]
  split
  · rename_i result transition
    have safe := step_correct_with Implementation.actualFacts valid
    simpa only [transition, InvariantProgress] using safe
  · rename_i after transition
    exact run_correct (step_preserves valid transition)
termination_by variant (max 1 formula.numVars) machine
decreasing_by exact step_decreases valid (by assumption)

/-- The pure solver succeeds with a valid result for every well-formed input. -/
theorem solvePure_correct (formula : Formula) (valid : WellFormed formula)
    (config : CDCL.Config := {}) :
    ∃ result, CDCL.solvePure formula config = .ok result ∧ ValidResult formula result := by
  unfold CDCL.solvePure
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

end MicrosatLean.Verification

namespace MicrosatLean.CDCL

/-- The public IO entry returns a valid result for every well-formed input. -/
theorem solve_correct (formula : Formula) (valid : Verification.WellFormed formula)
    (config : Config := {}) :
    ∃ result, solve formula config = pure (.ok result) ∧ Verification.ValidResult formula result := by
  obtain ⟨result, returned, correct⟩ := Verification.solvePure_correct formula valid config
  exact ⟨result, by simp only [solve, returned], correct⟩

end MicrosatLean.CDCL
