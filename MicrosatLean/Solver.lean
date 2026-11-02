import MicrosatLean.Verification.Correctness

namespace MicrosatLean.CDCL

/-- Execute the same CDCL transition through its proved total runner. -/
def solve (formula : Formula) (config : Config := {}) : IO (Except String SolveResult) :=
  pure (Verification.solveCertified formula config)

/-- The public IO entry returns a valid result for every well-formed input.
The implementation package and all its dependencies are proved. -/
theorem solve_correct (formula : Formula) (valid : Verification.WellFormed formula)
    (config : Config := {}) :
    ∃ result, solve formula config = pure (.ok result) ∧ Verification.ValidResult formula result := by
  obtain ⟨result, returned, correct⟩ := Verification.solveCertified_correct formula valid config
  exact ⟨result, by simp only [solve, returned], correct⟩

end MicrosatLean.CDCL
