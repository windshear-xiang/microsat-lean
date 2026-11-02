import MicrosatLean.CDCL.Runner

namespace MicrosatLean.CDCL

/-- Check input bounds, initialize, and execute the total search loop. -/
def solvePure (formula : Formula) (config : Config := {}) : Except String SolveResult :=
  if valid : Verification.WellFormed formula then
    match initialized : initState formula config with
    | .error message => .error message
    | .ok none => .ok (.unsat {})
    | .ok (some s) =>
      .ok (run formula (Verification.InitialMachine s)
        (Verification.initial_invariant valid initialized))
  else .error "literal outside the declared variable bounds"

/-- Public IO entry; logical correctness is proved in Verification/Correctness. -/
def solve (formula : Formula) (config : Config := {}) : IO (Except String SolveResult) :=
  pure (solvePure formula config)

end MicrosatLean.CDCL
