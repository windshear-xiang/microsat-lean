import MicrosatLean.Verification.Solver

namespace MicrosatLean.CDCL

/-- Run the verified total CDCL solver through the existing IO interface. -/
def solve (formula : Formula) (config : Config := {}) : IO (Except String SolveResult) :=
  pure (Verification.solveVerified formula config)

end MicrosatLean.CDCL
