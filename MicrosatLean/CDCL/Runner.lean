import MicrosatLean.Verification.Termination

namespace MicrosatLean.CDCL

/-- Execute the actual transition until it returns a result. Invariant proofs
justify recursion and erase at runtime; the return value carries no certificate.
Result correctness and finite runFor correspondence are proved separately. -/
def run (formula : Formula) (machine : Machine)
    (valid : Verification.Inv formula machine) : SolveResult :=
  match transition : step machine with
  | .finished result => result
  | .running after => run formula after (Verification.step_preserves valid transition)
termination_by Verification.variant (max 1 formula.numVars) machine
decreasing_by exact Verification.step_decreases valid transition

end MicrosatLean.CDCL
