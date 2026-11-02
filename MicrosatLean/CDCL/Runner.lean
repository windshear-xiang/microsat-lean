import MicrosatLean.Verification.Termination

/-! 只负责执行的 total runner。它调用真实 step，并用 invariant preservation 与 rank decrease 证明递归合法。
返回值是普通 SolveResult；有限 runFor 对应关系和结果正确性在 Verification/Correctness 中另行证明。
invariant 和 termination proofs 在编译时擦除。
-/

namespace MicrosatLean.CDCL

/-- 不断调用实际 step，直到得到 SolveResult。running 分支用 step_preserves 得到下一次调用所需的 invariant，
并用 step_decreases 证明同一 variant 严格下降，从而使递归 total。
返回值不携带 correctness certificate；相关 theorem 在验证层另行证明。
-/
def run (formula : Formula) (machine : Machine)
    (valid : Verification.Inv formula machine) : SolveResult :=
  match transition : step machine with
  | .finished result => result
  | .running after => run formula after (Verification.step_preserves valid transition)
termination_by Verification.variant (max 1 formula.numVars) machine
decreasing_by exact Verification.step_decreases valid transition

end MicrosatLean.CDCL
