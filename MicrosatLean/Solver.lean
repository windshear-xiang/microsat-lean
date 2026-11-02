import MicrosatLean.CDCL.Runner

/-! 公开求解入口：检查输入边界、初始化状态，再调用 total runner。
调用链为 solve → solvePure → run → step。最终结果的 correctness theorem 位于 Verification/Correctness。
-/

namespace MicrosatLean.CDCL

/-- 检查 WellFormed 输入边界，处理初始化的 error、提前 UNSAT 或正常 state，再调用 total runner。 -/
def solvePure (formula : Formula) (config : Config := {}) : Except String SolveResult :=
  if valid : Verification.WellFormed formula then
    match initialized : initState formula config with
    | .error message => .error message
    | .ok none => .ok (.unsat {})
    | .ok (some s) =>
      .ok (run formula (Verification.InitialMachine s)
        (Verification.initial_invariant valid initialized))
  else .error "literal outside the declared variable bounds"

/-- 保持公开 IO API 的薄包装；需要最终 correctness theorem 时导入 MicrosatLean.Verification。 -/
def solve (formula : Formula) (config : Config := {}) : IO (Except String SolveResult) :=
  pure (solvePure formula config)

end MicrosatLean.CDCL
