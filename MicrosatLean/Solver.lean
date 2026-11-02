import MicrosatLean.CDCL.Search

/-!
生产求解入口：先检查输入，再通过独立 IO 驱动反复执行 CDCL 批次。此入口不导入验证框架。
-/

namespace MicrosatLean.CDCL

/-- 反复恢复 CDCL 分批执行器，无需依赖验证模块。
只有这个不设总步数上限的 IO 驱动使用 `partial`；每一批执行仍会终止。 -/
private partial def drive (machine : Machine) : IO SolveResult := do
  match runFor 4096 machine with
  | .finished result => return result
  | .running next => drive next

/-- 先检查全部输入文字的范围，再初始化并运行 CDCL 核心。
此预检查与 `Tim-dev-verification` 分支的公开入口保持一致。 -/
def solve (formula : Formula) (config : Config := {}) : IO (Except String SolveResult) := do
  if !formula.wellFormed then
    return .error "literal outside the declared variable bounds"
  match initState formula config with
  | .error message => return .error message
  | .ok none => return .ok (.unsat {})
  | .ok (some state) =>
    return .ok (← drive { solver := state, decision := state.head })

end MicrosatLean.CDCL
