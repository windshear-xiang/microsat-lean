import MicrosatLean.Verification.Implementation.Logic.Terminal
import MicrosatLean.Verification.Implementation.Logic.Moves
import MicrosatLean.Verification.Implementation.Search.Begin
import MicrosatLean.Verification.Implementation.Search.Next
import MicrosatLean.Verification.Implementation.Bridge.Initialization
import MicrosatLean.Verification.Implementation.Bridge.Progress
import MicrosatLean.Verification.Implementation.Search.Watch
import MicrosatLean.Verification.Implementation.Search.Choose

namespace MicrosatLean.Verification.Implementation

/-!
将上面导入的具体实现证明组装为 Correctness 使用的完整 ImplementationFacts 证明包。
逻辑规则、实际 phase refinement 与具体 rank decrease 分别证明，再在这里汇总；
具体操作的细节位于 Search、Bridge 和各操作对应的证明目录中。
本文件只组合已经完成的证明；实际执行入口不接收这个证明包。
-/

/-- 逻辑迁移的 soundness：追加或截短 trail 保持 reason 顺序，learning、forgetting 和 permutation
保持数据库语义，扩展 root 前缀时也建立其 soundness。 -/
theorem logical_moves : LogicalSoundness := by
  exact Logic.logical_moves

/-- 标准 CNF 语义下的 terminal soundness：完整赋值与 unit closure 支持 SAT；
被输入蕴含的 root trail 上出现全假的存储 clause，则支持 UNSAT。 -/
theorem terminal : TerminalSoundness := by
  exact Logic.terminal

/-- 真实初始化满足 contract：包括 normalization、packed arena 分配、初始 units 和 watch lists，
以及提前 UNSAT 或建立初始 invariant 的正确性。 -/
theorem initialization : InitializationCorrect := by
  exact Bridge.concrete_initialization

/-- beginPropagation 的真实 phase refinement：正确建立 root 模式、重设旧 learned 计数，
并保持相关 solver state 字段。 -/
theorem begin_propagation : PhaseCorrect .beginPropagation := by
  exact Search.begin_propagation

/-- nextLiteral 的真实 phase refinement：取出待传播 literal，或结束传播并按需提交 root 前缀。 -/
theorem next_literal : PhaseCorrect .nextLiteral := by
  exact Search.next_literal

/-- watch 的真实 phase refinement：扫描不遗漏且预算充分，unit reason 有效；
冲突分支覆盖 first UIP、递归 minimization、backjump、asserting propagation 与 saved-prefix 恢复。 -/
theorem watch : PhaseCorrect .watch := by
  exact Search.watch

/-- choose 的真实 phase refinement：覆盖 restart/reduction、reason 地址重映射和 decision cursor，
随后作出 fresh decision 或满足真正的 SAT gate；所需的输出传播闭包由证明建立。 -/
theorem choose : PhaseCorrect .choose := by
  exact Search.choose

/-- 实际 running step 的 rank decrease：结合 canonical freshness、3^n clause-space 上界、
reduction 时上限增长、restart credit 和内部扫描的有限界。 -/
theorem decreases : StepDecreases := by
  exact Bridge.concrete_decreases

/-- 汇总八项已完成的证明义务，供最终 correctness composition 实例化 ImplementationFacts。 -/
theorem actualFacts : ImplementationFacts :=
  ⟨logical_moves, terminal, initialization, begin_propagation,
    next_literal, watch, choose, decreases⟩

end MicrosatLean.Verification.Implementation
