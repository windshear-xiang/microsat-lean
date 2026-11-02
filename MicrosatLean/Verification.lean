import MicrosatLean.Verification.Correctness

/-!
便于人工阅读的验证框架聚合入口。建议从 Specification、Model、Invariant、Transitions、
Progress 和 Contracts 开始；Correctness 将它们组合为整体结论。
当前所有待补证明集中在 Implementation/Obligations 中。此聚合模块需显式导入，
可执行库和 CLI 入口均不导入它。
-/
