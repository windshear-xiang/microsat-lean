import MicrosatLean.Verification.Transitions
import MicrosatLean.Verification.Progress

namespace MicrosatLean.Verification

/-!
本文件将待证明责任定义为命题，不将它们声明为公理。
`Implementation/Obligations.lean` 当前使用显式 `sorry` 提供占位证明；
在不改变公开接口的情况下，以具体证明替换这些占位即可补齐框架。

依赖方向：定义 → contracts → 实现证明 → correctness。
实现证明不能反向导入 Correctness，也不能仅为让证明通过而修改 specification。
细化内部 invariant 后，需要重新证明初始化和 preservation。
-/

/-- 初始化 contract：每个良构输入都初始化成功；提前返回 UNSAT 必须是真的不可满足，
否则实际产生的初始机器必须满足 invariant。 -/
def InitializationCorrect : Prop := ∀ formula,
  WellFormed formula → ∀ config : CDCL.Config,
    ∃ initialized, CDCL.initState formula config = .ok initialized ∧
      match initialized with
      | none => Std.Sat.CNF.Unsat (formulaView formula)
      | some s => Inv formula (InitialMachine s)

/-- 继续运行时的后置条件：建立输出的 representation、控制和进展事实，并对应一段逻辑执行。
此处不直接假定输出语义正确；`Correctness` 通过 `LogicalExecution` 推出该结论。 -/
def RunningPost (formula : Formula) (before : LogicalState) (after : CDCL.Machine) : Prop :=
  ∃ next witness,
    Rep after next witness ∧ next.numVars = max 1 formula.numVars ∧
    LogicalExecution (formulaView formula) before next ∧
    ControlInv (formulaView formula) after next witness ∧ ProgressInv next

/-- 结束 step 的后置条件：必须通过逻辑执行导出 SAT/UNSAT 终态条件，
不能直接假定返回结果已满足最终 `ValidResult`。 -/
def FinishedPost (formula : Formula) (before : LogicalState) (result : CDCL.SolveResult) : Prop :=
  ∃ next, LogicalExecution (formulaView formula) before next ∧ Terminal formula next result

/-- 指定执行阶段的 contract：输入完整证书成立时，真实 `step` 满足对应的运行或结束后置条件。 -/
def PhaseCorrect (phase : CDCL.Phase) : Prop :=
  ∀ formula machine state witness,
    Certificate formula machine state witness → machine.phase = phase →
      match CDCL.step machine with
      | .running after => RunningPost formula state after
      | .finished result => FinishedPost formula state result

/-- 最终组合所需的全部证明前提，包括纯逻辑规则、初始化、四个阶段和 variant 下降。
不假设成功的执行预算或正确性 oracle。各阶段按实际涉及的操作承担分配、规范化、watch 扫描、
分析与最小化、历史恢复、restart 和 reduction 的证明责任。 -/
structure ImplementationFacts : Prop where
  /-- 每种逻辑操作保持语义 invariant 的证明。 -/
  logicalMoves : LogicalSoundness
  /-- 逻辑 SAT/UNSAT 终态条件推出最终 specification 的证明。 -/
  terminal : TerminalSoundness
  /-- 真实初始化满足输入及初始 invariant contract 的证明。 -/
  initialization : InitializationCorrect
  /-- 开始 propagation 阶段满足其 contract 的证明。 -/
  beginPropagation : PhaseCorrect .beginPropagation
  /-- 选择下一个传播文字阶段满足其 contract 的证明。 -/
  nextLiteral : PhaseCorrect .nextLiteral
  /-- watch 扫描及其传播、冲突处理满足 contract 的证明。 -/
  watch : PhaseCorrect .watch
  /-- restart、reduction、decision 或 SAT 结束分支满足 contract 的证明。 -/
  choose : PhaseCorrect .choose
  /-- 每个继续运行的真实 step 都严格降低终止 variant 的证明。 -/
  decreases : StepDecreases

/-- 统一描述执行结果：继续运行时 invariant 成立；结束时结果满足 `ValidResult`。 -/
def InvariantProgress (formula : Formula) : CDCL.Progress → Prop
  | .running machine => Inv formula machine
  | .finished result => ValidResult formula result

/-- 根据机器当前阶段，选择对应的阶段 contract，得到真实单步执行的后置条件。 -/
theorem phase_correct (facts : ImplementationFacts) {formula : Formula}
    {machine : CDCL.Machine} {state : LogicalState} {witness : RepresentationWitness}
    (certificate : Certificate formula machine state witness) :
    match CDCL.step machine with
    | .running after => RunningPost formula state after
    | .finished result => FinishedPost formula state result := by
  cases phase : machine.phase with
  | beginPropagation => exact facts.beginPropagation _ _ _ _ certificate phase
  | nextLiteral => exact facts.nextLiteral _ _ _ _ certificate phase
  | watch => exact facts.watch _ _ _ _ certificate phase
  | choose => exact facts.choose _ _ _ _ certificate phase

end MicrosatLean.Verification
