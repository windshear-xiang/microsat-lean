import MicrosatLean.Verification.Transitions
import MicrosatLean.Verification.Progress

/-! 实现层必须证明的 contracts；这些是 Prop 定义，不是新增 axiom。
Implementation/Obligations 汇总具体证明，最终 correctness composition 显式使用这组 obligations。
执行用的 runner 只经 Termination 获取初始化、preservation 与 decrease 证明。
依赖顺序为定义 → contracts → 实现证明 → correctness；调整 invariant 后必须重新证明初始化与 preservation。
-/

namespace MicrosatLean.Verification

/-- 任意合法输入和 Config 都能成功初始化：提前返回 none 时输入确实 UNSAT；
返回某个 state 时，与该 state 精确对应的 CDCL.Machine.initial 满足 Inv。
-/
def InitializationCorrect : Prop := ∀ formula,
  WellFormed formula → ∀ config : CDCL.Config,
    ∃ initialized, CDCL.initState formula config = .ok initialized ∧
      match initialized with
      | none => Std.Sat.CNF.Unsat (formulaView formula)
      | some s => Inv formula (CDCL.Machine.initial s)

/-- running 分支必须给出真实逻辑 execution 以及输出的 representation、control 和 progress 事实。
SemanticInv 不直接作为输出前提，而由逻辑 preservation 推导。
-/
def RunningPost (formula : Formula) (before : LogicalState) (after : CDCL.Machine) : Prop :=
  ∃ next witness,
    Rep after next witness ∧ next.numVars = max 1 formula.numVars ∧
    LogicalExecution (formulaView formula) before next ∧
    ControlInv (formulaView formula) after next witness ∧ ProgressInv next

/-- 把 running refinement 与逻辑 soundness 组合成完整 Inv；termination 和最终 correctness 共用这一组合。 -/
theorem RunningPost.invariant {formula : Formula} {before after : CDCL.Machine}
    {state : LogicalState} {witness : RepresentationWitness}
    (sound : LogicalSoundness) (certificate : Certificate formula before state witness)
    (post : RunningPost formula state after) : Inv formula after := by
  obtain ⟨next, nextWitness, represented, variables, execution, control, progress⟩ := post
  exact ⟨next, nextWitness, certificate.input, variables, represented,
    execution_preserves sound certificate.semantic execution, control, progress⟩

/-- finished 分支必须给出到终止逻辑状态的 execution 和 Terminal gate，不能直接假定 ValidResult。 -/
def FinishedPost (formula : Formula) (before : LogicalState) (result : CDCL.SolveResult) : Prop :=
  ∃ next, LogicalExecution (formulaView formula) before next ∧ Terminal formula next result

/-- 指定 phase 上实际 CDCL.step 的 contract：从 Certificate 出发，按真实返回值建立 running 或 finished 后置条件。 -/
def PhaseCorrect (phase : CDCL.Phase) : Prop :=
  ∀ formula machine state witness,
    Certificate formula machine state witness → machine.phase = phase →
      match CDCL.step machine with
      | .running after => RunningPost formula state after
      | .finished result => FinishedPost formula state result

/-- 最终 composition 显式使用的八个证明义务。
四个 phase contracts 配合初始化和 rank 证明，覆盖 normalization、watch 扫描、analysis/minimization、history、restart 与 reduction。
没有额外假定可成功的执行预算或正确性 oracle。
-/
structure ImplementationFacts : Prop where
  /-- 所有逻辑迁移保持 SemanticInv。 -/
  logicalMoves : LogicalSoundness
  /-- 终止 gate 与 SemanticInv 推出 ValidResult。 -/
  terminal : TerminalSoundness
  /-- 真实初始化的成功性与结果正确性。 -/
  initialization : InitializationCorrect
  /-- 开始 propagation 的真实 phase refinement。 -/
  beginPropagation : PhaseCorrect .beginPropagation
  /-- 取待传播 literal 或完成 propagation 的真实 phase refinement。 -/
  nextLiteral : PhaseCorrect .nextLiteral
  /-- watch 扫描、unit/conflict 和 analysis 的真实 phase refinement。 -/
  watch : PhaseCorrect .watch
  /-- restart/reduction、decision 或 SAT 返回的真实 phase refinement。 -/
  choose : PhaseCorrect .choose
  /-- 真实 running transitions 使 variant 严格下降。 -/
  decreases : StepDecreases

/-- 统一解释运行结果：running 时要求 Inv，finished 时要求 ValidResult。 -/
def InvariantProgress (formula : Formula) : CDCL.Progress → Prop
  | .running machine => Inv formula machine
  | .finished result => ValidResult formula result

/-- 按当前 Machine.phase 选择对应的已证明 phase contract。 -/
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
