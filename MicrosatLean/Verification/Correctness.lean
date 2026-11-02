import MicrosatLean.Verification.Implementation.Obligations

namespace MicrosatLean.Verification

/-!
本文件的组合证明不使用 `sorry`；名称以 `_with` 结尾的定理显式声明证明依赖。
最终入口使用八项尚未证明的实现 obligations，因此整体仍是验证框架，尚未完成求解器验证。
原生 CLI 继续使用现有的独立 IO 驱动。
-/

/-- 给定实现层的全部证明，一个真实 step 保持 invariant，或返回满足 specification 的结果。 -/
theorem step_correct_with (facts : ImplementationFacts) {formula : Formula}
    {machine : CDCL.Machine} (valid : Inv formula machine) :
    InvariantProgress formula (CDCL.step machine) := by
  obtain ⟨state, witness, certificate⟩ := valid
  have outcome := phase_correct facts certificate
  cases transition : CDCL.step machine with
  | running after =>
    obtain ⟨next, nextWitness, represented, variables, execution, control, progress⟩ :=
      (show RunningPost formula state after from by simpa only [transition] using outcome)
    exact ⟨next, nextWitness, certificate.input, variables, represented,
      execution_preserves facts.logicalMoves certificate.semantic execution, control, progress⟩
  | finished result =>
    obtain ⟨next, execution, terminal⟩ :=
      (show FinishedPost formula state result from by simpa only [transition] using outcome)
    exact facts.terminal formula next result
      (execution_preserves facts.logicalMoves certificate.semantic execution) terminal

/-- 从单步正确性提取 invariant preservation：真实 step 继续运行时，后继机器仍满足 invariant。 -/
theorem step_running_with (facts : ImplementationFacts) {formula : Formula}
    {before after : CDCL.Machine} (valid : Inv formula before)
    (transition : CDCL.step before = .running after) : Inv formula after := by
  simpa only [transition, InvariantProgress] using step_correct_with facts valid

/-- 对 fuel 归纳，将单步正确性推广到任意有限批次的真实 `runFor` 执行。 -/
theorem runFor_correct_with (facts : ImplementationFacts) {formula : Formula}
    (fuel : Nat) {machine : CDCL.Machine} (valid : Inv formula machine) :
    InvariantProgress formula (CDCL.runFor fuel machine) := by
  induction fuel generalizing machine with
  | zero => exact valid
  | succ fuel ih =>
    have safe := step_correct_with facts valid
    cases transition : CDCL.step machine with
    | running next =>
      have nextValid : Inv formula next := by
        simpa only [transition, InvariantProgress] using safe
      simpa only [CDCL.runFor, transition] using ih nextValid
    | finished result =>
      simpa only [CDCL.runFor, transition, InvariantProgress] using safe

/-- 完整执行结论：结果满足 `ValidResult`，且存在有限 fuel，使真实 `runFor` 返回同一结果。 -/
def TotalRunSpec (formula : Formula) (machine : CDCL.Machine) (result : CDCL.SolveResult) : Prop :=
  ValidResult formula result ∧ ∃ fuel, CDCL.runFor fuel machine = .finished result

/-- 将当前机器、当前 invariant 证明和实现层证明前提一起传入递归。
这些证明与逻辑 invariant 分开，使每次递归都可使用 termination 依据；只有机器提供运行时数据。 -/
private structure ExecutionState (formula : Formula) where
  /-- 递归执行的实际机器状态。 -/
  machine : CDCL.Machine
  /-- 当前机器满足 invariant 的证明。 -/
  valid : Inv formula machine
  /-- 每次递归可用的实现层证明，用于单步正确性和终止下降。 -/
  facts : ImplementationFacts

/-- 仅调用真实 `step` 的递归执行器，返回结果及其正确性和有限执行见证。
证书和 variant 在 `Prop` 中论证递归合法，编译时会擦除；终止结论仍依赖传入的实现层证明。 -/
private def runCertified (formula : Formula) (state : ExecutionState formula) :
    { result : CDCL.SolveResult // TotalRunSpec formula state.machine result } :=
  match transition : CDCL.step state.machine with
  | .finished result =>
    ⟨result, by
      have safe := step_correct_with state.facts state.valid
      exact ⟨by simpa only [transition, InvariantProgress] using safe,
        ⟨1, by simp only [CDCL.runFor, transition]⟩⟩⟩
  | .running after =>
    let afterValid := step_running_with state.facts state.valid transition
    let result := runCertified formula ⟨after, afterValid, state.facts⟩
    ⟨result.val, by
      obtain ⟨correct, fuel, finished⟩ := result.property
      exact ⟨correct, ⟨fuel + 1, by simpa only [CDCL.runFor, transition] using finished⟩⟩⟩
termination_by variant (max 1 formula.numVars) state.machine
decreasing_by
  exact state.facts.decreases formula state.machine after state.valid afterValid transition

/-- 将显式的实现层证明和 invariant 包装成执行状态，调用带证书的执行器。 -/
def runCertifiedWith (facts : ImplementationFacts) (formula : Formula)
    (machine : CDCL.Machine) (valid : Inv formula machine) :
    { result : CDCL.SolveResult // TotalRunSpec formula machine result } :=
  runCertified formula ⟨machine, valid, facts⟩

/-- 给定实现层证明，良构输入初始化得到的搜索在有限步后结束，且结果正确。 -/
theorem initialized_search_correct_with (facts : ImplementationFacts) {formula : Formula}
    (valid : WellFormed formula) {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    ∃ fuel result, CDCL.runFor fuel (InitialMachine s) = .finished result ∧ ValidResult formula result := by
  obtain ⟨outcome, actual, checked⟩ := facts.initialization formula valid config
  have same : outcome = some s := Except.ok.inj (actual.symm.trans initialized)
  subst outcome
  obtain ⟨result, correct, fuel, finished⟩ := runCertifiedWith facts formula (InitialMachine s) checked
  exact ⟨fuel, result, finished, correct⟩

/-- 根据初始化 contract，良构输入不可能进入 `initState` 的错误分支。 -/
theorem initialization_no_error_with (facts : ImplementationFacts) {formula : Formula}
    (valid : WellFormed formula) (config : CDCL.Config) (message : String)
    (failed : CDCL.initState formula config = .error message) : False := by
  obtain ⟨outcome, initialized, _⟩ := facts.initialization formula valid config
  rw [failed] at initialized
  cases initialized

/-- 针对已有良构性证明的输入求解：初始化后处理提前 UNSAT，或调用有终止依据的执行器。 -/
def solveWellFormedWith (facts : ImplementationFacts) (formula : Formula)
    (valid : WellFormed formula) (config : CDCL.Config := {}) : CDCL.SolveResult :=
  match initialized : CDCL.initState formula config with
  | .error message => False.elim (initialization_no_error_with facts valid config message initialized)
  | .ok none => .unsat {}
  | .ok (some s) =>
    have initial : Inv formula (InitialMachine s) := by
      obtain ⟨outcome, actual, checked⟩ := facts.initialization formula valid config
      have same : outcome = some s := Except.ok.inj (actual.symm.trans initialized)
      simpa only [same] using checked
    (runCertifiedWith facts formula (InitialMachine s) initial).val

/-- 先判定输入范围，再调用良构输入求解器；实现层证明作为显式参数传入。 -/
def solveWith (facts : ImplementationFacts) (formula : Formula) (config : CDCL.Config := {}) :
    Except String CDCL.SolveResult :=
  if valid : WellFormed formula then .ok (solveWellFormedWith facts formula valid config)
  else .error "literal outside the declared variable bounds"

/-- 组合初始化 contract 与执行器结论，证明良构输入求解器返回有效结果。 -/
theorem solveWellFormed_correct_with (facts : ImplementationFacts) (formula : Formula)
    (valid : WellFormed formula) (config : CDCL.Config := {}) :
    ValidResult formula (solveWellFormedWith facts formula valid config) := by
  unfold solveWellFormedWith
  split
  · rename_i message failed
    exact False.elim (initialization_no_error_with facts valid config message failed)
  · rename_i initialized
    obtain ⟨outcome, actual, checked⟩ := facts.initialization formula valid config
    have same : outcome = none := Except.ok.inj (actual.symm.trans initialized)
    simpa only [same, ValidResult] using checked
  · exact (runCertifiedWith facts _ _ _).property.1

/-- 给定实现层证明，公开形式的求解入口对每个良构输入都会成功返回，并满足最终 specification。 -/
theorem solve_correct_with (facts : ImplementationFacts) (formula : Formula)
    (valid : WellFormed formula) (config : CDCL.Config := {}) :
    ∃ result, solveWith facts formula config = .ok result ∧ ValidResult formula result :=
  ⟨solveWellFormedWith facts formula valid config,
    by simp only [solveWith, dite_eq_left valid],
    solveWellFormed_correct_with facts formula valid config⟩

/-- 依赖尚以 `sorry` 占位的实现证明的实验入口。
它没有替换 `CDCL.solve`，也没有接入生产 CLI。 -/
def solveScaffold (formula : Formula) (config : CDCL.Config := {}) : Except String CDCL.SolveResult :=
  solveWith Implementation.actualFacts formula config

/-- 将通用正确性定理实例化到当前验证框架；因实现 obligations 尚未证明，此结论仍依赖 `sorryAx`。 -/
theorem solveScaffold_correct (formula : Formula) (valid : WellFormed formula)
    (config : CDCL.Config := {}) :
    ∃ result, solveScaffold formula config = .ok result ∧ ValidResult formula result :=
  solve_correct_with Implementation.actualFacts formula valid config

/-- 将有限步终止及结果正确性实例化到当前实现；此结论仍依赖未完成的实现 obligations。 -/
theorem initialized_search_terminates {formula : Formula} (valid : WellFormed formula)
    {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    ∃ fuel result, CDCL.runFor fuel (InitialMachine s) = .finished result ∧ ValidResult formula result :=
  initialized_search_correct_with Implementation.actualFacts valid initialized

end MicrosatLean.Verification
