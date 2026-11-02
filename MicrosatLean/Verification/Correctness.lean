import MicrosatLean.Solver
import MicrosatLean.Verification.Implementation.Obligations

/-! 执行定义位于 CDCL/Runner 与 Solver。本模块在这些定义之后证明有限 runFor 对应关系和结果有效性。
_with 定理显式接收实现 contracts；公开 correctness theorems 使用已经完成的 actualFacts。
证明链是 step correctness → 有限 runFor correctness → run_finishes → runner correctness → 公开 solver correctness。
-/

namespace MicrosatLean.Verification

/-- 将 phase contracts、逻辑 preservation 和 terminal soundness 组合为实际 step 的 correctness。
running 时保持 Inv，finished 时得到原始输入的 ValidResult。
-/
theorem step_correct_with (facts : ImplementationFacts) {formula : Formula}
    {machine : CDCL.Machine} (valid : Inv formula machine) :
    InvariantProgress formula (CDCL.step machine) := by
  obtain ⟨state, witness, certificate⟩ := valid
  have outcome := phase_correct facts certificate
  cases transition : CDCL.step machine with
  | running after =>
    exact RunningPost.invariant facts.logicalMoves certificate
      (show RunningPost formula state after from by simpa only [transition] using outcome)
  | finished result =>
    obtain ⟨next, execution, terminal⟩ :=
      (show FinishedPost formula state result from by simpa only [transition] using outcome)
    exact facts.terminal formula next result
      (execution_preserves facts.logicalMoves certificate.semantic execution) terminal

/-- 对 fuel 归纳，将一步 correctness 扩展到任意有界 runFor；预算用尽时仍保留可继续的 invariant。 -/
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

/-- 证明普通 total runner 的返回值来自某个有限 fuel 的真实 runFor 执行。
按与 runner 相同的 variant 递归建立对应关系，不在执行返回值中携带该 certificate。
-/
theorem run_finishes (formula : Formula) (machine : CDCL.Machine)
    (valid : Inv formula machine) :
    ∃ fuel, CDCL.runFor fuel machine = .finished (CDCL.run formula machine valid) := by
  rw [CDCL.run]
  split
  · rename_i result transition
    exact ⟨1, by simp only [CDCL.runFor, transition]⟩
  · rename_i after transition
    obtain ⟨fuel, finished⟩ := run_finishes formula after (step_preserves valid transition)
    exact ⟨fuel + 1, by simpa only [CDCL.runFor, transition] using finished⟩
termination_by variant (max 1 formula.numVars) machine
decreasing_by exact step_decreases valid (by assumption)

/-- 先用 run_finishes 找到有限执行，再用 runFor correctness 推出普通 runner 的返回结果满足 ValidResult。 -/
theorem run_correct {formula : Formula} {machine : CDCL.Machine}
    (valid : Inv formula machine) : ValidResult formula (CDCL.run formula machine valid) := by
  obtain ⟨fuel, finished⟩ := run_finishes formula machine valid
  have safe := runFor_correct_with Implementation.actualFacts fuel valid
  simpa only [finished, InvariantProgress] using safe

/-- 真实初始化成功后，存在有限 runFor 执行返回有效结果；显式 facts 用于有限执行的 correctness composition。 -/
theorem initialized_search_correct_with (facts : ImplementationFacts) {formula : Formula}
    (valid : WellFormed formula) {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    ∃ fuel result, CDCL.runFor fuel (InitialMachine s) = .finished result ∧ ValidResult formula result := by
  have initial := initial_invariant valid initialized
  obtain ⟨fuel, finished⟩ := run_finishes formula (InitialMachine s) initial
  have safe := runFor_correct_with facts fuel initial
  exact ⟨fuel, _, finished, by simpa only [finished, InvariantProgress] using safe⟩

/-- 保留旧 API 名称的 abbrev，直接指向公开纯求解器 solvePure，不增加执行层。 -/
abbrev solveCertified (formula : Formula) (config : CDCL.Config := {}) :=
  CDCL.solvePure formula config

/-- 任意合法 Formula 与 Config 上，公开纯求解器返回某个 .ok result，且 result 满足最终 specification。
分别处理初始化错误不可能、提前 UNSAT 和正常 runner 返回三种分支。
-/
theorem solveCertified_correct (formula : Formula) (valid : WellFormed formula)
    (config : CDCL.Config := {}) :
    ∃ result, solveCertified formula config = .ok result ∧ ValidResult formula result := by
  unfold solveCertified CDCL.solvePure
  simp only [dite_eq_left valid]
  split
  · rename_i message failed
    obtain ⟨outcome, initialized, _⟩ := Implementation.actualFacts.initialization formula valid config
    rw [failed] at initialized
    cases initialized
  · rename_i initialized
    obtain ⟨outcome, actual, checked⟩ := Implementation.actualFacts.initialization formula valid config
    have same : outcome = none := Except.ok.inj (actual.symm.trans initialized)
    exact ⟨.unsat {}, rfl, by simpa only [same, ValidResult] using checked⟩
  · exact ⟨_, rfl, run_correct _⟩

/-- 只要纯求解器实际返回 .ok result，该结果就有效；非法输入不会产生 .ok。 -/
theorem solveCertified_ok_valid {formula : Formula} {config : CDCL.Config}
    {result : CDCL.SolveResult} (returned : solveCertified formula config = .ok result) :
    ValidResult formula result := by
  by_cases valid : WellFormed formula
  · obtain ⟨actual, equal, correct⟩ := solveCertified_correct formula valid config
    cases Except.ok.inj (equal.symm.trans returned)
    exact correct
  · simp only [solveCertified, CDCL.solvePure, dite_eq_right valid] at returned
    cases returned

/-- 兼容最初 scaffold 的名称；同样直接指向 solvePure。 -/
abbrev solveScaffold (formula : Formula) (config : CDCL.Config := {}) :=
  CDCL.solvePure formula config

/-- 以旧 scaffold API 名称提供同一份完整 solver correctness theorem。 -/
theorem solveScaffold_correct (formula : Formula) (valid : WellFormed formula)
    (config : CDCL.Config := {}) :
    ∃ result, solveScaffold formula config = .ok result ∧ ValidResult formula result :=
  solveCertified_correct formula valid config

/-- 对任意合法输入的真实初始化成功状态，存在有限 step 数完成搜索，并返回符合 specification 的结果。 -/
theorem initialized_search_terminates {formula : Formula} (valid : WellFormed formula)
    {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    ∃ fuel result, CDCL.runFor fuel (InitialMachine s) = .finished result ∧ ValidResult formula result :=
  initialized_search_correct_with Implementation.actualFacts valid initialized

end MicrosatLean.Verification

namespace MicrosatLean.CDCL

/-- 把纯求解器 correctness 连接到公开 IO 包装：合法输入上 solve 等于返回有效 .ok result 的 pure IO。 -/
theorem solve_correct (formula : Formula) (valid : Verification.WellFormed formula)
    (config : Config := {}) :
    ∃ result, solve formula config = pure (.ok result) ∧ Verification.ValidResult formula result := by
  obtain ⟨result, returned, correct⟩ := Verification.solveCertified_correct formula valid config
  exact ⟨result, by simp only [solve, returned], correct⟩

end MicrosatLean.CDCL
