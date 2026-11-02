import MicrosatLean.Verification.Implementation.Logic.Moves
import MicrosatLean.Verification.Implementation.Search.Begin
import MicrosatLean.Verification.Implementation.Search.Next
import MicrosatLean.Verification.Implementation.Search.Concrete.MachineWatch
import MicrosatLean.Verification.Implementation.Search.Concrete.MachineChoice
import MicrosatLean.Verification.Implementation.Bridge.FromConcrete
import MicrosatLean.Verification.Implementation.Bridge.Progress

/-! 执行循环需要的三个事实：成功初始化建立 invariant、running step 保持 invariant、递归调用的 rank 严格下降。
本模块复用已有实现证明，不导入最终 Correctness 或已完成的 ImplementationFacts 证明包。
watch 与 choose 复用具体状态 preservation；它们的逻辑 execution traces 和终止 gates 留给后续 correctness composition。
这里没有把返回的 SAT/UNSAT 结果有效性作为假设。
-/

namespace MicrosatLean.Verification

/-- 真实 initState 成功返回 state 时，为它建立 runner 要求的完整逻辑 Inv。 -/
theorem initial_invariant {formula : Formula} (valid : WellFormed formula)
    {config : CDCL.Config} {s : CDCL.State}
    (initialized : CDCL.initState formula config = .ok (some s)) :
    Inv formula (InitialMachine s) :=
  Implementation.Bridge.of_concrete valid
    (Implementation.Search.Concrete.initState_some_machineInvariant valid initialized)
    (Implementation.Initialization.initState_some_variables valid initialized)

/-- 实际 step 返回 running after 时，after 继续满足 Inv，因而可以成为下一次递归调用的输入。
begin/next 使用逻辑 refinement；watch/choose 复用具体 preservation，再恢复成同一套逻辑 invariant。
-/
theorem step_preserves {formula : Formula} {before after : CDCL.Machine}
    (valid : Inv formula before) (transition : CDCL.step before = .running after) :
    Inv formula after := by
  obtain ⟨state, witness, certificate⟩ := valid
  have refinePhase {phase : CDCL.Phase} (correct : PhaseCorrect phase)
      (same : before.phase = phase) : Inv formula after := by
    have post : RunningPost formula state after := by
      simpa only [transition] using correct formula before state witness certificate same
    exact post.invariant Implementation.Logic.logical_moves certificate
  have recover (concrete : Implementation.Search.Concrete.MachineInvariant formula after) :
      Inv formula after :=
    Implementation.Bridge.of_concrete certificate.input concrete
      ((Implementation.Search.Concrete.step_nVars transition).trans
        (certificate.representation.variables.symm.trans certificate.variables))
  cases phase : before.phase with
  | beginPropagation => exact refinePhase Implementation.Search.begin_propagation phase
  | nextLiteral => exact refinePhase Implementation.Search.next_literal phase
  | watch =>
    apply recover
    simpa only [transition, Implementation.Search.Concrete.InvariantProgress] using
      Implementation.Search.Concrete.step_watch_invariant
        (Implementation.Bridge.concrete_of_certificate certificate) phase
  | choose =>
    apply recover
    simpa only [transition, Implementation.Search.Concrete.InvariantProgress] using
      Implementation.Search.Concrete.step_choose_invariant
        (Implementation.Bridge.concrete_of_certificate certificate) phase

/-- 结合 running preservation 与具体 rank 证明，得到每次递归调用的共享 variant 严格下降。 -/
theorem step_decreases {formula : Formula} {before after : CDCL.Machine}
    (valid : Inv formula before) (transition : CDCL.step before = .running after) :
    RankLT (variant (max 1 formula.numVars) after) (variant (max 1 formula.numVars) before) :=
  Implementation.Bridge.concrete_decreases formula before after valid
    (step_preserves valid transition) transition

end MicrosatLean.Verification
