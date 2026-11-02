import MicrosatLean.CDCL.Analysis

/-! 可恢复的 CDCL 状态机。step 将一次搜索推进分成四个 phase，runFor 执行有限步。
watch 扫描可在一次 step 中批量处理多个子句，但仍受 arena 长度限制。
无界执行循环位于 CDCL/Runner；本模块不依赖 verification。
-/

namespace MicrosatLean.CDCL

/-- 完成搜索的结果：SAT 携带 saved model 与统计，UNSAT 携带统计。 -/
inductive SolveResult where
  /-- SAT：给出有限 model 数组与最终统计。 -/
  | sat (model : Array Bool) (stats : Stats)
  /-- UNSAT：给出最终统计。 -/
  | unsat (stats : Stats)
  deriving Repr, Inhabited

/-- 外层搜索的四个控制阶段，使无界搜索可以表示为一系列 total transitions。 -/
inductive Phase where
  /-- 建立本次 propagation invocation 的 root 模式并保存 learned 计数。 -/
  | beginPropagation
  /-- 取出下一个待传播假 literal，或进入 choice。 -/
  | nextLiteral
  /-- 从保存的 cursor 继续扫描当前 literal 的 watch list。 -/
  | watch
  /-- 按需 restart/reduce，然后作 decision 或返回 SAT。 -/
  | choose
  deriving Repr, Inhabited

/-- 在 solver state 之外保存可恢复的搜索控制信息与 watch cursor。
previousWatch = 0 表示当前链表头，否则表示已访问前缀末端的 reference。
root 在一次 propagation invocation 中跨冲突保留；分析得到 unit learned clause 时设为 true。
-/
structure Machine where
  /-- 当前具体 solver state。 -/
  solver : State
  /-- MTF decision scan 的当前位置。 -/
  decision : Nat
  /-- 下一次 step 要执行的控制阶段。 -/
  phase : Phase := .beginPropagation
  /-- 本次 propagation 开始时的 learned 计数，用于识别新学习事件。 -/
  oldLemmas : Nat := 0
  /-- 本次 propagation invocation 的 root 模式。 -/
  root : Bool := false
  /-- watch 阶段正在传播的假 literal。 -/
  currentLit : Lit := 0
  /-- 当前 watch cursor 前的 reference；0 表示链头。 -/
  previousWatch : Nat := 0
  deriving Repr, Inhabited

/-- 从初始化后的 solver state 建立初始 machine：decision cursor 指向 MTF head，其余控制字段用默认值。 -/
def Machine.initial (s : State) : Machine := { solver := s, decision := s.head }

/-- 有限执行的返回状态：继续运行的 Machine，或已经完成的 SolveResult。 -/
inductive Progress where
  /-- 预算尚未得到最终结果，保存可恢复的 machine。 -/
  | running (machine : Machine)
  /-- 真实搜索已经完成。 -/
  | finished (result : SolveResult)
  deriving Repr, Inhabited

/-- 从 pos 开始按源顺序找第一个未置假的 replacement literal，遇到零终止符停止。
fuel 由剩余 arena 长度提供；结构递归避免为每个 clause 构造额外 range 和 early-return 累加器。
-/
def replacementScan : Nat → Array Nat → Array Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, arena, marks, pos =>
    let lit := arena[pos]!
    if lit == 0 then none
    else if marks[lit]! == 0 then some pos
    else replacementScan fuel arena marks (pos + 1)

/-- 跳过 clause 的两个 watched literals，在其剩余后缀中寻找 replacement。 -/
def replacement (arena marks : Array Nat) (clauseId : Nat) : Option Nat :=
  replacementScan (arena.size - (clauseId + 2)) arena marks (clauseId + 2)

/-- 沿 MTF 的 previous 链跳过已赋值变量；0 表示链已结束或有限遍历预算已耗尽。 -/
def nextDecisionScan : Nat → State → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, s, cursor =>
    if cursor == 0 then 0
    else if s.mark (2 * cursor) == 0 && s.mark (2 * cursor + 1) == 0 then cursor
    else nextDecisionScan fuel s s.previous[cursor]!

/-- 从 cursor 寻找下一个未赋值变量；MTF 链的无环与覆盖性质保证 nVars + 1 的预算足够。 -/
def nextDecision (s : State) (cursor : Nat) : Nat :=
  nextDecisionScan (s.nVars + 1) s cursor

/-- 把 watch 扫描临时取出的 arena 与 first 数组重新装回完整 state。 -/
@[inline] def restoreWatchArrays (s : State) (arena first : Array Nat) : State :=
  { s with arena := arena, first := first }

/-- 按参考求解器的顺序扫描一个假 literal 的 watch list。
arena 与 first 暂时脱离 s，避免每访问一个 clause 就重建所有状态字段；在赋值、分析或返回前重新装回。
representation invariant 对应 restoreWatchArrays s arena first，其他 state 字段在纯扫描期间保持不变。
replacement 不会是当前假 literal，因此移动 watch 不会扩充正在扫描的链。
预算耗尽返回可恢复的 cursor；传播可产生 unit assignment、真正的 root 冲突或 learned asserting clause。
-/
def propagateWatches : Nat → State → Array Nat → Array Nat → Nat → Nat → Bool → Lit → Nat → Progress
  | 0, s, arena, first, decision, oldLemmas, root, lit, previous =>
    .running ⟨restoreWatchArrays s arena first, decision, .watch, oldLemmas, root, lit, previous⟩
  | fuel + 1, s, arena, first, decision, oldLemmas, root, lit, previous => Id.run do
    let ref := if previous == 0 then first[lit]! else arena[watchLinkPos previous]!
    if ref == 0 then
      return .running ⟨restoreWatchArrays s arena first, decision, .nextLiteral, oldLemmas, root, 0, 0⟩
    let clauseId := watchClause ref

    -- 先把另一个 watch 放在首位，再保持参考实现的 replacement 扫描与交换顺序。
    let arena := if arena[clauseId]! == lit then
        arena.set! clauseId arena[clauseId + 1]!
      else arena
    match replacement arena s.marks clauseId with
    | some pos =>
      let newLit := arena[pos]!
      let arena := (arena.set! (clauseId + 1) newLit).set! pos lit
      let nextRef := arena[watchLinkPos ref]!
      let (arena, first) := if previous == 0 then
          (arena, first.set! lit nextRef)
        else
          (arena.set! (watchLinkPos previous) nextRef, first)
      let arena := arena.set! (watchLinkPos ref) first[newLit]!
      let first := first.set! newLit ref
      return propagateWatches fuel s arena first decision oldLemmas root lit previous
    | none =>
      let arena := arena.set! (clauseId + 1) lit
      let other : Lit := arena[clauseId]!
      if s.mark other.negate != 0 then
        return propagateWatches fuel s arena first decision oldLemmas root lit ref
      let s := restoreWatchArrays s arena first
      if s.mark other == 0 then
        let s := s.assign clauseId root
        return .running ⟨s, decision, .watch, oldLemmas, root, lit, ref⟩
      if root then return .finished (.unsat s.stats)
      let (s, learned) := analyze s clauseId
      let root := s.db (learned + 1) == 0
      let s := s.assign learned root
      return .running ⟨s, decision, .nextLiteral, oldLemmas, root, 0, 0⟩

/-- 执行一次真实 CDCL transition：开始传播、取待传播 literal、扫描 watches，或执行 choice。
watch 阶段可批量访问多个 clauses，直到 unit、冲突、链尾或有限界；其他内部扫描也都有有限界。
choice 阶段按原启发式执行 restart/reduction，再作新 decision 或返回完整 SAT model。
-/
def step (machine : Machine) : Progress := Id.run do
  let ⟨s, decision, phase, oldLemmas, root, lit, previous⟩ := machine
  match phase with
  | .beginPropagation =>
    let root := s.processed < s.assigned && s.reason s.trail[s.processed]! != 0
    return .running ⟨s, decision, .nextLiteral, s.nLemmas, root, 0, 0⟩
  | .nextLiteral =>
    if s.processed < s.assigned then
      let lit := s.trail[s.processed]!
      let s := { s with processed := s.processed + 1 }
      return .running ⟨s, decision, .watch, oldLemmas, root, lit, 0⟩
    let s := if root then { s with forced := s.processed } else s
    return .running ⟨s, decision, .choose, oldLemmas, root, 0, 0⟩
  | .watch =>
    let arena := s.arena
    let first := s.first
    let s := { s with arena := #[], first := #[] }
    return propagateWatches arena.size s arena first decision oldLemmas root lit previous
  | .choose =>
    let mut s := s
    let mut decision := decision
    if s.nLemmas > oldLemmas then
      decision := s.head
      let threshold := (s.slow / 100) * 125
      if s.fast > threshold then
        s := ({ s with res := 0, fast := threshold }).restart
        if s.nLemmas > s.maxLemmas then
          s := s.reduceDB s.config.reductionK
    decision := nextDecision s decision
    if decision == 0 then
      return .finished (.sat s.phases s.stats)
    s := s.decide decision
    return .running ⟨s, decision, .beginPropagation, 0, false, 0, 0⟩

/-- 最多执行 fuel 次 step；预算用尽时返回可继续的 Machine。
只有实际搜索终止才返回 SAT/UNSAT；watch 的内部预算与这里的外层 step 预算分开。
-/
def runFor : Nat → Machine → Progress
  | 0, machine => .running machine
  | fuel + 1, machine =>
    match step machine with
    | .finished result => .finished result
    | .running next => runFor fuel next

end MicrosatLean.CDCL
