import MicrosatLean.CDCL.Analysis

/-!
分阶段 CDCL 搜索：显式保留传播游标，将实际搜索拆分为全函数 `step`，并提供有界 `runFor` 入口。
-/

namespace MicrosatLean.CDCL

/-- 已完成搜索的结果；SAT 分支包含保存的完整赋值数组和执行统计。 -/
inductive SolveResult where
  /-- 找到满足输入的模型，并附带执行统计。 -/
  | sat (model : Array Bool) (stats : Stats)
  /-- 判定输入不可满足，并附带执行统计。 -/
  | unsat (stats : Stats)
  deriving Repr, Inhabited

/-- 将持续搜索拆分为一系列全函数 transition 的执行阶段。
watch 阶段处理一个文字的有界 watch 扫描；冲突分析也由 trail 长度限制。 -/
inductive Phase where
  /-- 开始一轮 propagation，记录学习子句数并确定 root 模式。 -/
  | beginPropagation
  /-- 取出下一个待传播假文字，或在传播完成后进入 choose。 -/
  | nextLiteral
  /-- 扫描当前假文字的 watch 链表，处理替代 watch、unit 或冲突。 -/
  | watch
  /-- 按需 restart 和 reduction，然后选择新 decision 或返回 SAT。 -/
  | choose
  deriving Repr, Inhabited

/-- 求解器状态以及恢复分阶段执行所需的控制信息。
`previousWatch = 0` 表示位于当前链表头，否则从该引用的下一链接继续。
`root` 在一次 propagation 及其冲突处理中保持，分析得到 unit 子句时转为 true。 -/
structure Machine where
  /-- 具体子句数据库、赋值、启发式信息及统计。 -/
  solver : State
  /-- 当前 MTF decision 搜索游标。 -/
  decision : Nat
  /-- 下一步要执行的阶段。 -/
  phase : Phase := .beginPropagation
  /-- 本轮 propagation 开始时的学习子句数量，用于检测本轮是否发生 learning。 -/
  oldLemmas : Nat := 0
  /-- 当前 propagation 是否处于 root 模式。 -/
  root : Bool := false
  /-- watch 阶段正在处理的假文字，其他阶段通常为 0。 -/
  currentLit : Lit := 0
  /-- 当前 watch 链表中最近访问的引用；0 表示从链表头继续。 -/
  previousWatch : Nat := 0
  deriving Repr, Inhabited

/-- 一次 transition 或一批执行的结果：可恢复的机器，或已经完成的求解结果。 -/
inductive Progress where
  /-- 搜索尚未结束，保存可继续执行的完整机器。 -/
  | running (machine : Machine)
  /-- 搜索已经完成，携带 SAT 或 UNSAT 结果。 -/
  | finished (result : SolveResult)
  deriving Repr, Inhabited

/-- 按源实现顺序寻找首个未被标为假的候选文字；调用者从两个 watch 之后开始扫描。
结构递归避免每访问一个子句就分配 range 和提前返回累加器；扫描上界是剩余 arena 长度。 -/
def replacementScan : Nat → Array Nat → Array Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, arena, marks, pos =>
    let lit := arena[pos]!
    if lit == 0 then none
    else if marks[lit]! == 0 then some pos
    else replacementScan fuel arena marks (pos + 1)

/-- 跳过子句的两个 watch，在剩余文字中寻找替代 watch；没有候选项时返回 `none`。 -/
def replacement (arena marks : Array Nat) (clauseId : Nat) : Option Nat :=
  replacementScan (arena.size - (clauseId + 2)) arena marks (clauseId + 2)

/-- 沿 MTF（move-to-front）链表跳过已赋值变量，寻找下一个 decision 变量。
链表结束或遍历预算耗尽时均返回 0。 -/
def nextDecisionScan : Nat → State → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, s, cursor =>
    if cursor == 0 then 0
    else if s.mark (2 * cursor) == 0 && s.mark (2 * cursor + 1) == 0 then cursor
    else nextDecisionScan fuel s s.previous[cursor]!

/-- 使用 `nVars + 1` 的预算寻找 decision 变量；预算充分性由 MTF 链表无环且覆盖变量来保证。 -/
def nextDecision (s : State) (cursor : Nat) : Nat :=
  nextDecisionScan (s.nVars + 1) s cursor

/-- 把 propagation 循环临时持有的 arena 和 watch 头数组装回状态。 -/
@[inline] def restoreWatchArrays (s : State) (arena first : Array Nat) : State :=
  { s with arena := arena, first := first }

/-- 按参考求解器的顺序遍历一个假文字的 watch 链表。
将 arena 和 watch 头数组从 `s` 中临时取出，避免访问每个子句时重建所有状态字段。
在赋值、分析和返回之前恢复完整状态；扫描期间其他字段不变。
representation invariant 描述的是 `restoreWatchArrays s arena first`，而非临时缺少数组的状态。

初始 arena 长度足以限制无环 watch 链表。替代文字不可能是当前假文字，
因此移动 watch 不会向正在扫描的链表添加条目。预算耗尽时仍返回可恢复游标，不声称 SAT/UNSAT。 -/
def propagateWatches : Nat → State → Array Nat → Array Nat → Nat → Nat → Bool → Lit → Nat → Progress
  | 0, s, arena, first, decision, oldLemmas, root, lit, previous =>
    .running ⟨restoreWatchArrays s arena first, decision, .watch, oldLemmas, root, lit, previous⟩
  | fuel + 1, s, arena, first, decision, oldLemmas, root, lit, previous => Id.run do
    let ref := if previous == 0 then first[lit]! else arena[watchLinkPos previous]!
    if ref == 0 then
      return .running ⟨restoreWatchArrays s arena first, decision, .nextLiteral, oldLemmas, root, 0, 0⟩
    let clauseId := watchClause ref
    -- 先将另一个 watch 放到首位，再保持与源实现相同的扫描和交换顺序。
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

/-- 执行一次 CDCL transition，将 watch 访问合并到遇到 unit、冲突、链尾或有限预算为止。
所有内部扫描都受有限数组长度限制；外层驱动负责持续执行。 -/
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

/-- 最多执行 `fuel` 次 transition；预算耗尽时返回可恢复机器，不判定 SAT/UNSAT。
这是会终止的 API，供 invariant 和 refinement 证明使用。
单次 watch transition 可以访问多个子句，并有独立的 arena 长度上界。 -/
def runFor : Nat → Machine → Progress
  | 0, machine => .running machine
  | fuel + 1, machine =>
    match step machine with
    | .finished result => .finished result
    | .running next => runFor fuel next

end MicrosatLean.CDCL
