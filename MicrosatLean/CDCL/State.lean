import MicrosatLean.Formula

/-!
CDCL 的具体数据结构及基本操作：赋值、子句分配、watch 链接、restart、数据库压缩和输入初始化。
-/

namespace MicrosatLean.CDCL

/-- 求解器配置：控制初始学习子句容量阈值和数据库删减策略。 -/
structure Config where
  /-- 初始学习子句数量阈值；超过阈值后可在 restart 时触发 reduction。 -/
  initialLemmaLimit : Nat := 2000
  /-- reduction 使用的已保存 phase 满足数量阈值。 -/
  reductionK : Nat := 6
  deriving Repr, Inhabited

/-- 执行统计；用于观察求解过程，不参与 SAT/UNSAT 的逻辑语义。 -/
structure Stats where
  /-- 已分析的非 root 冲突次数。 -/
  conflicts : Nat := 0
  /-- decision 赋值次数。 -/
  decisions : Nat := 0
  /-- 通过 reason 子句作出的赋值次数，包括初始 unit。 -/
  propagations : Nat := 0
  /-- restart 次数。 -/
  restarts : Nat := 0
  /-- 数据库 reduction 次数。 -/
  reductions : Nat := 0
  /-- reduction 累计删除的学习子句数。 -/
  removedLearned : Nat := 0
  deriving Repr, Inhabited

/-- 与 `microsat.c` 中可变字段对应的显式求解器状态。

`arena` 以两个零单元开头。每个子句依次占用两个 watch 链接单元、文字序列和零结束标记；
子句 ID 是首个文字的位置。watch 引用编码为 `2 * clauseId + slot`，其中 slot 为 0 或 1。
交换被观察文字时，两个引用仍对应各自的链接单元。0 表示 watch 链表结束，不能作为子句 ID。

有效状态要求各数组覆盖声明的变量和文字，子句 ID 不越界，且
`forced ≤ processed ≤ assigned ≤ nVars`。活动 trail 保存为假的文字，每个已赋值变量恰好出现一次。
标记值分别为 0（未设置）、1（假）、2（冲突分析标记）、5（未能推出）和 6（已推出）。
reason 是子句 ID，decision 的 reason 为 0。撤销赋值后仍保留 phase。
MTF（move-to-front）链表从 `head` 出发，沿 `previous` 遍历到 0。

访问函数本身是全函数；索引范围等前提需要在实现验证中通过 invariant 建立。 -/
structure State where
  /-- 内部变量数；初始化时取声明变量数与 1 的最大值。 -/
  nVars : Nat
  /-- 紧凑子句数据库，存放 watch 链接、文字和零结束标记。 -/
  arena : Array Nat
  /-- 每个文字的 watch 链表头；0 表示空链表。 -/
  first : Array Nat
  /-- 按文字索引的赋值及冲突分析标记。 -/
  marks : Array Nat
  /-- 按变量索引的 reason 子句 ID；0 表示 decision。 -/
  reasons : Array Nat
  /-- 每个变量最近保存的布尔取值，撤销赋值后仍保留。 -/
  phases : Array Bool
  /-- 固定容量的假文字数组；只有 `assigned` 之前的前缀是活动赋值。 -/
  trail : Array Lit
  /-- 活动 trail 的长度，即当前已赋值变量数。 -/
  assigned : Nat := 0
  /-- 已取出进行传播的 trail 前缀长度；watch 阶段还需完成当前文字的链表。 -/
  processed : Nat := 0
  /-- 已确认的 root trail 前缀长度，restart 时保留。 -/
  forced : Nat := 0
  /-- MTF 链表中从头部向后遍历的链接。 -/
  previous : Array Nat
  /-- MTF 链表中朝头部方向的反向链接。 -/
  next : Array Nat
  /-- MTF decision 链表的头变量。 -/
  head : Nat
  /-- 原始子句区域结束位置，也是学习子句区域起点。 -/
  fixed : Nat := 2
  /-- 当前保留的学习子句数量。 -/
  nLemmas : Nat := 0
  /-- 触发 reduction 的学习子句容量阈值，会随实际数量增长。 -/
  maxLemmas : Nat := 2000
  /-- 自上次相关重置以来的冲突分析计数，对应参考实现字段。 -/
  res : Nat := 0
  /-- LBD 的快速定点滑动统计，用于 restart 启发式。 -/
  fast : Nat := 16777216
  /-- LBD 的慢速定点滑动统计，用于 restart 启发式。 -/
  slow : Nat := 16777216
  /-- 累计执行统计。 -/
  stats : Stats := {}
  /-- 本次求解使用的配置。 -/
  config : Config := {}
  deriving Repr, Inhabited

/-- 从 watch 引用中解码所属子句的 ID。 -/
@[inline] def watchClause (ref : Nat) : Nat := ref / 2

/-- 计算 watch 引用对应的 arena 链接单元位置。 -/
@[inline] def watchLinkPos (ref : Nat) : Nat := ref / 2 - 2 + ref % 2

namespace State

/-- 读取文字的当前标记。 -/
@[inline] def mark (s : State) (lit : Lit) : Nat := s.marks[lit]!

/-- 读取文字所属变量的 reason 子句 ID；decision 使用 0。 -/
@[inline] def reason (s : State) (lit : Lit) : Nat := s.reasons[lit.var]!

/-- 读取 arena 中指定位置的单元。 -/
@[inline] def db (s : State) (idx : Nat) : Nat := s.arena[idx]!

/-- 更新一个文字的标记，保留状态的其他字段。 -/
@[inline] def setMark (s : State) (lit : Lit) (value : Nat) : State :=
  { s with marks := s.marks.set! lit value }

/-- 清除 trail 中假文字的标记，以撤销对应变量的赋值。 -/
@[inline] def unassign (s : State) (lit : Lit) : State := s.setMark lit 0

/-- 将子句的首文字赋为真，并保存 reason、phase 和相反的假文字。
调用前要求该子句在当前赋值下是 unit，且首文字对应的变量尚未赋值。 -/
@[inline] def assign (s : State) (clauseId : Nat) (root : Bool) : State := Id.run do
  let lit : Lit := s.db clauseId
  let falseLit := lit.negate
  return { s with
    marks := s.marks.set! falseLit (if root then 6 else 1)
    trail := s.trail.set! s.assigned falseLit
    assigned := s.assigned + 1
    reasons := s.reasons.set! lit.var clauseId
    phases := s.phases.set! lit.var (lit % 2 == 0)
    stats := { s.stats with propagations := s.stats.propagations + 1 } }

/-- 使用上次保存的 phase，为尚未赋值的变量作一次 decision。 -/
@[inline] def decide (s : State) (var : Nat) : State :=
  let lit : Lit := 2 * var + if s.phases[var]! then 0 else 1
  { s with
    marks := s.marks.set! lit.negate 1
    trail := s.trail.set! s.assigned lit.negate
    assigned := s.assigned + 1
    reasons := s.reasons.set! var 0
    stats := { s.stats with decisions := s.stats.decisions + 1 } }

/-- 将 watch 引用插入指定文字的 watch 链表头部。 -/
@[inline] def addWatch (s : State) (lit : Lit) (ref : Nat) : State :=
  { s with
    arena := s.arena.set! (watchLinkPos ref) s.first[lit]!
    first := s.first.set! lit ref }

/-- 追加一个子句，并返回首文字位置作为子句 ID。
原始子句必须位于所有学习子句之前，使 `fixed` 始终是输入子句前缀的边界。 -/
def addClause (s : State) (lits : Array Lit) (original : Bool) : State × Nat := Id.run do
  let clauseId := s.arena.size + 2
  let mut arena := s.arena.push 0 |>.push 0
  for lit in lits do
    arena := arena.push lit
  arena := arena.push 0
  let mut s := { s with arena }
  if lits.size > 1 then
    s := s.addWatch lits[0]! (2 * clauseId)
    s := s.addWatch lits[1]! (2 * clauseId + 1)
  if original then
    s := { s with fixed := s.arena.size }
  else
    s := { s with nLemmas := s.nLemmas + 1 }
  return (s, clauseId)

/-- 撤销所有非 root 赋值，保留 root 前缀和已保存的 phase。 -/
def restart (s : State) : State := Id.run do
  let mut s := s
  for _ in [:s.assigned - s.forced] do
    let idx := s.assigned - 1
    s := { s.unassign s.trail[idx]! with assigned := idx }
  return { s with
    processed := s.forced
    stats := { s.stats with restarts := s.stats.restarts + 1 } }

/-- 标记一个假文字，并将其变量移到 decision 链表头部。
与参考求解器一致，跳过标记为 root implied 的文字。 -/
def bump (s : State) (lit : Lit) : State := Id.run do
  if s.mark lit == 6 then return s
  let mut s := s.setMark lit 2
  let var := lit.var
  if var != s.head then
    let prev := s.previous[var]!
    let next := s.next[var]!
    s := { s with
      previous := s.previous.set! next prev
      next := s.next.set! prev next }
    s := { s with
      next := s.next.set! s.head var
      previous := s.previous.set! var s.head
      head := var }
  return s

/-- 移除学习子句的 watch，保留原始子句的链接及其顺序。
在有效状态下，每条链表无环，长度不超过 `arena.size`。 -/
def removeLearnedWatches (s : State) : State := Id.run do
  let mut s := s
  for lit in [2:s.first.size] do
    let mut ref := s.first[lit]!
    let mut previousLink : Option Nat := none
    for _ in [:s.arena.size] do
      if ref == 0 then break
      let linkPos := watchLinkPos ref
      let nextRef := s.db linkPos
      if watchClause ref < s.fixed then
        previousLink := some linkPos
      else
        match previousLink with
        | none => s := { s with first := s.first.set! lit nextRef }
        | some pos => s := { s with arena := s.arena.set! pos nextRef }
      ref := nextRef
  return s

/-- 在 root 层 restart 时压缩学习子句数据库，保留被少于 `k` 个已保存 phase 满足的子句。
同时保留 root reason 子句并重映射其 ID；在通常的 root invariant 和 `k > 1` 下，
这些子句已满足保留条件。显式保留和重映射避免了参考 C 实现中 reason 指向旧地址的问题。
所有扫描都有显式有限上界，以便后续证明 termination。 -/
def reduceDB (s : State) (k : Nat) : State := Id.run do
  let oldArena := s.arena
  let oldLemmas := s.nLemmas
  let mut limit := s.maxLemmas
  if s.nLemmas > limit then
    limit := limit + 300 * ((s.nLemmas - limit + 299) / 300)
  let mut locked := Array.replicate oldArena.size false
  for idx in [:s.forced] do
    let clauseId := s.reason s.trail[idx]!
    if clauseId != 0 then locked := locked.set! clauseId true
  let mut s := removeLearnedWatches s
  s := { s with arena := s.arena.extract 0 s.fixed, nLemmas := 0, maxLemmas := limit }
  let mut remap := Array.replicate oldArena.size 0
  let mut start := s.fixed
  for _ in [:oldLemmas] do
    let clauseId := start + 2
    let mut lits : Array Lit := #[]
    let mut count := 0
    let mut cursor := clauseId
    for _ in [:oldArena.size - clauseId] do
      let lit : Lit := oldArena[cursor]!
      if lit == 0 then break
      lits := lits.push lit
      if lit.satisfiedBy s.phases then count := count + 1
      cursor := cursor + 1
    start := cursor + 1
    if count < k || locked[clauseId]! then
      let (next, newId) := s.addClause lits false
      s := next
      remap := remap.set! clauseId newId
  let mut reasons := s.reasons
  for var in [1:s.nVars + 1] do
    let oldId := reasons[var]!
    if oldId >= s.fixed then
      reasons := reasons.set! var remap[oldId]!
  return { s with
    reasons := reasons
    stats := { s.stats with
      reductions := s.stats.reductions + 1
      removedLearned := s.stats.removedLearned + oldLemmas - s.nLemmas } }

end State

/-- 创建空的紧凑数据库和初始降序 decision 链表。
直接按索引构造链接值，避免可变初始化循环；内部变量数至少为 1。 -/
def emptyState (numVars : Nat) (config : Config := {}) : State :=
  let n := max 1 numVars
  {
    nVars := n, arena := #[0, 0]
    first := Array.replicate (2 * (n + 1)) 0
    marks := Array.replicate (2 * (n + 1)) 0
    reasons := Array.replicate (n + 1) 0
    phases := Array.replicate (n + 1) false
    trail := Array.replicate (n + 1) 0
    previous := Array.ofFn fun i : Fin (n + 1) => i.val - 1
    next := Array.ofFn fun i : Fin (n + 1) => if i.val < n then i.val + 1 else 0
    head := n, maxLemmas := config.initialLemmaLimit, config }

/-- 单个子句的规范化结果，以及与其他子句共用的时间戳表。 -/
structure NormalizedClause where
  /-- 删除重复文字后的子句，保留首次出现的次序。 -/
  lits : Array Lit
  /-- 按文字索引的共享时间戳表，记录当前子句中已经出现的文字。 -/
  stamps : Array Nat
  /-- 是否同时出现某变量的正负文字，即该子句是否为重言式。 -/
  tautology : Bool

/-- 检查文字范围，删除重复文字，并检测互补文字对。
调用者需要为每个输入子句选择不同的非零时间戳。 -/
def normalizeClause (numVars stamp : Nat) (stamps : Array Nat) (clause : Array Lit) :
    Except String NormalizedClause := do
  let mut result : NormalizedClause := ⟨#[], stamps, false⟩
  for lit in clause do
    if lit.var == 0 || lit.var > numVars then
      throw s!"literal {lit.toInt} is outside declared variable range 1..{numVars}"
    if result.stamps[lit.negate]! == stamp then
      result := { result with tautology := true }
    if result.stamps[lit]! != stamp then
      result := { result with stamps := result.stamps.set! lit stamp, lits := result.lits.push lit }
  return result

/-- 检查并规范化输入子句，然后构造初始状态。
通过每个子句独立的时间戳在线性时间内去重，并丢弃重言式。
`none` 表示发现空子句或互相矛盾的 unit；其他推论留给 watched-literal propagation。 -/
def initState (formula : Formula) (config : Config := {}) : Except String (Option State) := do
  let mut s := emptyState formula.numVars config
  let mut stamps := Array.replicate (2 * (s.nVars + 1)) 0
  for idx in [:formula.clauses.size] do
    let stamp := idx + 1
    let normalized ← normalizeClause formula.numVars stamp stamps formula.clauses[idx]!
    stamps := normalized.stamps
    let lits := normalized.lits
    if !normalized.tautology then
      if lits.isEmpty then return none
      let (nextState, clauseId) := s.addClause lits true
      s := nextState
      if lits.size == 1 then
        let lit := lits[0]!
        if s.mark lit != 0 then return none
        if s.mark lit.negate == 0 then s := s.assign clauseId true
  return some s

end MicrosatLean.CDCL
