import MicrosatLean.Formula

/-! Microsat 的具体存储与基础状态操作。子句紧凑存放在 arena 中，watch list 用数字链接表示。
可执行 trail 记录被置假的 literals；验证层的逻辑 trail 则记录它们的补 literal。
数组访问是 total 的；正常执行所需的边界、reason 和链表性质由 verification invariant 保证。
-/

namespace MicrosatLean.CDCL

/-- 可调的 learned-clause 数据库策略；验证覆盖任意 Config，而非只覆盖默认参数。 -/
structure Config where
  /-- 初始 learned-clause 数量上限。 -/
  initialLemmaLimit : Nat := 2000
  /-- reduction 的 saved-phase 满足项计数阈值。 -/
  reductionK : Nat := 6
  deriving Repr, Inhabited

/-- 执行过程中累计的搜索统计；最终 ValidResult specification 不约束这些计数。 -/
structure Stats where
  /-- 累计分析的非 root conflicts。 -/
  conflicts : Nat := 0
  /-- 累计 decisions。 -/
  decisions : Nat := 0
  /-- 通过 reason clause 执行的累计 assignments。 -/
  propagations : Nat := 0
  /-- 累计 restarts。 -/
  restarts : Nat := 0
  /-- 累计数据库 reductions。 -/
  reductions : Nat := 0
  /-- 累计删除的 learned clauses 数量。 -/
  removedLearned : Nat := 0
  deriving Repr, Inhabited

/-- 对应 microsat.c 可变字段的具体 solver state。

arena 开头保留两个零单元；每个 clause 占用两个 watch-link 单元、literal 序列及一个零终止符。
clauseId 指向首 literal，watch reference 为 2 * clauseId + slot，slot 为 0 或 1。
交换 watched literals 时 reference 仍对应原 link 单元；0 表示 watch 链结束，不是 clauseId。

有效状态满足 forced ≤ processed ≤ assigned ≤ nVars，活动 trail 每个已赋值变量恰有一个假 literal。
marks 的 0/1/2/5/6 分别用于未置假、普通假值、分析标记、implied 失败缓存与成功缓存。
reason 为 clauseId，decision 的 reason 为 0；phases 在撤销赋值后保留。
MTF decision list 从 head 沿 previous 遍历到 0。数组访问边界由 representation invariant 保证。
-/
structure State where
  /-- 内部变量上界，初始化为 max 1 numVars。 -/
  nVars : Nat
  /-- 紧凑存储 clause literals、watch links 与零终止符。 -/
  arena : Array Nat
  /-- 按 literal 索引的 watch list 头 reference。 -/
  first : Array Nat
  /-- 按 literal 索引的真假/分析 tag 数组。 -/
  marks : Array Nat
  /-- 按变量索引的 reason clauseId，decision 对应 0。 -/
  reasons : Array Nat
  /-- 各变量最后保存的 Bool phase，撤销赋值后仍保留。 -/
  phases : Array Bool
  /-- 固定容量数组，活动前缀保存假 literals。 -/
  trail : Array Lit
  /-- 正常搜索中活动 trail 项数；冲突分析中临时表示 candidate 索引。 -/
  assigned : Nat := 0
  /-- 已经取出开始处理的 trail 前缀长度；分析中也记录 backjump cursor。 -/
  processed : Nat := 0
  /-- 不可因 backjump/restart 撤销的 root trail 前缀长度。 -/
  forced : Nat := 0
  /-- MTF 链的 previous 指针；从 head 沿它访问 decision 候选变量。 -/
  previous : Array Nat
  /-- MTF 双向链的 next 指针，用于移动变量。 -/
  next : Array Nat
  /-- MTF decision list 的头变量。 -/
  head : Nat
  /-- 原始 clause 前缀结束、learned 数据区开始的 arena 边界。 -/
  fixed : Nat := 2
  /-- 当前保留的 learned clauses 数量。 -/
  nLemmas : Nat := 0
  /-- 触发数据库 reduction 的可增长上限。 -/
  maxLemmas : Nat := 2000
  /-- 重启相关冲突计数，由 choice 在选定 restart 时清零。 -/
  res : Nat := 0
  /-- LBD 的快速整数平滑量。 -/
  fast : Nat := 16777216
  /-- LBD 的慢速整数平滑量。 -/
  slow : Nat := 16777216
  /-- 累计执行统计。 -/
  stats : Stats := {}
  /-- 本次求解采用的策略配置。 -/
  config : Config := {}
  deriving Repr, Inhabited

/-- 从 watch reference 解码它所属的 clauseId。 -/
@[inline] def watchClause (ref : Nat) : Nat := ref / 2

/-- 从 watch reference 计算其 next-link 在 arena 中的存储位置。 -/
@[inline] def watchLinkPos (ref : Nat) : Nat := ref / 2 - 2 + ref % 2

namespace State

/-- 读取 literal 的 mark tag；正常执行中的索引范围由 invariant 保证。 -/
@[inline] def mark (s : State) (lit : Lit) : Nat := s.marks[lit]!

/-- 按 literal 的变量编号读取 reason clauseId；0 表示 decision。 -/
@[inline] def reason (s : State) (lit : Lit) : Nat := s.reasons[lit.var]!

/-- 读取 packed arena 中的一个单元；其含义取决于它是 literal、link 还是终止符。 -/
@[inline] def db (s : State) (idx : Nat) : Nat := s.arena[idx]!

/-- 更新一个 literal 的 mark，保留其他状态字段。 -/
@[inline] def setMark (s : State) (lit : Lit) (value : Nat) : State :=
  { s with marks := s.marks.set! lit value }

/-- 清除一个假 literal 的 mark；调用者负责同步活动 trail 的边界。 -/
@[inline] def unassign (s : State) (lit : Lit) : State := s.setMark lit 0

/-- 将 reason clause 的首 literal 置真，并把补 literal 追加到活动 trail。
调用前需要该 clause 在当前赋值下为 unit，且首 literal 的变量尚未赋值。
同时记录 reason、保存 phase，并增加 propagation 计数；root 决定使用 6 或 1 的 mark。
-/
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

/-- 为未赋值变量采用最后保存的 phase，追加 reason 为 0 的 decision，并增加 decision 计数。 -/
@[inline] def decide (s : State) (var : Nat) : State :=
  let lit : Lit := 2 * var + if s.phases[var]! then 0 else 1
  { s with
    marks := s.marks.set! lit.negate 1
    trail := s.trail.set! s.assigned lit.negate
    assigned := s.assigned + 1
    reasons := s.reasons.set! var 0
    stats := { s.stats with decisions := s.stats.decisions + 1 } }

/-- 把指定 watch reference 插到 literal 的 watch list 头部，同时更新 arena 中的 next-link。 -/
@[inline] def addWatch (s : State) (lit : Lit) (ref : Nat) : State :=
  { s with
    arena := s.arena.set! (watchLinkPos ref) s.first[lit]!
    first := s.first.set! lit ref }

/-- 把 clause 追加到 arena，并返回首 literal 的 clauseId；非 unit clause 同时建立两个 watches。
原始 clauses 必须先于所有 learned clauses 插入，以使 fixed 始终表示原始数据库前缀的边界。
-/
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

/-- 撤销全部非 root 赋值，把 processed 恢复到 forced；保留 saved phases，并累计 restart 次数。 -/
def restart (s : State) : State := Id.run do
  let mut s := s
  for _ in [:s.assigned - s.forced] do
    let idx := s.assigned - 1
    s := { s.unassign s.trail[idx]! with assigned := idx }
  return { s with
    processed := s.forced
    stats := { s.stats with restarts := s.stats.restarts + 1 } }

/-- 把假 literal 标成分析标记 2，并把变量移到 MTF decision list 的头部。
已具有 tag 6 的 literal 按参考求解器的规则跳过。
-/
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

/-- 从每个 watch list 中删除 learned-clause references，保留原始 links 的顺序。
有效状态下链表无环且长度至多为 arena.size，因此有限扫描预算足够。
-/
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

/-- 在 root-level restart 后压缩 learned 数据库，保留被 saved phases 满足的 literal 数少于 k 的 clauses。
root reason clauses 也会被锁定保留，并在复制后重映射 reason 地址，以避免悬空 reason。
maxLemmas 按实际计数递增；所有 clause/watch 扫描均有显式有限界。
-/
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

/-- 建立空 packed database 与初始 descending decision order。
内部变量数取 max 1 numVars，直接按索引构造 MTF 链，无需可变初始化循环。
-/
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

/-- 单个输入 clause 的规范化结果，以及跨 clause 复用的 stamp 数组。 -/
structure NormalizedClause where
  /-- 去重后的 literals，保持首次出现的顺序。 -/
  lits : Array Lit
  /-- 更新后的 per-clause stamp 表，供下一条 clause 复用。 -/
  stamps : Array Nat
  /-- 原 clause 是否出现了某个变量的互补 literal 对。 -/
  tautology : Bool

/-- 检查变量边界、去掉重复 literals 并检测互补对；调用者为每个 clause 提供新的非零 stamp。 -/
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

/-- 规范化输入并建立初始 state、clauses、watches 和 root units。
stamp 实现线性去重和 tautology 检测；空 clause 或冲突 unit 提前返回 none。
其余传播后果留给 watched-literal propagation；非法 literal 返回 error。
-/
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
