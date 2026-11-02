import MicrosatLean.Verification.Implementation.Representation.Types

/-! 逻辑 trail 记录真 literals，具体 trail 记录它们的补 literal；这里的 reason 是逻辑 clause，而非 arena 地址。
RepresentationWitness 统一描述 packed clauses、watch 链和变量顺序，Rep 将当前具体数据对应到逻辑状态。
Rep 只刻画当前状态；trail 数组活动区间之外的旧内容不构成有效 assignment，也不假定后续执行行为。
-/

namespace MicrosatLean.Verification

/-- 逻辑 trail 的一个真 literal 及其可选 reason；decision 使用 none。 -/
structure TrailEntry where
  /-- 该位置被置真的标准 literal。 -/
  literal : Literal
  /-- 传播使用的逻辑 reason clause；decision 为 none。 -/
  reason : Option Clause
  deriving Inhabited

/-- 用于推理的抽象搜索状态：变量上界、原始与 learned clauses、真值 trail 及 root 前缀长度。 -/
structure LogicalState where
  /-- 与具体 state 对齐的内部变量上界。 -/
  numVars : Nat
  /-- 初始化后保留的原始 clauses，与原始输入语义等价。 -/
  original : List Clause
  /-- 当前保留、且被原始输入蕴含的 learned clauses。 -/
  learned : List Clause
  /-- 按赋值先后排列的真 literals 与 reasons。 -/
  trail : List TrailEntry
  /-- 无需 decision assumptions 即成立的 root 前缀长度。 -/
  rootSize : Nat

/-- 按原始 clauses 在前、learned clauses 在后的顺序组成当前逻辑数据库。 -/
def LogicalState.database (a : LogicalState) : List Clause := a.original ++ a.learned

/-- 丢弃 reason 信息，取得逻辑 trail 上全部为真的 literals。 -/
def LogicalState.trueTrail (a : LogicalState) : List Literal := a.trail.map TrailEntry.literal

/-- 把逻辑 clause 列表装成标准 CNF，以使用 Std 的语义和 entailment 定理。 -/
def databaseView (clauses : List Clause) : CNF := ⟨clauses.toArray⟩

/-- literal 出现在真值 trail 中。 -/
def TrueIn (trail : List Literal) (lit : Literal) : Prop := lit ∈ trail

/-- literal 的补项出现在真值 trail 中，因此该 literal 已为假。 -/
def FalseIn (trail : List Literal) (lit : Literal) : Prop := lit.negate ∈ trail

/-- total assignment 与 trail 上记录的每个真 literal 一致。 -/
def Compatible (a : Assignment) (trail : List Literal) : Prop :=
  ∀ lit ∈ trail, a lit.1 = lit.2

/-- 指定变量尚未出现在真值 trail 上。 -/
def Unassigned (trail : List Literal) (var : Nat) : Prop :=
  ∀ lit ∈ trail, lit.1 ≠ var

/-- 标准 literal 的变量编号处于 1..variables 内。 -/
def LiteralBound (variables : Nat) (lit : Literal) : Prop := 0 < lit.1 ∧ lit.1 ≤ variables

/-- clause 的任一候选 head 若其余 literals 均为假，则该 head 已在 trail 上为真。
这描述传播闭包要求；所有 unit 后果均已体现于 trail。
-/
def UnitClosed (trail : List Literal) (clause : Clause) : Prop :=
  ∀ head ∈ clause, (∀ tail ∈ clause, tail ≠ head → FalseIn trail tail) → TrueIn trail head

/-- 当前数据库中的每个 clause 都满足 UnitClosed。 -/
def Closed (a : LogicalState) : Prop := ∀ clause ∈ a.database, UnitClosed a.trueTrail clause

/-- 每个声明变量都已在真值 trail 中出现。 -/
def Complete (a : LogicalState) : Prop :=
  ∀ var, 0 < var → var ≤ a.numVars → ∃ lit ∈ a.trueTrail, lit.1 = var

/-- 指定 clause 的所有 literals 在当前 trail 下均为假。 -/
def Conflict (a : LogicalState) (clause : Clause) : Prop :=
  ∀ lit ∈ clause, FalseIn a.trueTrail lit

/-- 取逻辑 trail 前 count 项的真 literals，用于描述 reason 的时间顺序和 decision 边界。 -/
def prefixLiterals (a : LogicalState) (count : Nat) : List Literal :=
  (a.trail.take count).map TrailEntry.literal

/-- 复用实现层唯一的 packed-clause 描述类型，避免维护重复的存储定义。 -/
abbrev StoredClause := Implementation.Representation.StoredClause

/-- 连接具体与逻辑状态的共享见证：存储 clauses、watch 链顺序以及 MTF 变量顺序。 -/
structure RepresentationWitness where
  /-- 按 arena 顺序排列的原始存储 entries。 -/
  original : List StoredClause
  /-- 原始前缀之后的 learned entries。 -/
  learned : List StoredClause
  /-- 每个 literal 对应的有序 watch references。 -/
  heads : Lit → List Nat
  /-- 从 MTF head 开始的变量顺序。 -/
  order : List Nat

/-- 按 packed database 顺序拼接原始和 learned 存储条目。 -/
def RepresentationWitness.entries (w : RepresentationWitness) : List StoredClause :=
  w.original ++ w.learned

/-- 复用具体状态的数组长度与索引覆盖谓词。 -/
abbrev ArrayBounds := Implementation.Representation.ArrayBounds

/-- 复用具体 arena 中 clauseId 与 literal 数组的 packed 存储关系。 -/
abbrev PackedClause (s : CDCL.State) (entry : StoredClause) :=
  Implementation.Representation.PackedClause s entry.id entry.lits

/-- 复用从指定 arena 起点连续存放 clause entries 的布局谓词。 -/
abbrev DatabaseFrom := Implementation.Representation.DatabaseFrom

/-- 复用 watch certificate，把具体 first/arena links 对应到同一个 witness 的 watch lists。 -/
abbrev WatchRepresentation (s : CDCL.State) (w : RepresentationWitness) :=
  Implementation.Propagation.WatchCertificate s w.entries w.heads

/-- 复用具体 MTF 链与逻辑变量顺序的对应关系。 -/
abbrev OrderRepresentation := Implementation.Representation.MTFOrder

/-- 通过同一个 witness 对齐 numeric storage 与 LogicalState。
记录 arena 布局、计数、活动 trail、marks、saved phases、reasons、watches 和 decision order。
数组活动区间之外允许存在旧值；这些旧值不被视为当前 assignment。
-/
structure Rep (m : CDCL.Machine) (a : LogicalState) (w : RepresentationWitness) : Prop where
  /-- 逻辑与具体状态使用同一个变量上界。 -/
  variables : a.numVars = m.solver.nVars
  /-- 各数组的长度覆盖有效索引范围。 -/
  arrays : ArrayBounds m.solver
  /-- arena 至少包含最初两个保留单元。 -/
  reserved : 2 ≤ m.solver.arena.size
  /-- 从偏移 2 起精确连续存储所有 witness entries。 -/
  layout : DatabaseFrom m.solver 2 w.entries
  /-- fixed 精确对应原始 entries 的总存储长度。 -/
  fixed : m.solver.fixed = 2 + (w.original.map fun e => e.lits.size + 3).sum
  /-- nLemmas 与 learned entries 数量一致。 -/
  count : m.solver.nLemmas = w.learned.length
  /-- 逻辑 original 由对应存储条目逐项解释得到。 -/
  original : a.original = w.original.map Implementation.Representation.StoredClause.view
  /-- 逻辑 learned 由对应存储条目逐项解释得到。 -/
  learned : a.learned = w.learned.map Implementation.Representation.StoredClause.view
  /-- 逻辑 trail 长度等于具体 assigned 计数。 -/
  trailLength : a.trail.length = m.solver.assigned
  /-- 逻辑 root 前缀长度等于具体 forced。 -/
  rootSize : a.rootSize = m.solver.forced
  /-- 三个 trail 边界依次有序且不超过内部变量数。 -/
  cursors : m.solver.forced ≤ m.solver.processed ∧
    m.solver.processed ≤ m.solver.assigned ∧ m.solver.assigned ≤ m.solver.nVars
  /-- 逻辑真 literal 是具体假 literal 的补项。 -/
  trail : ∀ i, i < m.solver.assigned →
    a.trail[i]!.literal = (literalView m.solver.trail[i]!).negate
  /-- 每个活动假 literal 的 mark 非零，其补 literal 的 mark 为零。 -/
  active : ∀ i, i < m.solver.assigned →
    m.solver.mark m.solver.trail[i]! ≠ 0 ∧ m.solver.mark m.solver.trail[i]!.negate = 0
  /-- mark 非零的 literals 恰好是活动具体 trail 中的项。 -/
  marks : ∀ lit, m.solver.mark lit ≠ 0 ↔
    ∃ i, i < m.solver.assigned ∧ m.solver.trail[i]! = lit
  /-- saved phases 与所有活动逻辑赋值一致。 -/
  phases : ∀ i, i < a.trail.length →
    m.solver.phases[a.trail[i]!.literal.1]! = a.trail[i]!.literal.2
  /-- 逻辑 reason 对应实际 reason 地址所指的同一存储 clause；decision 对应地址 0。 -/
  reasons : ∀ i, i < m.solver.assigned →
    match a.trail[i]!.reason with
    | none => m.solver.reason m.solver.trail[i]! = 0
    | some clause => ∃ entry ∈ w.entries,
        entry.id = m.solver.reason m.solver.trail[i]! ∧ entry.view = clause
  /-- 具体 watch 链与 witness heads 一致。 -/
  watches : WatchRepresentation m.solver w
  /-- 具体 MTF 链与 witness order 一致。 -/
  order : OrderRepresentation m.solver w.order

/-- clause 列表的标准 CNF view 被满足，当且仅当列表里的每个 clause 都被满足。 -/
theorem databaseView_sat_iff (clauses : List Clause) (a : Assignment) :
    Std.Sat.CNF.Sat a (databaseView clauses) ↔
      ∀ clause ∈ clauses, Std.Sat.CNF.Clause.Sat a clause := by
  simp [Std.Sat.CNF.sat_iff_all_mem_sat, databaseView, Std.Sat.CNF.Internal.mem_iff]

end MicrosatLean.Verification
