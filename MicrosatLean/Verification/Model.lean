import MicrosatLean.Verification.Specification

namespace MicrosatLean.Verification

/-!
逻辑 trail 记录为真的文字；可执行 trail 记录其互补文字。
这里的 reason 是逻辑子句，不是 arena 数值地址。`RepresentationWitness` 提供共享的
紧凑布局、watch 和变量顺序描述。`Rep` 只关联当前数据，不假设未来执行行为。
-/

/-- 逻辑 trail 的一项：保存为真的文字，以及可选的 reason 子句；`none` 表示 decision。 -/
structure TrailEntry where
  /-- 此项赋值为真的标准文字，与具体 trail 中的假文字互补。 -/
  literal : Literal
  /-- 传播使用的逻辑 reason 子句；decision 为 `none`。 -/
  reason : Option Clause
  deriving Inhabited

/-- 忽略物理数组布局的逻辑状态，记录子句数据库、为真的 trail 和 root 前缀长度。 -/
structure LogicalState where
  /-- 逻辑状态使用的内部变量上界，包含初始化器的最小容量处理。 -/
  numVars : Nat
  /-- 规范化后保留的原始子句。 -/
  original : List Clause
  /-- 当前保留的学习子句。 -/
  learned : List Clause
  /-- 按赋值顺序排列的真文字和 reason。 -/
  trail : List TrailEntry
  /-- 无需 decision 假设、由输入蕴含的 root 前缀长度。 -/
  rootSize : Nat

/-- 当前逻辑数据库，由原始子句和保留的学习子句组成。 -/
def LogicalState.database (a : LogicalState) : List Clause := a.original ++ a.learned

/-- 提取逻辑 trail 中依次为真的文字，不保留 reason 信息。 -/
def LogicalState.trueTrail (a : LogicalState) : List Literal := a.trail.map TrailEntry.literal

/-- 将逻辑子句列表转换为标准 CNF，便于使用标准满足关系。 -/
def databaseView (clauses : List Clause) : CNF := ⟨clauses.toArray⟩

/-- 文字出现在 true trail 中，即在当前部分赋值下为真。 -/
def TrueIn (trail : List Literal) (lit : Literal) : Prop := lit ∈ trail

/-- 文字的互补文字出现在 true trail 中，即该文字在当前部分赋值下为假。 -/
def FalseIn (trail : List Literal) (lit : Literal) : Prop := lit.negate ∈ trail

/-- 一个 total assignment 与 trail 中的所有赋值一致。 -/
def Compatible (a : Assignment) (trail : List Literal) : Prop :=
  ∀ lit ∈ trail, a lit.1 = lit.2

/-- trail 中没有该变量的任何文字，即变量尚未赋值。 -/
def Unassigned (trail : List Literal) (var : Nat) : Prop :=
  ∀ lit ∈ trail, lit.1 ≠ var

/-- 文字的变量编号为正，且不超过声明的变量上界。 -/
def LiteralBound (variables : Nat) (lit : Literal) : Prop := 0 < lit.1 ∧ lit.1 ≤ variables

/-- 子句满足 unit closure：任一文字之外的其余文字都为假时，该文字已经为真。 -/
def UnitClosed (trail : List Literal) (clause : Clause) : Prop :=
  ∀ head ∈ clause, (∀ tail ∈ clause, tail ≠ head → FalseIn trail tail) → TrueIn trail head

/-- 当前数据库的每个子句都满足 unit closure。 -/
def Closed (a : LogicalState) : Prop := ∀ clause ∈ a.database, UnitClosed a.trueTrail clause

/-- 每个声明变量都已经在逻辑 trail 中获得赋值。 -/
def Complete (a : LogicalState) : Prop :=
  ∀ var, 0 < var → var ≤ a.numVars → ∃ lit ∈ a.trueTrail, lit.1 = var

/-- 给定子句的所有文字都在当前 trail 下为假，构成一个冲突。 -/
def Conflict (a : LogicalState) (clause : Clause) : Prop :=
  ∀ lit ∈ clause, FalseIn a.trueTrail lit

/-- 提取逻辑 trail 前 `count` 项中的真文字，用于描述 reason 的先后顺序和历史前缀。 -/
def prefixLiterals (a : LogicalState) (count : Nat) : List Literal :=
  (a.trail.take count).map TrailEntry.literal

/-- 证明用的物理子句描述：记录真实 arena ID 及对应的文字数组。 -/
structure StoredClause where
  /-- 子句首文字在 arena 中的位置。 -/
  id : Nat
  /-- 该子句在当前物理布局中的完整文字数组。 -/
  lits : Array Lit

/-- 将一个物理子句描述转换为标准逻辑子句。 -/
def StoredClause.view (entry : StoredClause) : Clause := clauseView entry.lits

/-- 共享的表示见证：描述原始及学习子句、各文字的 watch 链表和 decision 顺序。 -/
structure RepresentationWitness where
  /-- 原始子句的物理描述，按 arena 次序排列。 -/
  original : List StoredClause
  /-- 学习子句的物理描述，按 arena 次序排列。 -/
  learned : List StoredClause
  /-- 每个内部编码文字对应的有限 watch 引用列表。 -/
  heads : Lit → List Nat
  /-- 从 MTF 链表头开始的完整变量顺序。 -/
  order : List Nat

/-- 按物理布局顺序合并原始子句与学习子句描述。 -/
def RepresentationWitness.entries (w : RepresentationWitness) : List StoredClause :=
  w.original ++ w.learned

/-- 各索引数组与内部变量数的长度对应关系，供索引合法性证明使用。 -/
structure ArrayBounds (s : CDCL.State) : Prop where
  /-- watch 头数组为每个变量的正负文字预留位置。 -/
  first : s.first.size = 2 * (s.nVars + 1)
  /-- 标记数组覆盖与 watch 头数组相同的文字范围。 -/
  marks : s.marks.size = 2 * (s.nVars + 1)
  /-- reason 数组覆盖所有内部变量及保留编号 0。 -/
  reasons : s.reasons.size = s.nVars + 1
  /-- phase 数组覆盖所有内部变量及保留编号 0。 -/
  phases : s.phases.size = s.nVars + 1
  /-- trail 容量覆盖全部内部变量，并额外保留一个位置。 -/
  trail : s.trail.size = s.nVars + 1
  /-- MTF 正向遍历链接数组覆盖全部变量及编号 0。 -/
  previous : s.previous.size = s.nVars + 1
  /-- MTF 反向链接数组覆盖全部变量及编号 0。 -/
  next : s.next.size = s.nVars + 1

/-- 单个子句在 arena 中的布局条件：起始位置、界限、文字内容、结束标记及变量范围。 -/
structure PackedClause (s : CDCL.State) (entry : StoredClause) : Prop where
  /-- 子句 ID 留出了 arena 的两个保留单元和自身的两个链接单元。 -/
  header : 4 ≤ entry.id
  /-- 子句全部文字和其结束标记均位于 arena 内。 -/
  bound : entry.id + entry.lits.size < s.arena.size
  /-- 子句描述中的每个文字与 arena 对应位置完全一致。 -/
  literals : ∀ i, i < entry.lits.size → s.db (entry.id + i) = entry.lits[i]!
  /-- 文字序列后紧跟零结束标记。 -/
  terminator : s.db (entry.id + entry.lits.size) = 0
  /-- 每个文字都使用合法且未越界的变量编号。 -/
  declared : ∀ lit ∈ entry.lits, 0 < lit.var ∧ lit.var ≤ s.nVars

/-- 从给定位置开始，子句依次连续存储并恰好填满剩余 arena。
精确布局排除了把任意子句后缀当作合法子句 ID 的情况。 -/
def DatabaseFrom (s : CDCL.State) (start : Nat) : List StoredClause → Prop
  | [] => start = s.arena.size
  | entry :: rest => entry.id = start + 2 ∧ PackedClause s entry ∧
      DatabaseFrom s (entry.id + entry.lits.size + 1) rest

/-- watch 链表的物理表示：链接准确、引用属于真实子句、两个 watch 被覆盖且归属唯一。 -/
structure WatchRepresentation (s : CDCL.State) (w : RepresentationWitness) : Prop where
  /-- 每条 watch 链表无重复，表头及每个物理后继都与见证列表一致。 -/
  lists : ∀ lit, (w.heads lit).Nodup ∧ s.first[lit]! = (w.heads lit).headD 0 ∧
    ∀ i, i < (w.heads lit).length →
      let ref := (w.heads lit).getD i 0
      ref ≠ 0 ∧ CDCL.watchLinkPos ref < s.arena.size ∧
        s.db (CDCL.watchLinkPos ref) = (w.heads lit).getD (i + 1) 0
  /-- 每个 watch 引用都属于数据库中的真实非 unit 子句。 -/
  genuine : ∀ lit ref, ref ∈ w.heads lit → ∃ entry ∈ w.entries,
    CDCL.watchClause ref = entry.id ∧ 2 ≤ entry.lits.size
  /-- 非 unit 子句的前两个文字不同，且恰有对应的两个 slot 引用覆盖它们，允许 slot 交换归属。 -/
  covered : ∀ entry ∈ w.entries, 2 ≤ entry.lits.size →
    entry.lits[0]! ≠ entry.lits[1]! ∧
    ((2 * entry.id ∈ w.heads entry.lits[0]! ∧ 2 * entry.id + 1 ∈ w.heads entry.lits[1]!) ∨
     (2 * entry.id ∈ w.heads entry.lits[1]! ∧ 2 * entry.id + 1 ∈ w.heads entry.lits[0]!))
  /-- 同一个 watch 引用不能属于两个不同文字的链表。 -/
  unique : ∀ lit other ref, ref ∈ w.heads lit → ref ∈ w.heads other → lit = other

/-- MTF decision 链表的表示关系：无重复地覆盖声明变量，并对应 `head`、`previous`、`next`。 -/
def OrderRepresentation (s : CDCL.State) (order : List Nat) : Prop :=
  order.Nodup ∧ (∀ var, var ∈ order ↔ 0 < var ∧ var ≤ s.nVars) ∧
  s.head = order.headD 0 ∧ ∀ i, i < order.length →
    s.previous[order.getD i 0]! = order.getD (i + 1) 0 ∧
    (0 < i → s.next[order.getD i 0]! = order.getD (i - 1) 0)

/-- 以同一个见证关联数值存储和逻辑状态，描述当前数据，不假设未来行为。
只有活动 trail 是赋值；数组中活动范围之外可能保留旧内容。 -/
structure Rep (m : CDCL.Machine) (a : LogicalState) (w : RepresentationWitness) : Prop where
  /-- 逻辑变量上界等于具体状态的内部变量数。 -/
  variables : a.numVars = m.solver.nVars
  /-- 所有索引数组具有约定长度。 -/
  arrays : ArrayBounds m.solver
  /-- arena 至少包含两个开头的保留单元。 -/
  reserved : 2 ≤ m.solver.arena.size
  /-- 从位置 2 开始的全部物理子句与见证精确对应。 -/
  layout : DatabaseFrom m.solver 2 w.entries
  /-- 原始子句与学习子句的边界由原始子句的实际占用长度确定。 -/
  fixed : m.solver.fixed = 2 + (w.original.map fun e => e.lits.size + 3).sum
  /-- 具体学习子句计数等于见证中的学习子句数。 -/
  count : m.solver.nLemmas = w.learned.length
  /-- 逻辑原始子句来自对应物理子句的标准视图。 -/
  original : a.original = w.original.map StoredClause.view
  /-- 逻辑学习子句来自对应物理子句的标准视图。 -/
  learned : a.learned = w.learned.map StoredClause.view
  /-- 逻辑 trail 的长度等于实际已赋值数量。 -/
  trailLength : a.trail.length = m.solver.assigned
  /-- 逻辑 root 前缀长度等于具体 `forced`。 -/
  rootSize : a.rootSize = m.solver.forced
  /-- root、处理和赋值游标依次有序，且不超过内部变量数。 -/
  cursors : m.solver.forced ≤ m.solver.processed ∧
    m.solver.processed ≤ m.solver.assigned ∧ m.solver.assigned ≤ m.solver.nVars
  /-- 每项逻辑真文字都恰好对应具体 trail 假文字的互补。 -/
  trail : ∀ i, i < m.solver.assigned →
    a.trail[i]!.literal = (literalView m.solver.trail[i]!).negate
  /-- 活动 trail 中的假文字有非零标记，其互补文字没有假标记。 -/
  active : ∀ i, i < m.solver.assigned →
    m.solver.mark m.solver.trail[i]! ≠ 0 ∧ m.solver.mark m.solver.trail[i]!.negate = 0
  /-- 非零标记与活动 trail 中出现的假文字双向对应。 -/
  marks : ∀ lit, m.solver.mark lit ≠ 0 ↔
    ∃ i, i < m.solver.assigned ∧ m.solver.trail[i]! = lit
  /-- 活动赋值与保存的 phase 值一致。 -/
  phases : ∀ i, i < a.trail.length →
    m.solver.phases[a.trail[i]!.literal.1]! = a.trail[i]!.literal.2
  /-- decision 对应 reason ID 0；传播项的 reason ID 对应真实存储的同一逻辑子句。 -/
  reasons : ∀ i, i < m.solver.assigned →
    match a.trail[i]!.reason with
    | none => m.solver.reason m.solver.trail[i]! = 0
    | some clause => ∃ entry ∈ w.entries,
        entry.id = m.solver.reason m.solver.trail[i]! ∧ entry.view = clause
  /-- watch 引用及物理链接满足统一表示关系。 -/
  watches : WatchRepresentation m.solver w
  /-- 具体 MTF 链表与见证变量顺序一致。 -/
  order : OrderRepresentation m.solver w.order

/-- 逻辑数据库的标准 CNF 视图被满足，当且仅当列表中每个子句都被满足。 -/
theorem databaseView_sat_iff (clauses : List Clause) (a : Assignment) :
    Std.Sat.CNF.Sat a (databaseView clauses) ↔
      ∀ clause ∈ clauses, Std.Sat.CNF.Clause.Sat a clause := by
  simp [Std.Sat.CNF.sat_iff_all_mem_sat, databaseView, Std.Sat.CNF.Internal.mem_iff]

end MicrosatLean.Verification
