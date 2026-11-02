import MicrosatLean.Verification.Model

namespace MicrosatLean.Verification

/-!
审查时需要检查谓词的实际内容，而不仅是名称。这里没有任何谓词直接断言未来的
preservation、成功执行或 termination。`Certificate` 将逻辑语义、当前存储及控制事实、
进展所需事实分开。历史条件只描述保留的 decision 前缀，属于证明信息，
并不是在运行时复制旧机器。
-/

/-- 逻辑语义 invariant：原始子句等价于输入，学习子句由输入蕴含，trail 和 reason 良构。
reason 的尾部文字必须在其 head 之前已为假；root 项还必须无需 decision 假设就由输入推出。 -/
structure SemanticInv (input : CNF) (a : LogicalState) : Prop where
  /-- 规范化后的原始数据库与输入具有完全相同的模型。 -/
  original : Std.Sat.CNF.BiEntails input (databaseView a.original)
  /-- 输入蕴含每个保留的学习子句。 -/
  learned : Std.Sat.CNF.Entails input (databaseView a.learned)
  /-- root 前缀不超过活动 trail 长度。 -/
  rootBound : a.rootSize ≤ a.trail.length
  /-- 活动 trail 长度不超过内部变量数。 -/
  trailBound : a.trail.length ≤ a.numVars
  /-- trail 中每个文字的变量编号都在合法范围内。 -/
  declaredTrail : ∀ lit ∈ a.trueTrail, LiteralBound a.numVars lit
  /-- trail 中每个变量至多赋值一次。 -/
  distinct : (a.trueTrail.map Prod.fst).Nodup
  /-- 数据库中所有文字的变量编号都在合法范围内。 -/
  declaredClauses : ∀ clause ∈ a.database, ∀ lit ∈ clause, LiteralBound a.numVars lit
  /-- 正常运行时数据库只保留非空子句；空子句由初始化或终态处理。 -/
  nonempty : ∀ clause ∈ a.database, clause.literals ≠ []
  /-- 传播 reason 由输入蕴含，以该项真文字为 head，且尾部文字在更早的 trail 前缀中为假。 -/
  reasons : ∀ i, i < a.trail.length → ∀ clause,
    a.trail[i]!.reason = some clause →
      Std.Sat.CNF.EntailsClause input clause ∧
      clause.literals.head? = some a.trail[i]!.literal ∧
      ∀ lit ∈ clause.literals.tail, FalseIn (prefixLiterals a i) lit
  /-- root 前缀的每项赋值都由输入自身蕴含，无需 decision 假设。 -/
  roots : ∀ lit ∈ prefixLiterals a a.rootSize,
    ∀ valuation, Std.Sat.CNF.Sat valuation input → valuation lit.1 = lit.2

/-- 每个保留的非 root decision 之前，所有当前数据库子句都满足 unit closure。
新学习子句也必须满足这些历史条件；建立该事实属于实现证明的 obligation。 -/
def DecisionHistory (a : LogicalState) : Prop :=
  ∀ i, a.rootSize ≤ i → i < a.trail.length → a.trail[i]!.reason = none →
    ∀ clause ∈ a.database, UnitClosed (prefixLiterals a i) clause

/-- 内部编码文字在逻辑 trail 的指定前缀内已经为假。 -/
def FalseBefore (a : LogicalState) (count : Nat) (lit : Lit) : Prop :=
  FalseIn (prefixLiterals a count) (literalView lit)

/-- 内部编码文字在逻辑 trail 的指定前缀内已经为真。 -/
def TrueBefore (a : LogicalState) (count : Nat) (lit : Lit) : Prop :=
  TrueIn (prefixLiterals a count) (literalView lit)

/-- 给定一个被观察文字，读取该子句前两个位置中的另一个 watch 文字。 -/
def otherWatch (entry : StoredClause) (lit : Lit) : Lit :=
  if entry.lits[0]! == lit then entry.lits[1]! else entry.lits[0]!

/-- 某个 watch 已处理妥当：其所属子句的另一个 watch 在指定 trail 前缀中为真。 -/
def SettledWatch (a : LogicalState) (w : RepresentationWitness)
    (count : Nat) (lit : Lit) (ref : Nat) : Prop :=
  ∀ entry ∈ w.entries, CDCL.watchClause ref = entry.id →
    TrueBefore a count (otherWatch entry lit)

/-- 对已经处理过的假文字，每个 watch 都有另一个为真的 watch 作为见证。
见证可以来自活动 trail 中任意已赋值项，包括尚待传播的项。 -/
def SettledPrefix (a : LogicalState) (w : RepresentationWitness) (count : Nat) : Prop :=
  ∀ lit, FalseBefore a count lit → ∀ ref ∈ w.heads lit,
    SettledWatch a w a.trail.length lit ref

/-- 当前 watch 链表中已经访问过的条目都有真文字见证；未访问部分由 `remaining` 指定。 -/
def SettledCursor (a : LogicalState) (w : RepresentationWitness)
    (lit : Lit) (remaining : List Nat) : Prop :=
  ∀ ref ∈ w.heads lit, ref ∉ remaining → SettledWatch a w a.trail.length lit ref

/-- 每个保留 decision 之前，相关 watch 的真文字见证已经位于当时的前缀内，供 backjump 恢复使用。 -/
def SavedWatches (a : LogicalState) (w : RepresentationWitness) : Prop :=
  ∀ i, a.rootSize ≤ i → i < a.trail.length → a.trail[i]!.reason = none →
    ∀ lit, FalseBefore a i lit → ∀ ref ∈ w.heads lit, SettledWatch a w i lit ref

/-- watch 游标精确位于已访问前缀之后；`previous = 0` 时尚未访问任何条目。 -/
def WatchCursor (w : RepresentationWitness) (lit : Lit) (previous : Nat)
    (remaining : List Nat) : Prop :=
  (previous = 0 ∧ remaining = w.heads lit) ∨
    ∃ visited, w.heads lit = visited ++ previous :: remaining

/-- 指定变量已经在逻辑 trail 中出现并获得赋值。 -/
def Assigned (a : LogicalState) (var : Nat) : Prop := ∃ lit ∈ a.trueTrail, lit.1 = var

/-- decision 游标对应 MTF 顺序中的一个位置，并且它之前的所有变量均已赋值。 -/
def DecisionCursor (a : LogicalState) (w : RepresentationWitness) (cursor : Nat) : Prop :=
  ∃ position, position ≤ w.order.length ∧ cursor = w.order.getD position 0 ∧
    ∀ i, i < position → Assigned a (w.order.getD i 0)

/-- 对每个非 root trail 项，都有一个不晚于它的非 root decision，作为该 decision level 的起点。 -/
def LevelCover (a : LogicalState) : Prop :=
  ∀ i, a.rootSize ≤ i → i < a.trail.length →
    ∃ decision, a.rootSize ≤ decision ∧ decision ≤ i ∧ a.trail[decision]!.reason = none

/-- 活动 trail 中标记为 6 的项都位于已确认的 root 前缀中。 -/
def SixBefore (s : CDCL.State) : Prop :=
  ∀ i, i < s.assigned → s.mark s.trail[i]! = 6 → i < s.forced

/-- 非 root 模式下的结构条件：存在非 root trail，每个非 root 项有 decision 起点，且标记 6 只出现在 root 前缀。 -/
def NonrootMode (m : CDCL.Machine) (a : LogicalState) : Prop :=
  a.rootSize < a.trail.length ∧ LevelCover a ∧ SixBefore m.solver

/-- 传播模式条件：root 模式下全部活动项标记为 6；非 root 模式下 trail 只有 root 前缀或满足非 root 条件。 -/
def PropagationMode (m : CDCL.Machine) (a : LogicalState) : Prop :=
  (m.root = true → ∀ i, i < m.solver.assigned → m.solver.mark m.solver.trail[i]! = 6) ∧
  (m.root = false → a.trail.length = a.rootSize ∨ NonrootMode m a)

/-- 进入 propagation 的两种依据：初始 root 传播，或刚加入且尚未处理的新 decision。 -/
def BeginEvidence (m : CDCL.Machine) (a : LogicalState) : Prop :=
  (m.solver.processed = 0 ∧ m.solver.forced = 0 ∧
    ∀ i, i < m.solver.assigned → m.solver.mark m.solver.trail[i]! = 6 ∧
      m.solver.reason m.solver.trail[i]! ≠ 0) ∨
  (NonrootMode m a ∧ m.solver.processed + 1 = m.solver.assigned ∧
    m.solver.reason m.solver.trail[m.solver.processed]! = 0)

/-- 按当前执行阶段规定传播前缀、模式、decision 游标和 watch 游标应满足的条件。 -/
def PhaseInv (m : CDCL.Machine) (a : LogicalState) (w : RepresentationWitness) : Prop :=
  match m.phase with
  | .beginPropagation => BeginEvidence m a ∧ DecisionCursor a w m.decision ∧
      m.oldLemmas = 0 ∧ m.root = false ∧ m.currentLit = 0 ∧ m.previousWatch = 0 ∧
      SettledPrefix a w m.solver.processed
  | .nextLiteral => PropagationMode m a ∧ m.currentLit = 0 ∧ m.previousWatch = 0 ∧
      SettledPrefix a w m.solver.processed
  | .watch => PropagationMode m a ∧ 0 < m.solver.processed ∧
      m.currentLit = m.solver.trail[m.solver.processed - 1]! ∧
      ∃ remaining, WatchCursor w m.currentLit m.previousWatch remaining ∧
        SettledCursor a w m.currentLit remaining ∧ SettledPrefix a w (m.solver.processed - 1)
  | .choose => m.solver.processed = m.solver.assigned ∧ m.currentLit = 0 ∧ m.previousWatch = 0 ∧
      LevelCover a ∧ SixBefore m.solver ∧ SettledPrefix a w m.solver.processed

/-- 控制 invariant：保留 decision 历史、watch 见证、unit 真值、计数器和标记含义，并满足当前阶段条件。 -/
structure ControlInv (input : CNF) (m : CDCL.Machine) (a : LogicalState)
    (w : RepresentationWitness) : Prop where
  /-- 保留各 decision 边界上的 unit closure 历史条件。 -/
  history : DecisionHistory a
  /-- 保留各 decision 边界之前的 watch 真文字见证。 -/
  saved : SavedWatches a w
  /-- 数据库中的每个 unit 子句，其文字都已经在 trail 中为真。 -/
  units : ∀ clause ∈ a.database, clause.literals.length = 1 →
    ∀ lit ∈ clause, TrueIn a.trueTrail lit
  /-- 没有待处理的 learning 增量时，decision 游标之前的变量均已赋值。 -/
  cursor : m.solver.nLemmas ≤ m.oldLemmas → DecisionCursor a w m.decision
  /-- 记录的旧学习子句数不超过当前数量。 -/
  oldCount : m.oldLemmas ≤ m.solver.nLemmas
  /-- 活动 trail 只使用约定的非零标记 1、2、5、6。 -/
  tags : ∀ i, i < m.solver.assigned →
    let tag := m.solver.mark m.solver.trail[i]!
    tag = 1 ∨ tag = 2 ∨ tag = 5 ∨ tag = 6
  /-- 标记为 6 的活动项所表达的真文字由输入蕴含。 -/
  rootTags : ∀ i, i < a.trail.length → m.solver.mark m.solver.trail[i]! = 6 →
    ∀ valuation, Std.Sat.CNF.Sat valuation input →
      valuation a.trail[i]!.literal.1 = a.trail[i]!.literal.2
  /-- 已确认的 root 前缀项全部具有标记 6。 -/
  rootPrefix : ∀ i, i < m.solver.forced → m.solver.mark m.solver.trail[i]! = 6
  /-- 当前具体阶段满足对应的局部控制条件。 -/
  phase : PhaseInv m a w

/-- 为每个声明变量记录缺席、正极性或负极性，得到与子句文字次序无关的 key。
同时出现正负极性的情形由规范化 invariant 排除。 -/
def canonicalKey (variables : Nat) (clause : Clause) : List (Option Bool) :=
  (List.range variables).map fun i =>
    if (i + 1, true) ∈ clause then some true
    else if (i + 1, false) ∈ clause then some false else none

/-- 进展证明所需的静态事实：子句中变量不重复，当前保留学习子句的 canonical key 两两不同。 -/
structure ProgressInv (a : LogicalState) : Prop where
  /-- 数据库中的每个子句既无重复文字，也无重复变量，因而没有互补文字对。 -/
  normalized : ∀ clause ∈ a.database, clause.literals.Nodup ∧
    (clause.literals.map Prod.fst).Nodup
  /-- 当前保留的学习子句具有两两不同的 canonical key。 -/
  distinctLearned : (a.learned.map (canonicalKey a.numVars)).Nodup

/-- 一次状态的完整证书，组合输入范围、变量数、representation、语义、控制和进展事实。
内部变量数固定为真实初始化器使用的 `max 1 numVars`，也覆盖声明变量数为 0 的情况。 -/
structure Certificate (formula : Formula) (m : CDCL.Machine)
    (a : LogicalState) (w : RepresentationWitness) : Prop where
  /-- 原始输入满足公开的变量范围 specification。 -/
  input : WellFormed formula
  /-- 逻辑内部变量数遵循真实初始化器的最小容量约定。 -/
  variables : a.numVars = max 1 formula.numVars
  /-- 具体存储与逻辑状态、共享见证一致。 -/
  representation : Rep m a w
  /-- 逻辑状态满足输入相关的语义 invariant。 -/
  semantic : SemanticInv (formulaView formula) a
  /-- 具体执行阶段、历史、watch 和标记满足控制 invariant。 -/
  control : ControlInv (formulaView formula) m a w
  /-- 逻辑数据库具有进展计数所需的规范化和新鲜性事实。 -/
  progress : ProgressInv a

/-- 具体机器满足 invariant：存在逻辑状态与共享表示见证，使完整证书成立。 -/
def Inv (formula : Formula) (m : CDCL.Machine) : Prop :=
  ∃ a w, Certificate formula m a w

/-- 将实际初始化状态包装成搜索机器，decision 游标从 MTF 链表头开始。 -/
def InitialMachine (s : CDCL.State) : CDCL.Machine := { solver := s, decision := s.head }

end MicrosatLean.Verification
