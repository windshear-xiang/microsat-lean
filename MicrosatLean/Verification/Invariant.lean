import MicrosatLean.Verification.Model

/-! 本文件中的 invariant 只陈述当前状态的性质，不预设未来 preservation、成功返回或 termination。
Certificate 将 semantic meaning、具体存储与控制事实、以及 progress 所需事实分开。
history 谓词描述仍保留的 decision prefixes，是证明信息，不是运行时保存的一份历史 machine 列表。
-/

namespace MicrosatLean.Verification

/-- 保持输入与数据库的语义联系、trail 一致性和 reason 顺序。
原始数据库与输入等价，learned clauses 被输入蕴含；reason 尾部的假值见证来自更早的 trail。
root literals 无需 decision assumptions 即被输入蕴含；非 root decisions 仅是当前搜索分支的假设。
-/
structure SemanticInv (input : CNF) (a : LogicalState) : Prop where
  /-- 输入与逻辑原始数据库互相蕴含。 -/
  original : Std.Sat.CNF.BiEntails input (databaseView a.original)
  /-- 输入蕴含当前 learned 数据库。 -/
  learned : Std.Sat.CNF.Entails input (databaseView a.learned)
  /-- root 前缀不超过当前 trail。 -/
  rootBound : a.rootSize ≤ a.trail.length
  /-- 活动赋值数量不超过变量上界。 -/
  trailBound : a.trail.length ≤ a.numVars
  /-- 所有 trail literals 都在声明的内部变量范围内。 -/
  declaredTrail : ∀ lit ∈ a.trueTrail, LiteralBound a.numVars lit
  /-- 每个变量在 trail 上至多出现一次。 -/
  distinct : (a.trueTrail.map Prod.fst).Nodup
  /-- 当前数据库的每个 literal 都在内部变量范围内。 -/
  declaredClauses : ∀ clause ∈ a.database, ∀ lit ∈ clause, LiteralBound a.numVars lit
  /-- 正常运行的数据库不包含空 clause。 -/
  nonempty : ∀ clause ∈ a.database, clause.literals ≠ []
  /-- reason 被输入蕴含、head 对应本次真 literal，且 tails 在更早的 prefix 上已为假。 -/
  reasons : ∀ i, i < a.trail.length → ∀ clause,
    a.trail[i]!.reason = some clause →
      Std.Sat.CNF.EntailsClause input clause ∧
      clause.literals.head? = some a.trail[i]!.literal ∧
      ∀ lit ∈ clause.literals.tail, FalseIn (prefixLiterals a i) lit
  /-- root prefix 的每个 literal 在输入的所有 models 中均为真。 -/
  roots : ∀ lit ∈ prefixLiterals a a.rootSize,
    ∀ valuation, Std.Sat.CNF.Sat valuation input → valuation lit.1 = lit.2

/-- 每个仍存活的非 root decision 边界之前，当前数据库在对应 trail prefix 上满足 unit closure。
新 learned clauses 也必须满足这个历史前缀性质，其成立性由实现证明给出。
-/
def DecisionHistory (a : LogicalState) : Prop :=
  ∀ i, a.rootSize ≤ i → i < a.trail.length → a.trail[i]!.reason = none →
    ∀ clause ∈ a.database, UnitClosed (prefixLiterals a i) clause

/-- 编码 literal 在前 count 个逻辑 trail 项确定的赋值下为假。 -/
def FalseBefore (a : LogicalState) (count : Nat) (lit : Lit) : Prop :=
  FalseIn (prefixLiterals a count) (literalView lit)

/-- 编码 literal 在前 count 个逻辑 trail 项确定的赋值下为真。 -/
def TrueBefore (a : LogicalState) (count : Nat) (lit : Lit) : Prop :=
  TrueIn (prefixLiterals a count) (literalView lit)

/-- 给定 clause 中被扫描的 watched literal，取另一个 watched literal。 -/
def otherWatch (entry : StoredClause) (lit : Lit) : Lit :=
  if entry.lits[0]! == lit then entry.lits[1]! else entry.lits[0]!

/-- watch reference 所属 clause 的另一个 watch，在指定 trail prefix 下已为真。 -/
def SettledWatch (a : LogicalState) (w : RepresentationWitness)
    (count : Nat) (lit : Lit) (ref : Nat) : Prop :=
  ∀ entry ∈ w.entries, CDCL.watchClause ref = entry.id →
    TrueBefore a count (otherWatch entry lit)

/-- 已处理的每个假 literal，其 watch clauses 都已有为真的另一个 watch 作为满足性见证。
该真值见证可以位于整个活动 trail 中，包括尚待传播的赋值。
-/
def SettledPrefix (a : LogicalState) (w : RepresentationWitness) (count : Nat) : Prop :=
  ∀ lit, FalseBefore a count lit → ∀ ref ∈ w.heads lit,
    SettledWatch a w a.trail.length lit ref

/-- 当前 watch list 中已访问、且不在 remaining 里的 references 都已 settled。 -/
def SettledCursor (a : LogicalState) (w : RepresentationWitness)
    (lit : Lit) (remaining : List Nat) : Prop :=
  ∀ ref ∈ w.heads lit, ref ∉ remaining → SettledWatch a w a.trail.length lit ref

/-- 在每个仍保留的 decision prefix 上，已为假的 literals 的 watch clauses 均具有该 prefix 内的真值见证。 -/
def SavedWatches (a : LogicalState) (w : RepresentationWitness) : Prop :=
  ∀ i, a.rootSize ≤ i → i < a.trail.length → a.trail[i]!.reason = none →
    ∀ lit, FalseBefore a i lit → ∀ ref ∈ w.heads lit, SettledWatch a w i lit ref

/-- remaining 恰好位于已访问前缀之后；previous = 0 时表示尚未访问、cursor 仍在链头。 -/
def WatchCursor (w : RepresentationWitness) (lit : Lit) (previous : Nat)
    (remaining : List Nat) : Prop :=
  (previous = 0 ∧ remaining = w.heads lit) ∨
    ∃ visited, w.heads lit = visited ++ previous :: remaining

/-- 指定变量已经在逻辑 trail 上获得赋值。 -/
def Assigned (a : LogicalState) (var : Nat) : Prop := ∃ lit ∈ a.trueTrail, lit.1 = var

/-- cursor 对应 MTF order 的某个位置，且该位置之前的变量均已赋值；末端以 0 表示。 -/
def DecisionCursor (a : LogicalState) (w : RepresentationWitness) (cursor : Nat) : Prop :=
  ∃ position, position ≤ w.order.length ∧ cursor = w.order.getD position 0 ∧
    ∀ i, i < position → Assigned a (w.order.getD i 0)

/-- 每个非 root trail 项之前，都存在一个覆盖其位置的非 root decision 边界。 -/
def LevelCover (a : LogicalState) : Prop :=
  ∀ i, a.rootSize ≤ i → i < a.trail.length →
    ∃ decision, a.rootSize ≤ decision ∧ decision ≤ i ∧ a.trail[decision]!.reason = none

/-- 活动 trail 上 tag 为 6 的项全部位于 forced root 前缀。 -/
def SixBefore (s : CDCL.State) : Prop :=
  ∀ i, i < s.assigned → s.mark s.trail[i]! = 6 → i < s.forced

/-- 存在真实的非 root trail 后缀，同时具备 decision-level 覆盖和 tag 6 的 root 边界事实。 -/
def NonrootMode (m : CDCL.Machine) (a : LogicalState) : Prop :=
  a.rootSize < a.trail.length ∧ LevelCover a ∧ SixBefore m.solver

/-- 活动 watch 阶段的模式要求：root 模式下全部活动项标为 6；非 root 模式下存在真实 decision 后缀。 -/
def PropagationMode (m : CDCL.Machine) (a : LogicalState) : Prop :=
  (m.root = true → ∀ i, i < m.solver.assigned → m.solver.mark m.solver.trail[i]! = 6) ∧
  (m.root = false → NonrootMode m a)

/-- nextLiteral 空闲阶段允许 root = false 且 trail 只有 root 前缀。
活动 watch 阶段不能直接采用这一放宽，因为非 root 冲突分支需要真实 decision level。
该区分刻画可达控制状态，不限制合法输入或 Config。
-/
def NextMode (m : CDCL.Machine) (a : LogicalState) : Prop :=
  (m.root = true → ∀ i, i < m.solver.assigned → m.solver.mark m.solver.trail[i]! = 6) ∧
  (m.root = false → a.trail.length = a.rootSize ∨ NonrootMode m a)

/-- 进入 beginPropagation 的两种实际来源：初始 root units，或刚追加的一次 reason-free decision。 -/
def BeginEvidence (m : CDCL.Machine) (a : LogicalState) : Prop :=
  (m.solver.processed = 0 ∧ m.solver.forced = 0 ∧
    ∀ i, i < m.solver.assigned → m.solver.mark m.solver.trail[i]! = 6 ∧
      m.solver.reason m.solver.trail[i]! ≠ 0) ∨
  (NonrootMode m a ∧ m.solver.processed + 1 = m.solver.assigned ∧
    m.solver.reason m.solver.trail[m.solver.processed]! = 0)

/-- 按 Machine.phase 规定当前模式、cursor、已处理前缀和待传播 literal 的对应关系。 -/
def PhaseInv (m : CDCL.Machine) (a : LogicalState) (w : RepresentationWitness) : Prop :=
  match m.phase with
  | .beginPropagation => BeginEvidence m a ∧ DecisionCursor a w m.decision ∧
      m.oldLemmas = 0 ∧ m.root = false ∧ m.currentLit = 0 ∧ m.previousWatch = 0 ∧
      SettledPrefix a w m.solver.processed
  | .nextLiteral => NextMode m a ∧ m.currentLit = 0 ∧ m.previousWatch = 0 ∧
      SettledPrefix a w m.solver.processed
  | .watch => PropagationMode m a ∧ 0 < m.solver.processed ∧
      m.currentLit = m.solver.trail[m.solver.processed - 1]! ∧
      ∃ remaining, WatchCursor w m.currentLit m.previousWatch remaining ∧
        SettledCursor a w m.currentLit remaining ∧ SettledPrefix a w (m.solver.processed - 1)
  | .choose => m.solver.processed = m.solver.assigned ∧ m.currentLit = 0 ∧ m.previousWatch = 0 ∧
      LevelCover a ∧ SixBefore m.solver ∧ SettledPrefix a w m.solver.processed

/-- 控制侧 invariant：decision history、saved watches、unit 真值、游标、计数、mark tags 和各 phase 的事实。 -/
structure ControlInv (input : CNF) (m : CDCL.Machine) (a : LogicalState)
    (w : RepresentationWitness) : Prop where
  /-- 保留每个 decision prefix 的 unit closure 事实。 -/
  history : DecisionHistory a
  /-- 保留 decision prefixes 上的 watch 真值见证。 -/
  saved : SavedWatches a w
  /-- 数据库中每个 unit clause 的 literal 已在活动 trail 上为真。 -/
  units : ∀ clause ∈ a.database, clause.literals.length = 1 →
    ∀ lit ∈ clause, TrueIn a.trueTrail lit
  /-- 没有新学习事件时，原 decision cursor 仍覆盖已访问变量。 -/
  cursor : m.solver.nLemmas ≤ m.oldLemmas → DecisionCursor a w m.decision
  /-- 本次 propagation 保存的旧计数不超过当前 learned 计数。 -/
  oldCount : m.oldLemmas ≤ m.solver.nLemmas
  /-- 活动具体 trail 的 marks 只采用算法认可的非零 tags。 -/
  tags : ∀ i, i < m.solver.assigned →
    let tag := m.solver.mark m.solver.trail[i]!
    tag = 1 ∨ tag = 2 ∨ tag = 5 ∨ tag = 6
  /-- 标记为 6 的活动项在输入的所有 models 中成立。 -/
  rootTags : ∀ i, i < a.trail.length → m.solver.mark m.solver.trail[i]! = 6 →
    ∀ valuation, Std.Sat.CNF.Sat valuation input →
      valuation a.trail[i]!.literal.1 = a.trail[i]!.literal.2
  /-- forced root 前缀中的每项都具有 tag 6。 -/
  rootPrefix : ∀ i, i < m.solver.forced → m.solver.mark m.solver.trail[i]! = 6
  /-- 当前 phase 满足对应的模式、游标与传播前缀要求。 -/
  phase : PhaseInv m a w

/-- 按变量编号构造 clause 的规范 key，每个变量取不出现、正 polarity 或负 polarity。
key 不依赖 literal 的排列，用于有限 clause space 与 learned freshness 的证明。
-/
def canonicalKey (variables : Nat) (clause : Clause) : List (Option Bool) :=
  (List.range variables).map fun i =>
    if (i + 1, true) ∈ clause then some true
    else if (i + 1, false) ∈ clause then some false else none

/-- termination 所需的当前数据库性质：clause 规范化，以及保留 learned clauses 的 canonical keys 不重复。 -/
structure ProgressInv (a : LogicalState) : Prop where
  /-- 每个 clause 内 literal 不重复，变量也不重复，因此不存在互补对。 -/
  normalized : ∀ clause ∈ a.database, clause.literals.Nodup ∧
    (clause.literals.map Prod.fst).Nodup
  /-- 当前保留 learned clauses 的规范 keys 两两不同。 -/
  distinctLearned : (a.learned.map (canonicalKey a.numVars)).Nodup

/-- 针对同一个 logical state 和 representation witness 汇总全部 invariant。
内部变量数固定为初始化器选择的 max 1 numVars，因此也覆盖零变量输入。
-/
structure Certificate (formula : Formula) (m : CDCL.Machine)
    (a : LogicalState) (w : RepresentationWitness) : Prop where
  /-- 原始 Formula 通过变量边界规格。 -/
  input : WellFormed formula
  /-- 逻辑变量数采用真实初始化器的 padding 规则。 -/
  variables : a.numVars = max 1 formula.numVars
  /-- 具体 machine 精确表示这个 logical state 与 witness。 -/
  representation : Rep m a w
  /-- 当前逻辑状态满足语义 invariant。 -/
  semantic : SemanticInv (formulaView formula) a
  /-- 当前 machine 满足控制与 history invariant。 -/
  control : ControlInv (formulaView formula) m a w
  /-- 当前数据库满足有限进展所需的 invariant。 -/
  progress : ProgressInv a

/-- 存在某个逻辑状态与共享 witness，使当前具体 Machine 满足完整 Certificate。 -/
def Inv (formula : Formula) (m : CDCL.Machine) : Prop :=
  ∃ a w, Certificate formula m a w

/-- 从初始化后的 solver state 建立初始 machine：decision cursor 指向 MTF head，其余控制字段用默认值。 -/
def InitialMachine (s : CDCL.State) : CDCL.Machine := { solver := s, decision := s.head }

end MicrosatLean.Verification
