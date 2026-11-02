import MicrosatLean.CDCL.Search
import Std.Sat.CNF

/-! 验证边界是变量编号有界的 Formula。literal、clause 和 formula 的 view 连接到 Std.Sat.CNF，
并保留原始子句中的重复项、空子句和 tautology；normalization 的正确性属于初始化证明。
SAT 要返回覆盖声明变量的有效 model，UNSAT 要排除标准 CNF 语义下的全部 assignment。
统计信息、DIMACS 字节解析和文件 IO 不属于这里的 functional correctness claim。
-/

namespace MicrosatLean.Verification

/-- 标准语义中的 total assignment：为任意自然数变量给出 Bool 值。 -/
abbrev Assignment := Nat → Bool
/-- 直接复用 Std.Sat 的 literal 类型，以变量编号和 polarity 表示正负项。 -/
abbrev Literal := Std.Sat.Literal Nat
/-- 直接复用 Std.Sat.CNF.Clause，不再单独定义另一套 clause 语义。 -/
abbrev Clause := Std.Sat.CNF.Clause Nat
/-- 直接复用以 Nat 为变量类型的 Std.Sat.CNF。 -/
abbrev CNF := Std.Sat.CNF Nat

/-- 把内部偶数/奇数 literal 编码解释为标准 literal；偶数对应正 polarity。 -/
def literalView (lit : Lit) : Literal := (lit.var, lit % 2 == 0)

/-- 逐项翻译可执行 clause 的 literals，得到标准 clause；此处不做 normalization。 -/
def clauseView (clause : Array Lit) : Clause :=
  .ofLiterals (clause.toList.map literalView)

/-- 把原始 Formula 的每个 clause 翻译成标准 CNF，作为最终 specification 的输入语义。 -/
def formulaView (formula : Formula) : CNF :=
  ⟨formula.clauses.map clauseView⟩

/-- 将有限 model 数组解释成 total assignment；数组范围之外的变量取 false。 -/
def assignment (model : Array Bool) : Assignment := fun var => model.getD var false

/-- 一个可执行 clause 中的变量编号都为正且不超过给定上界；供 normalization 等证明复用。 -/
def ClauseWellFormed (variables : Nat) (clause : Array Lit) : Prop :=
  ∀ lit ∈ clause, 0 < lit.var ∧ lit.var ≤ variables

/-- 输入 Formula 的每个 literal 都使用声明范围 1..numVars 内的变量。 -/
def WellFormed (formula : Formula) : Prop :=
  ∀ clause ∈ formula.clauses, ∀ lit ∈ clause,
    0 < lit.var ∧ lit.var ≤ formula.numVars

/-- 把命题式输入前提 WellFormed 与实际执行的 Bool 边界检查对应起来。 -/
theorem wellFormed_iff_check (formula : Formula) :
    WellFormed formula ↔ formula.wellFormed = true := by
  simp only [WellFormed, Formula.wellFormed, Array.all_eq_true]
  constructor
  · intro valid i hi j hj
    exact decide_eq_true (valid _ (Array.getElem_mem hi) _ (Array.getElem_mem hj))
  · intro checked clause member lit contained
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp member
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp contained
    exact of_decide_eq_true (checked i hi j hj)

/-- 通过已有的有限 Bool 检查判定 WellFormed；证明部分把检查结果翻译回命题。 -/
instance (formula : Formula) : Decidable (WellFormed formula) :=
  if checked : formula.wellFormed = true then
    isTrue ((wellFormed_iff_check formula).mpr checked)
  else
    isFalse (fun valid => checked ((wellFormed_iff_check formula).mp valid))

/-- model 数组覆盖所有声明变量；由于索引 0 保留，数组长度必须严格大于变量上界。 -/
def Covers (model : Array Bool) (variables : Nat) : Prop := variables < model.size

/-- assignment 满足原始输入的标准 CNF view。 -/
def Models (formula : Formula) (a : Assignment) : Prop :=
  Std.Sat.CNF.Sat a (formulaView formula)

/-- 原始输入在标准 CNF 语义下蕴含给定的可执行 clause。 -/
def EntailsClause (formula : Formula) (clause : Array Lit) : Prop :=
  Std.Sat.CNF.EntailsClause (formulaView formula) (clauseView clause)

/-- 最终功能规格：SAT model 覆盖声明变量并满足原始输入；UNSAT 排除所有 assignment。
返回的统计信息不属于该 correctness claim。
-/
def ValidResult (formula : Formula) : CDCL.SolveResult → Prop
  | .sat model _ => Covers model formula.numVars ∧ Models formula (assignment model)
  | .unsat _ => Std.Sat.CNF.Unsat (formulaView formula)

/-- 标准 clause view 的 literal 列表恰好是原始数组逐项翻译后的结果。 -/
theorem clauseView_literals (clause : Array Lit) :
    (clauseView clause).literals = clause.toList.map literalView := by
  simp [clauseView]

/-- 标准 view 中的 literal 成员关系，等价于它来自原数组中的某个编码项。 -/
theorem clauseView_mem {lit : Literal} {clause : Array Lit} :
    lit ∈ clauseView clause ↔ ∃ encoded ∈ clause, literalView encoded = lit := by
  simp [← Std.Sat.CNF.Clause.mem_literals_iff, clauseView_literals]

/-- 标准 clause 的满足性等价于：原数组里至少有一个 literal 在 assignment 下为真。 -/
theorem clauseView_sat_iff (clause : Array Lit) (a : Assignment) :
    Std.Sat.CNF.Clause.Sat a (clauseView clause) ↔
      ∃ lit ∈ clause, a lit.var = (lit % 2 == 0) := by
  rw [Std.Sat.CNF.Clause.sat_iff_exists_mem_eq]
  constructor
  · rintro ⟨lit, member, truth⟩
    obtain ⟨encoded, contained, rfl⟩ := clauseView_mem.mp member
    exact ⟨encoded, contained, truth⟩
  · rintro ⟨lit, contained, truth⟩
    exact ⟨literalView lit, clauseView_mem.mpr ⟨lit, contained, rfl⟩, truth⟩

/-- 展开整份输入的标准满足性：每个原始 clause 都存在一个为真的 literal。 -/
theorem models_iff (formula : Formula) (a : Assignment) :
    Models formula a ↔ ∀ clause ∈ formula.clauses,
      ∃ lit ∈ clause, a lit.var = (lit % 2 == 0) := by
  simp only [Models, Std.Sat.CNF.sat_iff_all_mem_sat, formulaView]
  constructor
  · intro satisfied clause member
    exact (clauseView_sat_iff clause a).mp
      (satisfied _ (Array.mem_map.mpr ⟨clause, member, rfl⟩))
  · intro satisfied clause member
    obtain ⟨encoded, contained, rfl⟩ := Array.mem_map.mp member
    exact (clauseView_sat_iff encoded a).mpr (satisfied encoded contained)

/-- 编码层的取补与标准 literal 的取补相容；先取补再翻译与先翻译再取补相同。 -/
@[simp] theorem literalView_negate (lit : Lit) :
    literalView lit.negate = (literalView lit).negate := by
  have remainder : (lit ^^^ 1) % 2 = lit % 2 ^^^ 1 := by
    simpa using (Nat.xor_mod_two_pow (a := lit) (b := 1) (n := 1))
  apply Prod.ext
  · simp [literalView, Lit.negate, Lit.var, Nat.xor_div_two, Std.Sat.Literal.negate]
  · rcases Nat.mod_two_eq_zero_or_one lit with even | odd
    · simp [literalView, Lit.negate, Std.Sat.Literal.negate, remainder, even]
    · simp [literalView, Lit.negate, Std.Sat.Literal.negate, remainder, odd]

/-- 对合法 Formula，可执行 model checker 返回 true 当且仅当对应 assignment 满足标准 CNF。 -/
theorem satisfiedBy_iff_models {formula : Formula} (valid : WellFormed formula)
    (model : Array Bool) : formula.satisfiedBy model = true ↔ Models formula (assignment model) := by
  rw [models_iff]
  simp only [Formula.satisfiedBy, Array.all_eq_true_iff_forall_mem,
    Array.any_eq_true]
  have literal (clause : Array Lit) (member : clause ∈ formula.clauses)
      (lit : Lit) (contained : lit ∈ clause) :
      lit.satisfiedBy model = true ↔ assignment model lit.var = (lit % 2 == 0) := by
    have nonzero : lit ≠ 0 := by
      intro zero
      have positive := (valid clause member lit contained).1
      simp [zero, Lit.var] at positive
    simp [Lit.satisfiedBy, nonzero, assignment, Array.getElem!_eq_getD]
  constructor
  · intro checked clause member
    obtain ⟨i, hi, truth⟩ := checked clause member
    exact ⟨clause[i], Array.getElem_mem hi,
      (literal clause member clause[i] (Array.getElem_mem hi)).mp truth⟩
  · intro satisfied clause member
    obtain ⟨lit, contained, truth⟩ := satisfied clause member
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp contained
    exact ⟨i, hi, (literal clause member clause[i] (Array.getElem_mem hi)).mpr truth⟩

/-- 把 total assignment 限制成索引 0..variables 的有限数组；保留未出现在 clauses 中的声明变量。 -/
def modelOfAssignment (variables : Nat) (a : Assignment) : Array Bool :=
  Array.ofFn fun i : Fin (variables + 1) => a i.val

/-- 从 total assignment 构造的有限 model 一定覆盖给定变量上界。 -/
@[simp] theorem modelOfAssignment_covers (variables : Nat) (a : Assignment) :
    Covers (modelOfAssignment variables a) variables := by
  simp [Covers, modelOfAssignment]

/-- 在声明范围内，从有限 model 读回的 assignment 与原 total assignment 一致。 -/
theorem assignment_modelOfAssignment {variables var : Nat} (a : Assignment)
    (bound : var ≤ variables) : assignment (modelOfAssignment variables a) var = a var := by
  unfold assignment
  rw [← Array.getElem_eq_getD (h := by simpa [modelOfAssignment] using Nat.lt_succ_of_le bound)]
  simp [modelOfAssignment]

/-- 合法 Formula 只使用声明范围内的变量，因此把 total assignment 限制为有限 model 不改变满足性。 -/
theorem models_restrict {formula : Formula} (valid : WellFormed formula) (a : Assignment) :
    Models formula (assignment (modelOfAssignment formula.numVars a)) ↔ Models formula a := by
  simp only [models_iff]
  constructor
  · intro satisfied clause member
    obtain ⟨lit, contained, truth⟩ := satisfied clause member
    exact ⟨lit, contained, (assignment_modelOfAssignment a (valid clause member lit contained).2) ▸ truth⟩
  · intro satisfied clause member
    obtain ⟨lit, contained, truth⟩ := satisfied clause member
    exact ⟨lit, contained, (assignment_modelOfAssignment a (valid clause member lit contained).2).symm ▸ truth⟩

/-- 标准语义下存在 satisfying assignment，当且仅当存在覆盖声明变量且通过可执行 checker 的 model。 -/
theorem satisfiable_iff_complete_model {formula : Formula} (valid : WellFormed formula) :
    (∃ a, Models formula a) ↔
      ∃ model, Covers model formula.numVars ∧ formula.satisfiedBy model = true := by
  constructor
  · rintro ⟨a, satisfied⟩
    exact ⟨modelOfAssignment formula.numVars a, modelOfAssignment_covers _ _,
      (satisfiedBy_iff_models valid _).mpr ((models_restrict valid a).mpr satisfied)⟩
  · rintro ⟨model, _, satisfied⟩
    exact ⟨assignment model, (satisfiedBy_iff_models valid model).mp satisfied⟩

/-- 标准 UNSAT 等价于所有覆盖声明变量的有限 model 都被可执行 checker 拒绝。 -/
theorem unsat_iff_complete_models {formula : Formula} (valid : WellFormed formula) :
    Std.Sat.CNF.Unsat (formulaView formula) ↔
      ∀ model, Covers model formula.numVars → formula.satisfiedBy model = false := by
  rw [Std.Sat.CNF.unsat_iff_not_sat]
  constructor
  · intro unsat model _
    exact Bool.eq_false_iff.mpr (fun satisfied =>
      unsat (assignment model) ((satisfiedBy_iff_models valid model).mp satisfied))
  · intro unsat a satisfied
    have checked := unsat (modelOfAssignment formula.numVars a) (modelOfAssignment_covers _ _)
    have truth := (satisfiedBy_iff_models valid _).mpr ((models_restrict valid a).mpr satisfied)
    simp [checked] at truth

/-- 满足 ValidResult 的 SAT 输出会通过原始 Formula 的独立 model checker。 -/
theorem valid_sat_passes_checker {formula : Formula} (valid : WellFormed formula)
    {model : Array Bool} {stats : CDCL.Stats} (result : ValidResult formula (.sat model stats)) :
    formula.satisfiedBy model = true := (satisfiedBy_iff_models valid model).mpr result.2

end MicrosatLean.Verification
