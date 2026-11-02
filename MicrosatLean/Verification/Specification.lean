import MicrosatLean.CDCL.Search
import Std.Sat.CNF

namespace MicrosatLean.Verification

/-!
specification 的输入边界是带变量上界的 `Formula`，不是 DIMACS 字节流。
下面的视图保留原始子句，包括重复项、空子句和重言式；规范化由初始化 contract 负责。
本文件不含待补证明，也不改变可执行代码中的文字编码。
-/

/-- 标准语义使用的 total assignment：为每个自然数变量给出布尔值。 -/
abbrev Assignment := Nat → Bool
/-- `Std.Sat` 的文字类型，由变量编号和使文字为真的布尔值组成。 -/
abbrev Literal := Std.Sat.Literal Nat
/-- `Std.Sat.CNF` 的子句类型，语义为其中各文字的析取。 -/
abbrev Clause := Std.Sat.CNF.Clause Nat
/-- `Std.Sat.CNF` 的公式类型，语义为其中各子句的合取。 -/
abbrev CNF := Std.Sat.CNF Nat

/-- 将整数编码的文字解释为标准库中的变量和极性。 -/
def literalView (lit : Lit) : Literal := (lit.var, lit % 2 == 0)

/-- 逐个转换文字，得到标准子句视图，保留文字的次序和重复项。 -/
def clauseView (clause : Array Lit) : Clause :=
  .ofLiterals (clause.toList.map literalView)

/-- 逐个转换输入子句，建立与 `Std.Sat.CNF` 的语义桥接。 -/
def formulaView (formula : Formula) : CNF :=
  ⟨formula.clauses.map clauseView⟩

/-- 将有限模型数组扩展为 total assignment；数组范围外的变量取 false。 -/
def assignment (model : Array Bool) : Assignment := fun var => model.getD var false

/-- 输入范围 specification：每个文字的变量编号都在 `1..numVars` 内。 -/
def WellFormed (formula : Formula) : Prop :=
  ∀ clause ∈ formula.clauses, ∀ lit ∈ clause,
    0 < lit.var ∧ lit.var ≤ formula.numVars

/-- 命题形式的 `WellFormed` 与可执行的输入范围检查等价。 -/
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

/-- 通过已有的有限范围检查判定 `WellFormed`，供可执行入口使用。 -/
instance (formula : Formula) : Decidable (WellFormed formula) :=
  if checked : formula.wellFormed = true then
    isTrue ((wellFormed_iff_check formula).mpr checked)
  else
    isFalse (fun valid => checked ((wellFormed_iff_check formula).mp valid))

/-- 模型数组覆盖所有声明变量；数组还包含编号 0 的保留位置。 -/
def Covers (model : Array Bool) (variables : Nat) : Prop := variables < model.size

/-- 使用标准库 CNF 语义，表达一个 total assignment 满足输入公式。 -/
def Models (formula : Formula) (a : Assignment) : Prop :=
  Std.Sat.CNF.Sat a (formulaView formula)

/-- 输入公式蕴含给定子句：输入的每个模型都满足该子句，适合表述学习子句的有效性。 -/
def EntailsClause (formula : Formula) (clause : Array Lit) : Prop :=
  Std.Sat.CNF.EntailsClause (formulaView formula) (clauseView clause)

/-- 最终结果的功能正确性 specification：SAT 模型覆盖所有变量并满足输入，
UNSAT 表示输入不存在模型。执行统计不属于此正确性结论。 -/
def ValidResult (formula : Formula) : CDCL.SolveResult → Prop
  | .sat model _ => Covers model formula.numVars ∧ Models formula (assignment model)
  | .unsat _ => Std.Sat.CNF.Unsat (formulaView formula)

/-- 标准子句视图中的文字列表，恰好是原数组逐个转换后的列表。 -/
theorem clauseView_literals (clause : Array Lit) :
    (clauseView clause).literals = clause.toList.map literalView := by
  simp [clauseView]

/-- 将标准子句中的成员关系转换为原文字数组中的成员关系。 -/
theorem clauseView_mem {lit : Literal} {clause : Array Lit} :
    lit ∈ clauseView clause ↔ ∃ encoded ∈ clause, literalView encoded = lit := by
  simp [← Std.Sat.CNF.Clause.mem_literals_iff, clauseView_literals]

/-- 标准子句被满足，当且仅当原数组中至少有一个文字为真。 -/
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

/-- 将标准 CNF 的满足关系展开为：每个输入子句中至少有一个文字为真。 -/
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

/-- 整数编码的取反操作与标准文字取反相容。 -/
@[simp] theorem literalView_negate (lit : Lit) :
    literalView lit.negate = (literalView lit).negate := by
  have remainder : (lit ^^^ 1) % 2 = lit % 2 ^^^ 1 := by
    simpa using (Nat.xor_mod_two_pow (a := lit) (b := 1) (n := 1))
  apply Prod.ext
  · simp [literalView, Lit.negate, Lit.var, Nat.xor_div_two, Std.Sat.Literal.negate]
  · rcases Nat.mod_two_eq_zero_or_one lit with even | odd
    · simp [literalView, Lit.negate, Std.Sat.Literal.negate, remainder, even]
    · simp [literalView, Lit.negate, Std.Sat.Literal.negate, remainder, odd]

/-- 对良构输入，可执行模型检查返回 true，当且仅当扩展后的赋值满足标准 CNF 语义。 -/
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

/-- 将 total assignment 截取为覆盖声明变量的有限数组；未出现在子句中的声明变量也保留。 -/
def modelOfAssignment (variables : Nat) (a : Assignment) : Array Bool :=
  Array.ofFn fun i : Fin (variables + 1) => a i.val

/-- 从 total assignment 构造的数组覆盖全部声明变量。 -/
@[simp] theorem modelOfAssignment_covers (variables : Nat) (a : Assignment) :
    Covers (modelOfAssignment variables a) variables := by
  simp [Covers, modelOfAssignment]

/-- 在声明范围内，将 total assignment 截成数组再扩展，不改变变量取值。 -/
theorem assignment_modelOfAssignment {variables var : Nat} (a : Assignment)
    (bound : var ≤ variables) : assignment (modelOfAssignment variables a) var = a var := by
  unfold assignment
  rw [← Array.getElem_eq_getD (h := by simpa [modelOfAssignment] using Nat.lt_succ_of_le bound)]
  simp [modelOfAssignment]

/-- 对良构输入，将 total assignment 限制到声明范围，不改变公式是否被满足。 -/
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

/-- 良构输入存在标准语义模型，当且仅当存在覆盖全部变量并通过检查的有限模型数组。 -/
theorem satisfiable_iff_complete_model {formula : Formula} (valid : WellFormed formula) :
    (∃ a, Models formula a) ↔
      ∃ model, Covers model formula.numVars ∧ formula.satisfiedBy model = true := by
  constructor
  · rintro ⟨a, satisfied⟩
    exact ⟨modelOfAssignment formula.numVars a, modelOfAssignment_covers _ _,
      (satisfiedBy_iff_models valid _).mpr ((models_restrict valid a).mpr satisfied)⟩
  · rintro ⟨model, _, satisfied⟩
    exact ⟨assignment model, (satisfiedBy_iff_models valid model).mp satisfied⟩

/-- 良构输入的标准 UNSAT，等价于每个覆盖声明变量的模型数组都无法通过检查。 -/
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

/-- 满足最终 SAT specification 的返回模型一定通过可执行的输入公式检查。 -/
theorem valid_sat_passes_checker {formula : Formula} (valid : WellFormed formula)
    {model : Array Bool} {stats : CDCL.Stats} (result : ValidResult formula (.sat model stats)) :
    formula.satisfiedBy model = true := (satisfiedBy_iff_models valid model).mpr result.2

end MicrosatLean.Verification
