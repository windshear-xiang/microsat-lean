import MicrosatLean.Verification.Invariant

namespace MicrosatLean.Verification

/-!
本文件定义允许的逻辑操作，不实现第二个求解器。
每条规则中关于学习子句或 unit 的前提，最终都必须从真实代码中导出。
该关系保持语义的结论是显式的待证 obligation；具体 watch 和控制状态的保持另有证明责任。
-/

/-- 在逻辑 trail 末尾追加一个真文字及其 reason，保留其他逻辑状态字段。 -/
def appendEntry (a : LogicalState) (lit : Literal) (reason : Option Clause) : LogicalState :=
  { a with trail := a.trail ++ [⟨lit, reason⟩] }

/-- 要求两个子句列表逐项对应，每对子句的文字列表互为排列。
该关系明确记录文字重排，不把子句次序或重复项随意视为相同。 -/
def ClausePermutations : List Clause → List Clause → Prop
  | [], [] => True
  | left :: rest, right :: remaining =>
      left.literals.Perm right.literals ∧ ClausePermutations rest remaining
  | _, _ => False

/-- 允许的单次逻辑 transition，显式列出 decision、propagation、learning、backjump 等操作的前提。 -/
inductive LogicalMove (input : CNF) : LogicalState → LogicalState → Prop where
  /-- 在 unit closure 已成立时，为合法且未赋值的变量追加无 reason 的 decision。 -/
  | decide (a : LogicalState) (lit : Literal)
      (declared : LiteralBound a.numVars lit) (fresh : Unassigned a.trueTrail lit.1)
      (closed : Closed a) : LogicalMove input a (appendEntry a lit none)
  /-- 数据库中的子句已变为 unit 时，将其未赋值的 head 设为真并保存该子句作为 reason。 -/
  | propagate (a : LogicalState) (clause : Clause) (lit : Literal)
      (stored : clause ∈ a.database) (head : clause.literals.head? = some lit)
      (fresh : Unassigned a.trueTrail lit.1)
      (tails : ∀ other ∈ clause.literals.tail, FalseIn a.trueTrail other) :
      LogicalMove input a (appendEntry a lit (some clause))
  /-- 追加一个由输入蕴含、变量范围合法且非空的学习子句。 -/
  | learn (a : LogicalState) (clause : Clause)
      (entailed : Std.Sat.CNF.EntailsClause input clause)
      (declared : ∀ lit ∈ clause, LiteralBound a.numVars lit)
      (nonempty : clause.literals ≠ []) :
      LogicalMove input a { a with learned := a.learned ++ [clause] }
  /-- 保留指定 trail 前缀，且不能撤销已确认的 root 项。 -/
  | backjump (a : LogicalState) (keep : Nat)
      (roots : a.rootSize ≤ keep) (active : keep ≤ a.trail.length) :
      LogicalMove input a { a with trail := a.trail.take keep }
  /-- 将活动 trail 截断至 root 前缀。 -/
  | restart (a : LogicalState) :
      LogicalMove input a { a with trail := a.trail.take a.rootSize }
  /-- 删除部分学习子句，但必须保留所有活动 trail 项仍在使用的 reason。 -/
  | forget (a : LogicalState) (retained : List Clause) (subset : retained ⊆ a.learned)
      (reasons : ∀ entry ∈ a.trail, ∀ clause, entry.reason = some clause →
        clause ∈ a.original ++ retained) :
      LogicalMove input a { a with learned := retained }
  /-- 对对应子句内部的文字作排列，描述 watch 交换引起的逻辑表示变化。 -/
  | permute (a : LogicalState) (original learned : List Clause)
      (originals : ClausePermutations a.original original)
      (lemmas : ClausePermutations a.learned learned) :
      LogicalMove input a { a with original := original, learned := learned }
  /-- 在证明整个指定前缀均由输入蕴含后，扩大已确认的 root 前缀。 -/
  | commitRoots (a : LogicalState) (count : Nat)
      (lower : a.rootSize ≤ count) (upper : count ≤ a.trail.length)
      (sound : ∀ lit ∈ prefixLiterals a count, ∀ valuation,
        Std.Sat.CNF.Sat valuation input → valuation lit.1 = lit.2) :
      LogicalMove input a { a with rootSize := count }

/-- 有限次逻辑 transition 的自反传递闭包。
一个具体 step 可以对应零次或多次逻辑操作；仅调整 watch 时可以不改变逻辑状态，但具体 variant 仍须严格下降。 -/
inductive LogicalExecution (input : CNF) : LogicalState → LogicalState → Prop where
  /-- 零次逻辑操作，允许具体步骤只调整物理或控制信息。 -/
  | refl (a : LogicalState) : LogicalExecution input a a
  /-- 在已有有限执行之后追加一次允许的逻辑操作。 -/
  | advance {before middle after : LogicalState} :
      LogicalExecution input before middle → LogicalMove input middle after →
      LogicalExecution input before after

/-- 待证明的逻辑规则健全性：每种允许的逻辑 transition 都保持 `SemanticInv`。 -/
def LogicalSoundness : Prop := ∀ input before after,
  SemanticInv input before → LogicalMove input before after → SemanticInv input after

/-- 给定单步逻辑健全性，用归纳得到任意有限逻辑执行都保持语义 invariant。 -/
theorem execution_preserves (sound : LogicalSoundness) {input : CNF}
    {before after : LogicalState} (valid : SemanticInv input before)
    (execution : LogicalExecution input before after) : SemanticInv input after := by
  induction execution with
  | refl => exact valid
  | advance _ move ih => exact sound _ _ _ ih move

/-- 返回结果前必须建立的逻辑条件：SAT 要求赋值完整、unit closure 且输出模型与 trail 一致；
UNSAT 要求整个 trail 都是 root，并且数据库中存在所有文字均为假的真实子句。 -/
def Terminal (formula : Formula) (a : LogicalState) : CDCL.SolveResult → Prop
  | .sat model _ => Covers model formula.numVars ∧ Compatible (assignment model) a.trueTrail ∧
      Complete a ∧ Closed a
  | .unsat _ => a.rootSize = a.trail.length ∧ ∃ clause ∈ a.database, Conflict a clause

/-- 待证明的终态健全性：语义 invariant 与终态条件共同推出最终 `ValidResult`。 -/
def TerminalSoundness : Prop := ∀ formula a result,
  SemanticInv (formulaView formula) a → Terminal formula a result → ValidResult formula result

/-- 已满足的子句若除 head 外的所有文字均为假，则 head 必须为真；供 unit propagation 的证明复用。 -/
theorem forced_head {valuation : Assignment} {clause : Clause} {head : Literal}
    (satisfied : Std.Sat.CNF.Clause.Sat valuation clause)
    (tails : ∀ lit ∈ clause, lit ≠ head → valuation lit.1 ≠ lit.2) :
    valuation head.1 = head.2 := by
  obtain ⟨lit, member, truth⟩ := Std.Sat.CNF.Clause.sat_iff_exists_mem_eq.mp satisfied
  by_cases equal : lit = head
  · simpa only [equal] using truth
  · exact False.elim (tails lit member equal truth)

/-- 加入由输入蕴含的子句，保持输入公式的全部模型不变。 -/
theorem learning_preserves_models {input : CNF} {clause : Clause}
    (entailed : Std.Sat.CNF.EntailsClause input clause) :
    Std.Sat.CNF.BiEntails input (input.add clause) :=
  ⟨Std.Sat.CNF.entails_add_of_entails_clause _ _ entailed, Std.Sat.CNF.add_entails_left⟩

end MicrosatLean.Verification
