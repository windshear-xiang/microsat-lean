import MicrosatLean.Verification.Invariant

/-! 允许的逻辑迁移规则，用于解释真实程序的一步或多步效果。
learn 与 propagation 的前提必须由实际代码证明；semantic preservation 位于 Implementation/Logic/Moves。
watch、cursor 等具体控制信息的 preservation 另由实现证明处理。
-/

namespace MicrosatLean.Verification

/-- 在逻辑 trail 末尾追加一个真 literal 及其 reason，保留其余状态。 -/
def appendEntry (a : LogicalState) (lit : Literal) (reason : Option Clause) : LogicalState :=
  { a with trail := a.trail ++ [⟨lit, reason⟩] }

/-- 逐条对应的 clauses 仅改变 literal 排列。
这里显式记录列表 permutation，不把 clause 顺序或重复项直接当作语义等号。
-/
def ClausePermutations : List Clause → List Clause → Prop
  | [], [] => True
  | left :: rest, right :: remaining =>
      left.literals.Perm right.literals ∧ ClausePermutations rest remaining
  | _, _ => False

/-- 抽象搜索允许的单次逻辑迁移；每个 constructor 的前提都是实际实现必须建立的证明义务。 -/
inductive LogicalMove (input : CNF) : LogicalState → LogicalState → Prop where
  /-- 在传播闭包状态，为合法的未赋值变量追加一个 branch decision。 -/
  | decide (a : LogicalState) (lit : Literal)
      (declared : LiteralBound a.numVars lit) (fresh : Unassigned a.trueTrail lit.1)
      (closed : Closed a) : LogicalMove input a (appendEntry a lit none)
  /-- 根据数据库中的 unit reason，为未赋值变量追加被强制的真 literal。 -/
  | propagate (a : LogicalState) (clause : Clause) (lit : Literal)
      (stored : clause ∈ a.database) (head : clause.literals.head? = some lit)
      (fresh : Unassigned a.trueTrail lit.1)
      (tails : ∀ other ∈ clause.literals.tail, FalseIn a.trueTrail other) :
      LogicalMove input a (appendEntry a lit (some clause))
  /-- 加入输入蕴含、变量有界且非空的 learned clause。 -/
  | learn (a : LogicalState) (clause : Clause)
      (entailed : Std.Sat.CNF.EntailsClause input clause)
      (declared : ∀ lit ∈ clause, LiteralBound a.numVars lit)
      (nonempty : clause.literals ≠ []) :
      LogicalMove input a { a with learned := a.learned ++ [clause] }
  /-- 缩短 trail，但保留全部 root assignments。 -/
  | backjump (a : LogicalState) (keep : Nat)
      (roots : a.rootSize ≤ keep) (active : keep ≤ a.trail.length) :
      LogicalMove input a { a with trail := a.trail.take keep }
  /-- 撤销整个非 root 后缀。 -/
  | restart (a : LogicalState) :
      LogicalMove input a { a with trail := a.trail.take a.rootSize }
  /-- 删除部分 learned clauses，同时保留活动 trail 使用的所有 reason clauses。 -/
  | forget (a : LogicalState) (retained : List Clause) (subset : retained ⊆ a.learned)
      (reasons : ∀ entry ∈ a.trail, ∀ clause, entry.reason = some clause →
        clause ∈ a.original ++ retained) :
      LogicalMove input a { a with learned := retained }
  /-- 只调整各个 clause 内的 literal 排列。 -/
  | permute (a : LogicalState) (original learned : List Clause)
      (originals : ClausePermutations a.original original)
      (lemmas : ClausePermutations a.learned learned) :
      LogicalMove input a { a with original := original, learned := learned }
  /-- 把更长的 trail prefix 确认为 root，并证明其中全部 literals 无需 decisions 即由输入蕴含。 -/
  | commitRoots (a : LogicalState) (count : Nat)
      (lower : a.rootSize ≤ count) (upper : count ≤ a.trail.length)
      (sound : ∀ lit ∈ prefixLiterals a count, ∀ valuation,
        Std.Sat.CNF.Sat valuation input → valuation lit.1 = lit.2) :
      LogicalMove input a { a with rootSize := count }

/-- 零步或多步逻辑迁移。一次具体 step 可对应多个逻辑动作，也可仅调整 watches 而逻辑状态不变。
即使逻辑上 stutter，具体 rank 仍需严格下降。
-/
inductive LogicalExecution (input : CNF) : LogicalState → LogicalState → Prop where
  /-- 零次迁移，起点和终点相同。 -/
  | refl (a : LogicalState) : LogicalExecution input a a
  /-- 在已有有限 execution 之后追加一次 LogicalMove。 -/
  | advance {before middle after : LogicalState} :
      LogicalExecution input before middle → LogicalMove input middle after →
      LogicalExecution input before after

/-- 每一种 LogicalMove 都保持 SemanticInv 的通用语义 preservation contract。 -/
def LogicalSoundness : Prop := ∀ input before after,
  SemanticInv input before → LogicalMove input before after → SemanticInv input after

/-- 将单次逻辑迁移的 preservation 提升为任意有限 LogicalExecution 的 preservation。 -/
theorem execution_preserves (sound : LogicalSoundness) {input : CNF}
    {before after : LogicalState} (valid : SemanticInv input before)
    (execution : LogicalExecution input before after) : SemanticInv input after := by
  induction execution with
  | refl => exact valid
  | advance _ move ih => exact sound _ _ _ ih move

/-- 从逻辑状态推出最终结果所需的 gate。
SAT 同时要求完整赋值、传播闭包、model 覆盖及与 trail 相容；UNSAT 要求全 trail 为 root，且存在真正全假的存储 clause。
-/
def Terminal (formula : Formula) (a : LogicalState) : CDCL.SolveResult → Prop
  | .sat model _ => Covers model formula.numVars ∧ Compatible (assignment model) a.trueTrail ∧
      Complete a ∧ Closed a
  | .unsat _ => a.rootSize = a.trail.length ∧ ∃ clause ∈ a.database, Conflict a clause

/-- SemanticInv 与对应 Terminal gate 一起推出最终 ValidResult。 -/
def TerminalSoundness : Prop := ∀ formula a result,
  SemanticInv (formulaView formula) a → Terminal formula a result → ValidResult formula result

/-- 一个 clause 被满足而除 head 外的所有候选 literal 都为假时，head 必须为真。 -/
theorem forced_head {valuation : Assignment} {clause : Clause} {head : Literal}
    (satisfied : Std.Sat.CNF.Clause.Sat valuation clause)
    (tails : ∀ lit ∈ clause, lit ≠ head → valuation lit.1 ≠ lit.2) :
    valuation head.1 = head.2 := by
  obtain ⟨lit, member, truth⟩ := Std.Sat.CNF.Clause.sat_iff_exists_mem_eq.mp satisfied
  by_cases equal : lit = head
  · simpa only [equal] using truth
  · exact False.elim (tails lit member equal truth)

/-- 把输入已蕴含的 clause 加入 CNF 后，新旧公式互相蕴含，因此保持完全相同的 models。 -/
theorem learning_preserves_models {input : CNF} {clause : Clause}
    (entailed : Std.Sat.CNF.EntailsClause input clause) :
    Std.Sat.CNF.BiEntails input (input.add clause) :=
  ⟨Std.Sat.CNF.entails_add_of_entails_clause _ _ entailed, Std.Sat.CNF.add_entails_left⟩

end MicrosatLean.Verification
