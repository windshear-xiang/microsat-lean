import MicrosatLean.CDCL.Search

/-! 框架与具体 transition proofs 共用的算术 measure 和 lexicographic rank。
本模块只依赖可执行状态类型，不导入逻辑 invariant。rank 的各分量在证明中使用，编译后无需逐步计算。
-/

namespace MicrosatLean.Verification

/-- 把 learned-clause 数量与可增长的数据库上限组合成自然数 measure。
学习增加 count 会减小末项；reduction 提高 limit 可补偿删除 clauses 后 count 的下降。
-/
def numericProgress (bound count limit : Nat) : Nat :=
  (bound + 1) * (bound - min bound limit) + (bound - count)

/-- 将 numericProgress 应用于实际 state 的 nLemmas 与 maxLemmas。 -/
def clauseProgress (bound : Nat) (s : CDCL.State) : Nat :=
  numericProgress bound s.nLemmas s.maxLemmas

/-- 由四个自然数组成的共享 termination rank。 -/
abbrev Rank := Nat × Nat × Nat × Nat

/-- Rank 上从左到右比较的严格 lexicographic 次序。 -/
def RankLT : Rank → Rank → Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))

/-- 自然数严格次序的有限 lexicographic 组合是 well-founded，因此不能无限严格下降。 -/
theorem rank_wellFounded : WellFounded RankLT :=
  (inferInstance : WellFoundedRelation Rank).wf

/-- 记录本轮传播是否已经学到新 clause，供随后的 restart/choice 记账；beginPropagation 阶段清零。 -/
def learningCredit (m : CDCL.Machine) : Nat :=
  match m.phase with
  | .beginPropagation => 0
  | _ => if m.oldLemmas < m.solver.nLemmas then 1 else 0

/-- 控制 phase 的最后一级 rank：begin/watch 为 2，nextLiteral 为 1，choose 为 0。 -/
def phaseRank : CDCL.Phase → Nat
  | .beginPropagation => 2
  | .nextLiteral => 1
  | .watch => 2
  | .choose => 0

/-- 组合数据库进展、学习 credit、待赋值/待处理数量以及 phase 位置。
variables 是初始化时固定的数量；watch 内部扫描必须在预算内推进 phase、赋值、学习或完成。
该预算充分性的证明属于具体实现验证。
-/
def controlRank (bound variables : Nat) (m : CDCL.Machine) : Rank :=
  (clauseProgress bound m.solver,
   learningCredit m, 2 * variables - m.solver.assigned - m.solver.processed, phaseRank m.phase)

/-- 把 clause-space 上界固定为 3^variables，得到实际递归使用的 rank。 -/
def variant (variables : Nat) (m : CDCL.Machine) : Rank :=
  controlRank (3 ^ variables) variables m

/-- 当 count 尚未达到有限 clause 上界时，新增一个 learned clause 会严格减小 numericProgress。 -/
theorem numericProgress_learn {bound count limit : Nat} (room : count < bound) :
    numericProgress bound (count + 1) limit < numericProgress bound count limit := by
  unfold numericProgress
  omega

end MicrosatLean.Verification
