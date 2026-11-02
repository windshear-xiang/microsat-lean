import MicrosatLean.Verification.Invariant

namespace MicrosatLean.Verification

/-!
现有 restart/reduction 策略的候选 rank。数值关系的证明，与真实运行 step
严格降低 rank 的 obligation 分开。`3 ^ n` 计算变量的三元极性选择数，不是赋值数。
新鲜性针对当前保留的学习子句；删除后再次学习的情况由容量阈值增长处理。
-/

/-- 枚举每个变量取缺席、正文字或负文字三种选择得到的所有 key，用于有限子句空间计数。 -/
def clauseUniverse : Nat → List (List (Option Bool))
  | 0 => [[]]
  | n + 1 => (clauseUniverse n).map (none :: ·) ++
      (clauseUniverse n).map (some true :: ·) ++ (clauseUniverse n).map (some false :: ·)

/-- `n` 个变量的三元选择共有 `3 ^ n` 个；这里计数的是子句 key，而非赋值。 -/
theorem clauseUniverse_length (n : Nat) : (clauseUniverse n).length = 3 ^ n := by
  induction n with
  | zero => simp [clauseUniverse]
  | succ n ih => simp [clauseUniverse, ih, Nat.pow_succ]; omega

/-- 每个子句的 canonical key 恰好为每个声明变量保留一个位置。 -/
theorem canonicalKey_length (n : Nat) (clause : Clause) :
    (canonicalKey n clause).length = n := by simp [canonicalKey]

/-- 综合剩余子句空间与学习子句容量阈值的数值度量，用于处理 learning 以及删除后再次学习。 -/
def numericProgress (bound count limit : Nat) : Nat :=
  (bound + 1) * (bound - min bound limit) + (bound - count)

/-- 终止度量的四元组：数据库数值进展、learning credit、赋值与传播余量、阶段权重。 -/
abbrev Rank := Nat × Nat × Nat × Nat

/-- 四元组上的严格字典序关系，前面的分量具有更高优先级。 -/
def RankLT : Rank → Rank → Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))

/-- 自然数四元组的严格字典序是 well-founded，因而不存在无限严格下降链。 -/
theorem rank_wellFounded : WellFounded RankLT :=
  (inferInstance : WellFoundedRelation Rank).wf

/-- 记录本轮 propagation 是否增加了学习子句；用于协调后续 choose 与 restart 的进展比较。 -/
def learningCredit (m : CDCL.Machine) : Nat :=
  match m.phase with
  | .beginPropagation => 0
  | _ => if m.oldLemmas < m.solver.nLemmas then 1 else 0

/-- 执行阶段的末级权重；仅在更高优先级的度量分量不变时用于比较。 -/
def phaseRank : CDCL.Phase → Nat
  | .beginPropagation => 2
  | .nextLiteral => 1
  | .watch => 2
  | .choose => 0

/-- 为具体机器计算候选终止度量；`variables` 在初始化后固定，不随 step 改变。
watch 的扫描预算属于内部实现：充分的扫描必须推进阶段、产生赋值、学习或结束。
证明扫描预算充分是实现层的 obligation。 -/
def variant (variables : Nat) (m : CDCL.Machine) : Rank :=
  (numericProgress (3 ^ variables) m.solver.nLemmas m.solver.maxLemmas,
   learningCredit m, 2 * variables - m.solver.assigned - m.solver.processed, phaseRank m.phase)

/-- 在学习子句数量尚未达到空间上界时，增加一个子句会严格减小数据库数值度量。 -/
theorem numericProgress_learn {bound count limit : Nat} (room : count < bound) :
    numericProgress bound (count + 1) limit < numericProgress bound count limit := by
  unfold numericProgress
  omega

/-- 待证明的具体算法性质：每个继续运行且前后 invariant 成立的真实 step 都使 variant 严格下降。
它不是 `Inv` 的字段，也不是调用者提供的某个成功 fuel。 -/
def StepDecreases : Prop := ∀ formula before after,
  Inv formula before → Inv formula after → CDCL.step before = .running after →
    RankLT (variant (max 1 formula.numVars) after) (variant (max 1 formula.numVars) before)

end MicrosatLean.Verification
