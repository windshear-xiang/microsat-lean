import MicrosatLean.Verification.Invariant
import MicrosatLean.Verification.Progress.Rank

/-! progress contract 与有限 clause space。共享 rank 定义位于 Progress/Rank，使两层证明使用同一个 measure。
3^n 统计每个变量在规范子句中的三种选择：不出现、正出现、负出现。
freshness 针对当前保留的 learned clauses；删除后重新学习的情形还需要结合数据库上限的增长证明进展。
-/

namespace MicrosatLean.Verification

/-- 枚举 n 个变量的全部三值 polarity keys：每个位置取 none、some true 或 some false。 -/
def clauseUniverse : Nat → List (List (Option Bool))
  | 0 => [[]]
  | n + 1 => (clauseUniverse n).map (none :: ·) ++
      (clauseUniverse n).map (some true :: ·) ++ (clauseUniverse n).map (some false :: ·)

/-- n 个变量的三值 clause space 大小为 3^n。 -/
theorem clauseUniverse_length (n : Nat) : (clauseUniverse n).length = 3 ^ n := by
  induction n with
  | zero => simp [clauseUniverse]
  | succ n ih => simp [clauseUniverse, ih, Nat.pow_succ]; omega

/-- canonicalKey 为每个声明变量保留一个位置，因此长度恰为 n。 -/
theorem canonicalKey_length (n : Nat) (clause : Clause) :
    (canonicalKey n clause).length = n := by simp [canonicalKey]

/-- 每个实际 running step 在前后状态满足 Inv 时，都使共享 variant 严格下降。
这是待证明的程序性质，不是 Inv 内的未来行为假设，也不要求调用者提供已知足够的 fuel。
-/
def StepDecreases : Prop := ∀ formula before after,
  Inv formula before → Inv formula after → CDCL.step before = .running after →
    RankLT (variant (max 1 formula.numVars) after) (variant (max 1 formula.numVars) before)

end MicrosatLean.Verification
