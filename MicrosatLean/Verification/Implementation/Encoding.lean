import MicrosatLean.Verification.Specification

namespace MicrosatLean.Verification.Implementation

/-!
Specification 中共享 views 的辅助引理，供具体实现证明复用。
可执行 literal 编码与标准 CNF 语义均使用已有的唯一共享定义；这里补充数组读取、
view 的单射性，以及子句成员关系和互补 literals 对满足性的影响。
-/

/-- 索引在数组范围内时，assignment 与直接读取 model[var] 相同，不会使用越界默认值 false。 -/
theorem assignment_eq_getElem (model : Array Bool) {var : Nat}
    (h : var < model.size) : assignment model var = model[var] := by
  exact (Array.getElem_eq_getD false).symm

/-- 空 literal 数组的标准 view 就是空 clause。 -/
@[simp] theorem clauseView_empty : clauseView #[] = .empty := by
  simp [clauseView, Std.Sat.CNF.Clause.ofLiterals]

/-- 从整份 Formula 的 WellFormed 前提，取得其中任一 clause 的变量边界性质。 -/
theorem WellFormed.clause {formula : Formula} (h : WellFormed formula)
    {clause : Array Lit} (hc : clause ∈ formula.clauses) :
    ClauseWellFormed formula.numVars clause := h clause hc

/-- literalView 是单射：标准 view 中的变量编号与 polarity 唯一确定原始编码。
该性质对所有编码成立，无需额外的 WellFormed 前提。 -/
theorem literalView_injective : Function.Injective literalView := by
  intro left right heq
  have hvar := congrArg Prod.fst heq
  have hpol := congrArg Prod.snd heq
  dsimp [literalView, Lit.var] at hvar hpol
  have hzero : (left % 2 = 0) ↔ (right % 2 = 0) := by
    simpa using Bool.eq_iff_iff.mp hpol
  have hmod : left % 2 = right % 2 := by
    rcases Nat.mod_two_eq_zero_or_one left with hleft | hleft
    · rw [hleft, hzero.mp hleft]
    · rcases Nat.mod_two_eq_zero_or_one right with hright | hright
      · have := hzero.mpr hright
        simp [hleft] at this
      · rw [hleft, hright]
  rw [← Nat.mod_add_div left 2, ← Nat.mod_add_div right 2]
  rw [hmod, hvar]

/-- 两个 literal 数组若具有相同的成员关系，其标准 clause views 在同一 assignment 下的满足性相同。
数组的 literal 排列与重复次数可以不同。 -/
theorem clauseView_sat_iff_of_mem_iff {left right : Array Lit}
    (h : ∀ lit, lit ∈ left ↔ lit ∈ right) (a : Nat → Bool) :
    Std.Sat.CNF.Clause.Sat a (clauseView left) ↔
      Std.Sat.CNF.Clause.Sat a (clauseView right) := by
  simp only [clauseView_sat_iff, h]

/-- clause 同时包含某个 literal 及其补项时，它是 tautology，标准 view 被任意 assignment 满足。 -/
theorem clauseView_sat_of_complement {clause : Array Lit} {lit : Lit}
    (hpos : lit ∈ clause) (hneg : lit.negate ∈ clause) :
    ∀ a, Std.Sat.CNF.Clause.Sat a (clauseView clause) := by
  apply Std.Sat.CNF.Clause.sat_of_mem_of_mem_neg
    (atom := (literalView lit).1) (pol := (literalView lit).2)
  · exact clauseView_mem.mpr ⟨lit, hpos, rfl⟩
  · exact clauseView_mem.mpr ⟨lit.negate, hneg, literalView_negate lit⟩

end MicrosatLean.Verification.Implementation
