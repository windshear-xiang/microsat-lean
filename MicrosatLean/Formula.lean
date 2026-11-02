import Std

/-! 输入公式与可执行的 literal 编码。变量从 1 开始，0 保留作 arena 子句终止符。
本模块保留原始输入；标准 CNF 语义及其桥接位于 Verification/Specification。
-/

namespace MicrosatLean

/-- 可执行 literal：正项编码为 2 * variable，负项编码为 2 * variable + 1；变量从 1 开始。 -/
abbrev Lit := Nat

namespace Lit

/-- 从 literal 编码中提取变量编号。 -/
@[inline] def var (lit : Lit) : Nat := lit / 2

/-- 翻转编码的最低位，得到补 literal；同一变量的正负 literal 互换。 -/
@[inline] def negate (lit : Lit) : Lit := lit ^^^ 1

/-- 把 DIMACS 带符号整数转换为内部 literal 编码；输入 0 保留为终止符。 -/
@[inline] def ofInt (value : Int) : Lit :=
  if value == 0 then 0
  else 2 * value.natAbs + if value < 0 then 1 else 0

/-- 把内部 literal 编码转换回 DIMACS 带符号整数。 -/
@[inline] def toInt (lit : Lit) : Int :=
  if lit % 2 == 0 then Int.ofNat lit.var else -(Int.ofNat lit.var)

/-- 在有限 model 数组中检查 literal 是否为真；保留的零终止符不算满足。 -/
@[inline] def satisfiedBy (lit : Lit) (model : Array Bool) : Bool :=
  lit != 0 && (model[lit.var]! == (lit % 2 == 0))

end Lit

/-- 保留全部原始子句及声明变量数的输入公式，供独立 model checker 与语义桥接使用。
求解器在建立索引状态之前检查 literal 的变量边界。
-/
structure Formula where
  /-- 输入声明的变量数量。 -/
  numVars : Nat
  /-- 按输入顺序保存的原始 clauses；每个 clause 是 literal 数组。 -/
  clauses : Array (Array Lit)
  deriving Repr, Inhabited

/-- 逐子句检查 model：每个子句都必须至少有一个为真的 literal。 -/
def Formula.satisfiedBy (formula : Formula) (model : Array Bool) : Bool :=
  formula.clauses.all fun clause => clause.any fun lit => lit.satisfiedBy model

/-- 可执行的变量边界检查：所有 literal 的变量都在 1..numVars 内。
空公式、空子句属于合法 CNF 语法，是否可满足由求解结果决定。
-/
def Formula.wellFormed (formula : Formula) : Bool :=
  formula.clauses.all fun clause =>
    clause.all fun lit => decide (0 < lit.var ∧ lit.var ≤ formula.numVars)

end MicrosatLean
