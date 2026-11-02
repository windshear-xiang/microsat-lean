import Std

/-!
输入公式、文字整数编码和可执行检查器。这里保留原始输入；求解器状态使用的规范化副本另行构造。
-/

namespace MicrosatLean

/-- 文字（literal）的整数编码：正文字为 `2 * variable`，负文字为 `2 * variable + 1`。
变量编号从 1 开始；0 用作 arena 中子句的结束标记。 -/
abbrev Lit := Nat

namespace Lit

/-- 从文字编码中提取变量编号。 -/
@[inline] def var (lit : Lit) : Nat := lit / 2

/-- 翻转最低位，得到同一变量的互补文字。 -/
@[inline] def negate (lit : Lit) : Lit := lit ^^^ 1

/-- 将 DIMACS 的有符号整数转换为内部文字编码；输入 0 时保留结束标记 0。 -/
@[inline] def ofInt (value : Int) : Lit :=
  if value == 0 then 0
  else 2 * value.natAbs + if value < 0 then 1 else 0

/-- 将内部文字转换为 DIMACS 使用的有符号整数。 -/
@[inline] def toInt (lit : Lit) : Int :=
  if lit % 2 == 0 then Int.ofNat lit.var else -(Int.ofNat lit.var)

/-- 检查模型数组是否满足该文字；编码 0 不视为可满足的文字。 -/
@[inline] def satisfiedBy (lit : Lit) (model : Array Bool) : Bool :=
  lit != 0 && (model[lit.var]! == (lit % 2 == 0))

end Lit

/-- 保留所有输入子句的 DIMACS 公式，供独立检查模型使用。
求解器在创建按变量索引的状态之前检查文字的变量范围。 -/
structure Formula where
  /-- DIMACS header 声明的变量数。 -/
  numVars : Nat
  /-- 保留输入顺序的子句数组，文字使用内部整数编码。 -/
  clauses : Array (Array Lit)
  deriving Repr, Inhabited

/-- 检查每个输入子句是否至少有一个文字被模型满足。 -/
def Formula.satisfiedBy (formula : Formula) (model : Array Bool) : Bool :=
  formula.clauses.all fun clause => clause.any fun lit => lit.satisfiedBy model

/-- 检查所有文字的变量编号都在声明范围内，并排除保留变量 0。
空公式和空子句都是合法的 CNF 语法。 -/
def Formula.wellFormed (formula : Formula) : Bool :=
  formula.clauses.all fun clause =>
    clause.all fun lit => decide (0 < lit.var ∧ lit.var ≤ formula.numVars)

end MicrosatLean
