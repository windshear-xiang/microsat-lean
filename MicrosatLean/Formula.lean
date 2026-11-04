import Std

namespace MicrosatLean

/-- Literals use `2 * variable` for positive and `2 * variable + 1` for
negative occurrences. Variables start at one; zero terminates arena clauses. -/
abbrev Lit := Nat

namespace Lit

@[inline] def var (lit : Lit) : Nat := lit / 2

@[inline] def negate (lit : Lit) : Lit := lit ^^^ 1

@[inline] def ofInt (value : Int) : Lit :=
  if value == 0 then 0
  else 2 * value.natAbs + if value < 0 then 1 else 0

@[inline] def toInt (lit : Lit) : Int :=
  if lit % 2 == 0 then Int.ofNat lit.var else -(Int.ofNat lit.var)

@[inline] def satisfiedBy (lit : Lit) (model : Array Bool) : Bool :=
  lit != 0 && (model[lit.var]! == (lit % 2 == 0))

end Lit

/-- A DIMACS formula, retaining all input clauses for independent model checks.
The solver checks literal bounds before constructing its indexed state. -/
structure Formula where
  numVars : Nat
  clauses : Array (Array Lit)
  deriving Repr, Inhabited

def Formula.satisfiedBy (formula : Formula) (model : Array Bool) : Bool :=
  formula.clauses.all fun clause => clause.any fun lit => lit.satisfiedBy model

/-- Check declared variable bounds, including exclusion of the reserved
zero variable. Empty formulas and empty clauses are valid CNF syntax. -/
def Formula.wellFormed (formula : Formula) : Bool :=
  formula.clauses.all fun clause =>
    clause.all fun lit => decide (0 < lit.var ∧ lit.var ≤ formula.numVars)

end MicrosatLean
