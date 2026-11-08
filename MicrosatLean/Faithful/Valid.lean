import MicrosatLean.Faithful.Memory

/-!
# Valid inputs

Every theorem about the faithful port takes `input.Valid` as its only hypothesis
about the input. The conditions, the reason each one is needed, and the rule for
adding new ones are in `ASSUMPTIONS.md` (section 1). Keep this file and that
section in sync: a new input condition is a new field here, documented there,
in the same change.
-/

namespace MicrosatLean.Faithful

/-- A DIMACS input: the `p cnf nVars nClauses` header and the clauses in file
order, each without its terminating `0`. -/
structure Input where
  nVars : CInt
  nClauses : CInt
  clauses : Array (Array CInt)
  deriving Repr, Inhabited

/-- The literal tokens `parse` reads after the header: each clause, then `0`. -/
def Input.tokens (input : Input) : Array CInt :=
  input.clauses.foldl (init := #[]) fun acc clause => (acc ++ clause).push 0

/-- `ASSUMPTIONS.md`, section 1. -/
structure Input.Valid (input : Input) : Prop where
  /-- V1 (DIMACS): the variable count is nonnegative. -/
  nVars_nonneg : 0 ≤ input.nVars
  /-- V1 (DIMACS): exactly `nClauses` clauses follow the header. -/
  nClauses_eq : input.nClauses = input.clauses.size
  /-- V1 (DIMACS): every literal is nonzero and names a declared variable. -/
  lit_range : ∀ clause ∈ input.clauses, ∀ lit ∈ clause, lit ≠ 0 ∧ abs lit ≤ input.nVars
  /-- V2: no literal occurs twice in one clause. -/
  no_repeated_lit : ∀ clause ∈ input.clauses, clause.toList.Nodup
  /-- V3: every clause has at most `nVars` literals (C's `buffer` has `nVars` cells). -/
  clause_size_le : ∀ clause ∈ input.clauses, (clause.size : CInt) ≤ input.nVars

end MicrosatLean.Faithful
