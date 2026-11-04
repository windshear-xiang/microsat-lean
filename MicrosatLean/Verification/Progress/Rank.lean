import MicrosatLean.CDCL.Search

namespace MicrosatLean.Verification

/-! Shared arithmetic and rank definitions for the framework and concrete
transition proofs. This module depends only on executable state types. -/

def numericProgress (bound count limit : Nat) : Nat :=
  (bound + 1) * (bound - min bound limit) + (bound - count)

/-- The shared numeric component evaluated at the actual database counters. -/
def clauseProgress (bound : Nat) (s : CDCL.State) : Nat :=
  numericProgress bound s.nLemmas s.maxLemmas

abbrev Rank := Nat × Nat × Nat × Nat

def RankLT : Rank → Rank → Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))

theorem rank_wellFounded : WellFounded RankLT :=
  (inferInstance : WellFoundedRelation Rank).wf

def learningCredit (m : CDCL.Machine) : Nat :=
  match m.phase with
  | .beginPropagation => 0
  | _ => if m.oldLemmas < m.solver.nLemmas then 1 else 0

def phaseRank : CDCL.Phase → Nat
  | .beginPropagation => 2
  | .nextLiteral => 1
  | .watch => 2
  | .choose => 0

/-- `variables` is fixed at initialization, not changed after each step.
Watch fuel is internal: a sufficient scan must either advance phase, assign,
learn or finish. Proving that sufficiency is part of the implementation work. -/
def controlRank (bound variables : Nat) (m : CDCL.Machine) : Rank :=
  (clauseProgress bound m.solver,
   learningCredit m, 2 * variables - m.solver.assigned - m.solver.processed, phaseRank m.phase)

/-- Fix the finite clause bound for the initialized variable count. -/
def variant (variables : Nat) (m : CDCL.Machine) : Rank :=
  controlRank (3 ^ variables) variables m

end MicrosatLean.Verification
