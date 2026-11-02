import MicrosatLean.Verification.Invariant

namespace MicrosatLean.Verification

/-!
Termination rank for the existing restart/reduction policy. The arithmetic is
separate from the obligation that every actual running step decreases it.
`3^n` counts ternary polarity choices, not assignments. Freshness concerns the
retained learned clauses; deleting and relearning is handled by limit growth.
-/

def clauseUniverse : Nat → List (List (Option Bool))
  | 0 => [[]]
  | n + 1 => (clauseUniverse n).map (none :: ·) ++
      (clauseUniverse n).map (some true :: ·) ++ (clauseUniverse n).map (some false :: ·)

theorem clauseUniverse_length (n : Nat) : (clauseUniverse n).length = 3 ^ n := by
  induction n with
  | zero => simp [clauseUniverse]
  | succ n ih => simp [clauseUniverse, ih, Nat.pow_succ]; omega

theorem canonicalKey_length (n : Nat) (clause : Clause) :
    (canonicalKey n clause).length = n := by simp [canonicalKey]

def numericProgress (bound count limit : Nat) : Nat :=
  (bound + 1) * (bound - min bound limit) + (bound - count)

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
def variant (variables : Nat) (m : CDCL.Machine) : Rank :=
  (numericProgress (3 ^ variables) m.solver.nLemmas m.solver.maxLemmas,
   learningCredit m, 2 * variables - m.solver.assigned - m.solver.processed, phaseRank m.phase)

theorem numericProgress_learn {bound count limit : Nat} (room : count < bound) :
    numericProgress bound (count + 1) limit < numericProgress bound count limit := by
  unfold numericProgress
  omega

/-- This is a proposition to prove about the concrete algorithm, not a field
of `Inv` and not a successful fuel supplied by a caller. -/
def StepDecreases : Prop := ∀ formula before after,
  Inv formula before → Inv formula after → CDCL.step before = .running after →
    RankLT (variant (max 1 formula.numVars) after) (variant (max 1 formula.numVars) before)

end MicrosatLean.Verification
