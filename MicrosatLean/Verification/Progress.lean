import MicrosatLean.Verification.Invariant
import MicrosatLean.Verification.Progress.Rank

namespace MicrosatLean.Verification

/-!
The shared rank is defined in Progress/Rank so both proof layers use it without
depending on each other's invariants. This module states the concrete
step-decrease obligation and the finite ternary clause-space interpretation.
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

/-- This is a proposition to prove about the concrete algorithm, not a field
of `Inv` and not a successful fuel supplied by a caller. -/
def StepDecreases : Prop := ∀ formula before after,
  Inv formula before → Inv formula after → CDCL.step before = .running after →
    RankLT (variant (max 1 formula.numVars) after) (variant (max 1 formula.numVars) before)

end MicrosatLean.Verification
