import MicrosatLean.Verification.Invariant
import MicrosatLean.Verification.Progress.Rank

namespace MicrosatLean.Verification

/-!
The shared rank is defined in Progress/Rank so both proof layers use it without
depending on each other's invariants. The finite clause bound is proved in
Implementation/Logic/ClauseSpace: `3^n` counts absent/positive/negative choices
for each variable. Freshness concerns retained learned clauses; deleting and
relearning is handled by limit growth.
-/

/-- This is a proposition to prove about the concrete algorithm, not a field
of `Inv` and not a successful fuel supplied by a caller. -/
def StepDecreases : Prop := ∀ formula before after,
  Inv formula before → Inv formula after → CDCL.step before = .running after →
    RankLT (variant (max 1 formula.numVars) after) (variant (max 1 formula.numVars) before)

end MicrosatLean.Verification
