import MicrosatLean.Verification.Implementation.Propagation.WatchSettlementBranches
import MicrosatLean.Verification.Implementation.Propagation.Effects

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL Representation Analysis Std.Sat

/-- Completing the current literal's list extends the processed prefix by
that actual trail entry, while retaining concrete active-trail truth witnesses. -/
theorem SettledPrefix.extend {s : State} {entries : List StoredClause}
    {heads : Nat → List Nat} {count : Nat} {lit : Lit}
    (settled : SettledPrefix s entries heads count)
    (current : ∀ ref ∈ heads lit, SettledWatch s entries s.assigned lit ref)
    (value : s.trail[count]! = lit) : SettledPrefix s entries heads (count + 1) := by
  intro query falseLit ref member
  obtain ⟨i, before, literal⟩ := falseLit
  by_cases old : i < count
  · exact settled query ⟨i, old, literal⟩ ref member
  · have equal : i = count := by omega
    subst i
    have same : lit = query := value.symm.trans literal
    exact (same ▸ current) ref member

end MicrosatLean.Verification.Implementation.Propagation
