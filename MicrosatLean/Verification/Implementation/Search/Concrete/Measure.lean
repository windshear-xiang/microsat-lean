import MicrosatLean.Verification.Progress.Rank

namespace MicrosatLean.Verification.Implementation.Search.Concrete

/-!
Arithmetic for the existing learned-clause policy. This module does not prove
that learned clauses are fresh, that the active database has a finite cardinality
bound, or that control transitions decrease a global search measure. Those facts
must be established from the executable-state invariants before these lemmas can
be used to prove termination of the solver.
-/

/-- Unused growth in the lemma limit, saturated at a finite clause bound. -/
def capacityDebt (bound limit : Nat) : Nat := bound - min bound limit

/-- Remaining distinct clauses that could be learned without forgetting. -/
def clauseDebt (bound count : Nat) : Nat := bound - count

theorem clauseDebt_le (bound count : Nat) : clauseDebt bound count ≤ bound := by
  exact Nat.sub_le _ _

theorem clauseDebt_lt_of_count_lt {bound before after : Nat}
    (hCount : before < after) (hBound : after ≤ bound) :
    clauseDebt bound after < clauseDebt bound before := by
  unfold clauseDebt
  omega

/-- Strict growth of a limit below the clause bound decreases its saturated
debt, including when the new limit reaches or exceeds the bound. -/
theorem capacityDebt_lt_of_limit_lt {bound before after : Nat}
    (hBefore : before < bound) (hGrowth : before < after) :
    capacityDebt bound after < capacityDebt bound before := by
  unfold capacityDebt
  omega

/-- A fresh learned clause decreases the measure while the limit is unchanged.
The finite bound is required for the increased count, so subtraction cannot
saturate before witnessing progress. -/
theorem numericProgress_lt_of_learn {bound countBefore countAfter limit : Nat}
    (hCount : countBefore < countAfter) (hBound : countAfter ≤ bound) :
    numericProgress bound countAfter limit < numericProgress bound countBefore limit := by
  exact Nat.add_lt_add_left (clauseDebt_lt_of_count_lt hCount hBound) _

/-- Raising the limit under database pressure dominates arbitrary forgetting.
No hypothesis on the new count is necessary for this arithmetic conclusion. -/
theorem numericProgress_lt_of_reduce
    {bound countBefore countAfter limitBefore limitAfter : Nat}
    (hBound : countBefore ≤ bound) (hPressure : limitBefore < countBefore)
    (hGrowth : limitBefore < limitAfter) :
    numericProgress bound countAfter limitAfter <
      numericProgress bound countBefore limitBefore := by
  have hDebt : capacityDebt bound limitAfter < capacityDebt bound limitBefore :=
    capacityDebt_lt_of_limit_lt (by omega) hGrowth
  unfold numericProgress
  calc
    (bound + 1) * capacityDebt bound limitAfter + clauseDebt bound countAfter
        ≤ (bound + 1) * capacityDebt bound limitAfter + bound :=
      Nat.add_le_add_left (clauseDebt_le bound countAfter) _
    _ < (bound + 1) * capacityDebt bound limitAfter + (bound + 1) := by omega
    _ = (bound + 1) * (capacityDebt bound limitAfter + 1) := by
      simp [Nat.mul_add]
    _ ≤ (bound + 1) * capacityDebt bound limitBefore :=
      Nat.mul_le_mul_left _ (by omega)
    _ ≤ (bound + 1) * capacityDebt bound limitBefore + clauseDebt bound countBefore :=
      Nat.le_add_right _ _

theorem clauseProgress_lt_of_learn {bound : Nat} {before after : CDCL.State}
    (hLimit : after.maxLemmas = before.maxLemmas)
    (hCount : before.nLemmas < after.nLemmas) (hBound : after.nLemmas ≤ bound) :
    clauseProgress bound after < clauseProgress bound before := by
  simp only [clauseProgress, hLimit]
  exact numericProgress_lt_of_learn hCount hBound

theorem clauseProgress_lt_of_reduce {bound : Nat} {before after : CDCL.State}
    (hBound : before.nLemmas ≤ bound)
    (hPressure : before.maxLemmas < before.nLemmas)
    (hGrowth : before.maxLemmas < after.maxLemmas) :
    clauseProgress bound after < clauseProgress bound before := by
  exact numericProgress_lt_of_reduce hBound hPressure hGrowth

/-- The limit expression used in `State.reduceDB`. This arithmetic view does
not yet establish the counter projection of the complete compaction function. -/
def scheduledLimit (count limit : Nat) : Nat :=
  if count > limit then limit + 300 * ((count - limit + 299) / 300) else limit

theorem scheduledLimit_strict_of_pressure {count limit : Nat} (h : limit < count) :
    limit < scheduledLimit count limit := by
  unfold scheduledLimit
  split <;> omega

end MicrosatLean.Verification.Implementation.Search.Concrete
