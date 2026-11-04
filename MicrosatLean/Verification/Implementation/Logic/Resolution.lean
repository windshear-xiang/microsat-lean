import Std.Sat.CNF

namespace MicrosatLean.Verification.Implementation.Logic

open Std.Sat

/-!
Semantic rules used by conflict analysis and propagation. They describe clauses
with the standard library's semantics; refinement of the packed arena must show
that each executable operation implements the corresponding rule.
-/

/-- Resolve two clauses by removing the pivot and its complement. All
occurrences are removed, so the rule also applies before deduplication. -/
def resolvent [BEq α] (conflict reason : CNF.Clause α) (pivot : Literal α) : CNF.Clause α :=
  conflict.erase pivot ++ reason.erase pivot.negate

/-- If every other literal is false, a satisfied reason forces its head. -/
theorem forced_of_sat {a : α → Bool} {reason : CNF.Clause α} {head : Literal α}
    (hr : CNF.Clause.Sat a reason)
    (hrest : ∀ lit ∈ reason, lit ≠ head → a lit.1 ≠ lit.2) :
    a head.1 = head.2 := by
  obtain ⟨lit, hmem, hval⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp hr
  by_cases heq : lit = head
  · simpa [heq] using hval
  · exact False.elim (hrest lit hmem heq hval)

/-- A root conflict excludes all models of the input formula. -/
theorem unsat_of_root_conflict {formula : CNF α} {conflict : CNF.Clause α}
    (hc : CNF.EntailsClause formula conflict)
    (hfalse : ∀ a, CNF.Sat a formula → ∀ lit ∈ conflict, a lit.1 ≠ lit.2) :
    CNF.Unsat formula := by
  apply CNF.unsat_iff_not_sat.mpr
  intro a ha
  exact CNF.Clause.not_sat_iff_forall_mem_ne.mpr (hfalse a ha) (hc a ha)

end MicrosatLean.Verification.Implementation.Logic
