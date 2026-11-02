import Std.Sat.CNF

namespace MicrosatLean.Verification.Implementation.Native.Logic

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

/-- Binary resolution preserves every common model of its two premises. -/
theorem sat_resolvent [DecidableEq α] {a : α → Bool}
    {conflict reason : CNF.Clause α} (pivot : Literal α)
    (hc : CNF.Clause.Sat a conflict) (hr : CNF.Clause.Sat a reason) :
    CNF.Clause.Sat a (resolvent conflict reason pivot) := by
  obtain ⟨lit, hmem, hval⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp hc
  by_cases hp : pivot = lit
  · subst lit
    obtain ⟨other, hother, hotherVal⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp hr
    have hne : pivot.negate ≠ other := by
      intro heq
      subst other
      simp [Literal.negate, hval] at hotherVal
    exact CNF.Clause.sat_append_right
      (CNF.Clause.sat_of_mem_of_eq (CNF.Clause.mem_erase_iff.mpr ⟨hne, hother⟩) hotherVal)
  · exact CNF.Clause.sat_append_left
      (CNF.Clause.sat_of_mem_of_eq (CNF.Clause.mem_erase_iff.mpr ⟨hp, hmem⟩) hval)

theorem entails_resolvent [DecidableEq α] {formula : CNF α}
    {conflict reason : CNF.Clause α} (pivot : Literal α)
    (hc : CNF.EntailsClause formula conflict) (hr : CNF.EntailsClause formula reason) :
    CNF.EntailsClause formula (resolvent conflict reason pivot) :=
  fun a ha => sat_resolvent pivot (hc a ha) (hr a ha)

/-- Learning a resolvent preserves exactly the models of the database. -/
theorem add_resolvent_biEntails [DecidableEq α] {formula : CNF α}
    {conflict reason : CNF.Clause α} (pivot : Literal α)
    (hc : CNF.EntailsClause formula conflict) (hr : CNF.EntailsClause formula reason) :
    CNF.BiEntails formula (formula.add (resolvent conflict reason pivot)) :=
  ⟨CNF.entails_add_of_entails_clause _ _ (entails_resolvent pivot hc hr),
    CNF.add_entails_left⟩

/-- If every other literal is false, a satisfied reason forces its head. -/
theorem forced_of_sat {a : α → Bool} {reason : CNF.Clause α} {head : Literal α}
    (hr : CNF.Clause.Sat a reason)
    (hrest : ∀ lit ∈ reason, lit ≠ head → a lit.1 ≠ lit.2) :
    a head.1 = head.2 := by
  obtain ⟨lit, hmem, hval⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp hr
  by_cases heq : lit = head
  · simpa [heq] using hval
  · exact False.elim (hrest lit hmem heq hval)

/-- An entailed reason can propagate under any fixed decision assumptions.
The assumptions are represented by an arbitrary predicate on total models. -/
theorem propagate_consequence {formula : CNF α} {reason : CNF.Clause α}
    {head : Literal α} {assumptions : (α → Bool) → Prop}
    (hr : CNF.EntailsClause formula reason)
    (hrest : ∀ a, CNF.Sat a formula → assumptions a →
      ∀ lit ∈ reason, lit ≠ head → a lit.1 ≠ lit.2) :
    ∀ a, CNF.Sat a formula → assumptions a → a head.1 = head.2 :=
  fun a ha hd => forced_of_sat (hr a ha) (hrest a ha hd)

/-- Root propagation is unconditional when the other literals are false in
every model of the input formula. -/
theorem root_propagate_consequence {formula : CNF α} {reason : CNF.Clause α}
    {head : Literal α} (hr : CNF.EntailsClause formula reason)
    (hrest : ∀ a, CNF.Sat a formula →
      ∀ lit ∈ reason, lit ≠ head → a lit.1 ≠ lit.2) :
    ∀ a, CNF.Sat a formula → a head.1 = head.2 :=
  fun a ha => forced_of_sat (hr a ha) (hrest a ha)

/-- A root conflict excludes all models of the input formula. -/
theorem unsat_of_root_conflict {formula : CNF α} {conflict : CNF.Clause α}
    (hc : CNF.EntailsClause formula conflict)
    (hfalse : ∀ a, CNF.Sat a formula → ∀ lit ∈ conflict, a lit.1 ≠ lit.2) :
    CNF.Unsat formula := by
  apply CNF.unsat_iff_not_sat.mpr
  intro a ha
  exact CNF.Clause.not_sat_iff_forall_mem_ne.mpr (hfalse a ha) (hc a ha)

end MicrosatLean.Verification.Implementation.Native.Logic
