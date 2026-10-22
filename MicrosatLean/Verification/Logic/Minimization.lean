import Std.Sat.CNF

namespace MicrosatLean.Verification.Logic.Minimization

open Std.Sat

/-!
Sound ordered elimination of clause literals. The original list is ordered by
increasing trail position. A removed entry may depend on strictly earlier
original entries, but never on itself or on the whole original clause being
false. The proof derives those earlier facts by forward induction.

This logical rule does not establish that `CDCL.implied` or `CDCL.analyze`
implements its hypotheses. Their reason-graph and cache refinement remain
separate obligations.
-/

def Falsifies (a : α → Bool) (lit : Literal α) : Prop := a lit.1 ≠ lit.2

/-- Only entries at positions strictly below `i` are assumptions. -/
def PrefixFalse (a : α → Bool) (original : List (Literal α)) (i : Nat) : Prop :=
  ∀ j (hj : j < original.length), j < i → Falsifies a original[j]

/-- The semantic premise required of each removal. The candidate at `i` does
not occur among the supplied prefix assumptions. -/
def OrderedRemoval (formula : CNF α) (original : List (Literal α))
    (keep : Literal α → Bool) : Prop :=
  ∀ i (hi : i < original.length), keep original[i] = false →
    ∀ a, CNF.Sat a formula → PrefixFalse a original i → Falsifies a original[i]

/-- Falsity of retained literals propagates forward to every original entry. -/
theorem all_false_of_ordered_removal {formula : CNF α}
    {original : List (Literal α)} {keep : Literal α → Bool}
    (removal : OrderedRemoval formula original keep) {a : α → Bool}
    (model : CNF.Sat a formula)
    (retained : ∀ lit ∈ original.filter keep, Falsifies a lit) :
    ∀ lit ∈ original, Falsifies a lit := by
  have byIndex : ∀ i (hi : i < original.length), Falsifies a original[i] := by
    intro i
    induction i using Nat.strongRecOn with
    | ind i ih =>
      intro hi
      by_cases selected : keep original[i] = true
      · exact retained _ (List.mem_filter.mpr ⟨List.getElem_mem hi, selected⟩)
      · apply removal i hi (Bool.eq_false_iff.mpr selected) a model
        intro j hj earlier
        exact ih j earlier hj
  intro lit member
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp member
  exact byIndex i hi

/-- An entailed original disjunction remains entailed after ordered removal. -/
theorem entails_retained_of_ordered_removal {formula : CNF α}
    {original : List (Literal α)} {keep : Literal α → Bool}
    (entailed : CNF.EntailsClause formula (.ofLiterals original))
    (removal : OrderedRemoval formula original keep) :
    CNF.EntailsClause formula (.ofLiterals (original.filter keep)) := by
  intro a model
  by_cases satisfied : CNF.Clause.Sat a (.ofLiterals (original.filter keep))
  · exact satisfied
  · have retained : ∀ lit ∈ original.filter keep, Falsifies a lit := by
      intro lit member
      apply CNF.Clause.not_sat_iff_forall_mem_ne.mp satisfied lit
      simpa only [← CNF.Clause.mem_literals_iff, CNF.Clause.literals_ofLiterals] using member
    have allFalse := all_false_of_ordered_removal removal model retained
    have contradiction : ¬ CNF.Clause.Sat a (.ofLiterals original) := by
      apply CNF.Clause.not_sat_iff_forall_mem_ne.mpr
      intro lit member
      apply allFalse lit
      simpa only [← CNF.Clause.mem_literals_iff, CNF.Clause.literals_ofLiterals] using member
    exact False.elim (contradiction (entailed a model))

/-- The learned minimized clause preserves every model of the database. -/
theorem add_retained_biEntails {formula : CNF α}
    {original : List (Literal α)} {keep : Literal α → Bool}
    (entailed : CNF.EntailsClause formula (.ofLiterals original))
    (removal : OrderedRemoval formula original keep) :
    CNF.BiEntails formula (formula.add (.ofLiterals (original.filter keep))) :=
  ⟨CNF.entails_add_of_entails_clause _ _ (entails_retained_of_ordered_removal entailed removal),
    CNF.add_entails_left⟩

end MicrosatLean.Verification.Logic.Minimization
