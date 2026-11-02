import MicrosatLean.Verification.Specification

namespace MicrosatLean.Verification.Implementation

/-!
Auxiliary lemmas for the canonical views in Specification. The executable
literal encoding and standard CNF semantics each have one shared definition.
-/

theorem assignment_eq_getElem (model : Array Bool) {var : Nat}
    (h : var < model.size) : assignment model var = model[var] := by
  exact (Array.getElem_eq_getD false).symm

@[simp] theorem clauseView_empty : clauseView #[] = .empty := by
  simp [clauseView, Std.Sat.CNF.Clause.ofLiterals]

theorem WellFormed.clause {formula : Formula} (h : WellFormed formula)
    {clause : Array Lit} (hc : clause ∈ formula.clauses) :
    ClauseWellFormed formula.numVars clause := h clause hc

theorem literalView_injective : Function.Injective literalView := by
  intro left right heq
  have hvar := congrArg Prod.fst heq
  have hpol := congrArg Prod.snd heq
  dsimp [literalView, Lit.var] at hvar hpol
  have hzero : (left % 2 = 0) ↔ (right % 2 = 0) := by
    simpa using Bool.eq_iff_iff.mp hpol
  have hmod : left % 2 = right % 2 := by
    rcases Nat.mod_two_eq_zero_or_one left with hleft | hleft
    · rw [hleft, hzero.mp hleft]
    · rcases Nat.mod_two_eq_zero_or_one right with hright | hright
      · have := hzero.mpr hright
        simp [hleft] at this
      · rw [hleft, hright]
  rw [← Nat.mod_add_div left 2, ← Nat.mod_add_div right 2]
  rw [hmod, hvar]

theorem clauseView_sat_iff_of_mem_iff {left right : Array Lit}
    (h : ∀ lit, lit ∈ left ↔ lit ∈ right) (a : Nat → Bool) :
    Std.Sat.CNF.Clause.Sat a (clauseView left) ↔
      Std.Sat.CNF.Clause.Sat a (clauseView right) := by
  simp only [clauseView_sat_iff, h]

theorem clauseView_sat_of_complement {clause : Array Lit} {lit : Lit}
    (hpos : lit ∈ clause) (hneg : lit.negate ∈ clause) :
    ∀ a, Std.Sat.CNF.Clause.Sat a (clauseView clause) := by
  apply Std.Sat.CNF.Clause.sat_of_mem_of_mem_neg
    (atom := (literalView lit).1) (pol := (literalView lit).2)
  · exact clauseView_mem.mpr ⟨lit, hpos, rfl⟩
  · exact clauseView_mem.mpr ⟨lit.negate, hneg, literalView_negate lit⟩

end MicrosatLean.Verification.Implementation
