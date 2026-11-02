import MicrosatLean.Verification.Specification

namespace MicrosatLean.Verification.Implementation.Native

/-!
Logical views of the executable representation. These definitions do not alter
the solver's packed storage or its literal encoding. Zero arena terminators
are excluded by well-formedness; declared variable bounds remain metadata.
-/

theorem assignment_eq_getElem (model : Array Bool) {var : Nat}
    (h : var < model.size) : assignment model var = model[var] := by
  exact (Array.getElem_eq_getD false).symm

theorem literal_ne_zero {lit : Lit} (h : 0 < lit.var) : lit ≠ 0 := by
  intro hz
  simp [hz, Lit.var] at h

/-- The semantic bridge is stronger than the operational bounds requirement:
both logical evaluations use the same false default outside a finite model. -/
theorem literal_satisfiedBy_eq_eval (lit : Lit) (model : Array Bool)
    (h : 0 < lit.var) :
    lit.satisfiedBy model =
      (assignment model (literalView lit).1 == (literalView lit).2) := by
  simp [Lit.satisfiedBy, literalView, assignment, literal_ne_zero h,
    Array.getElem!_eq_getD]

theorem clause_satisfiedBy_eq_eval (clause : Array Lit) (model : Array Bool)
    {n : Nat} (h : ClauseWellFormed n clause) :
    (clause.any fun lit => lit.satisfiedBy model) =
      Std.Sat.CNF.Clause.eval (assignment model) (clauseView clause) := by
  simp only [Std.Sat.CNF.Clause.eval, clauseView_literals, List.any_map,
    Array.any_toList, Function.comp_def]
  rw [Bool.eq_iff_iff]
  simp only [Array.any_eq_true]
  constructor
  · rintro ⟨i, hi, hs⟩
    exact ⟨i, hi, (literal_satisfiedBy_eq_eval _ model (h _ (Array.getElem_mem hi)).1) ▸ hs⟩
  · rintro ⟨i, hi, hs⟩
    exact ⟨i, hi, (literal_satisfiedBy_eq_eval _ model (h _ (Array.getElem_mem hi)).1).symm ▸ hs⟩

theorem formula_satisfiedBy_eq_eval (formula : Formula) (model : Array Bool)
    (h : WellFormed formula) :
    formula.satisfiedBy model = Std.Sat.CNF.eval (assignment model) (formulaView formula) := by
  simp only [Formula.satisfiedBy, Std.Sat.CNF.eval, formulaView, Array.all_map,
    Function.comp_def]
  rw [Bool.eq_iff_iff]
  simp only [Array.all_eq_true]
  constructor
  · intro hs i hi
    exact (clause_satisfiedBy_eq_eval _ model (h _ (Array.getElem_mem hi))) ▸ hs i hi
  · intro hs i hi
    exact (clause_satisfiedBy_eq_eval _ model (h _ (Array.getElem_mem hi))).symm ▸ hs i hi

theorem clause_satisfiedBy_iff_sat (clause : Array Lit) (model : Array Bool)
    {n : Nat} (h : ClauseWellFormed n clause) :
    (clause.any fun lit => lit.satisfiedBy model) = true ↔
      Std.Sat.CNF.Clause.Sat (assignment model) (clauseView clause) := by
  rw [clause_satisfiedBy_eq_eval clause model h]
  rfl


@[simp] theorem clauseView_empty : clauseView #[] = .empty := by
  simp [clauseView, Std.Sat.CNF.Clause.ofLiterals]

@[simp] theorem formulaView_no_clauses (n : Nat) :
    formulaView ⟨n, #[]⟩ = .empty := by
  simp [formulaView, Std.Sat.CNF.empty]

theorem WellFormed.clause {formula : Formula} (h : WellFormed formula)
    {clause : Array Lit} (hc : clause ∈ formula.clauses) :
    ClauseWellFormed formula.numVars clause := h clause hc

theorem ClauseWellFormed.literal_bound {n : Nat} {clause : Array Lit}
    (h : ClauseWellFormed n clause) {lit : Lit} (hl : lit ∈ clause)
    {model : Array Bool} (hm : Covers model n) : lit.var < model.size :=
  Nat.lt_of_le_of_lt (h lit hl).2 hm


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

@[simp] theorem formulaView_push (formula : Formula) (clause : Array Lit) :
    formulaView { formula with clauses := formula.clauses.push clause } =
      (formulaView formula).add (clauseView clause) := by
  simp [formulaView, Std.Sat.CNF.add]

/-- Adding an entailed clause preserves exactly the original models. -/
theorem formulaView_push_biEntails (formula : Formula) (clause : Array Lit)
    (h : Std.Sat.CNF.EntailsClause (formulaView formula) (clauseView clause)) :
    Std.Sat.CNF.BiEntails (formulaView formula)
      (formulaView { formula with clauses := formula.clauses.push clause }) := by
  rw [formulaView_push]
  exact ⟨Std.Sat.CNF.entails_add_of_entails_clause _ _ h, Std.Sat.CNF.add_entails_left⟩

theorem formulaView_push_tautology_biEntails (formula : Formula) (clause : Array Lit)
    {lit : Lit} (hpos : lit ∈ clause) (hneg : lit.negate ∈ clause) :
    Std.Sat.CNF.BiEntails (formulaView formula)
      (formulaView { formula with clauses := formula.clauses.push clause }) :=
  formulaView_push_biEntails formula clause
    (Std.Sat.CNF.entails_clause_of_forall_sat (clauseView_sat_of_complement hpos hneg))

end MicrosatLean.Verification.Implementation.Native
