import MicrosatLean.Formula
import Std.Sat.CNF

namespace MicrosatLean.Verification.Implementation.Native

/-!
Logical views of the executable representation. These definitions do not alter
the solver's packed storage or its literal encoding. Zero arena terminators
are excluded by well-formedness; declared variable bounds remain metadata.
-/

/-- Interpret the executable literal's variable and polarity. -/
def literalView (lit : Lit) : Std.Sat.Literal Nat :=
  (lit.var, lit % 2 == 0)

/-- Interpret an array of literals as a disjunction. -/
def clauseView (clause : Array Lit) : Std.Sat.CNF.Clause Nat :=
  .ofLiterals (clause.toList.map literalView)

/-- Interpret the original formula as a conjunction of clauses. -/
def formulaView (formula : Formula) : Std.Sat.CNF Nat :=
  ⟨formula.clauses.map clauseView⟩

/-- A total extension of a finite model to all variable identifiers. -/
def assignment (model : Array Bool) (var : Nat) : Bool := model.getD var false

/-- Every literal denotes a declared, nonzero variable. -/
def ClauseWellFormed (n : Nat) (clause : Array Lit) : Prop :=
  ∀ lit ∈ clause, 0 < lit.var ∧ lit.var ≤ n

def WellFormed (formula : Formula) : Prop :=
  ∀ clause ∈ formula.clauses, ClauseWellFormed formula.numVars clause

/-- The executable bounds precheck decides exactly the existing logical
input specification; it does not inspect a solver answer or a model. -/
theorem formula_wellFormed_iff (formula : Formula) :
    formula.wellFormed = true ↔ WellFormed formula := by
  simp only [Formula.wellFormed, Array.all_eq_true, decide_eq_true_eq]
  constructor
  · intro checked clause clauseMember lit litMember
    obtain ⟨i, beforeClause, value⟩ := Array.mem_iff_getElem.mp clauseMember
    obtain ⟨j, beforeLiteral, literalValue⟩ := Array.mem_iff_getElem.mp litMember
    have bounds := checked i beforeClause j (by simpa only [value] using beforeLiteral)
    simpa only [value, literalValue] using bounds
  · intro valid i beforeClause j beforeLiteral
    exact valid _ (Array.getElem_mem beforeClause) _ (Array.getElem_mem beforeLiteral)

theorem formula_wellFormed_false_iff (formula : Formula) :
    formula.wellFormed = false ↔ ¬WellFormed formula := by
  rw [← formula_wellFormed_iff]
  exact Bool.eq_false_iff

/-- The runtime branch is the finite Boolean bounds check. Its logical
certificate is erased, so arbitrary literal quantifiers need no choice. -/
instance wellFormedDecidable (formula : Formula) : Decidable (WellFormed formula) :=
  if checked : formula.wellFormed = true then
    isTrue ((formula_wellFormed_iff formula).mp checked)
  else isFalse (fun valid => checked ((formula_wellFormed_iff formula).mpr valid))

/-- The executable model includes the reserved zero slot and all declared variables. -/
def Covers (model : Array Bool) (n : Nat) : Prop := n < model.size

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

theorem clauseView_literals (clause : Array Lit) :
    (clauseView clause).literals = clause.toList.map literalView := by
  simp [clauseView]

theorem clauseView_mem {lit : Std.Sat.Literal Nat} {clause : Array Lit} :
    lit ∈ clauseView clause ↔ ∃ encoded ∈ clause, literalView encoded = lit := by
  simp [← Std.Sat.CNF.Clause.mem_literals_iff, clauseView_literals]

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

theorem formula_satisfiedBy_iff_sat (formula : Formula) (model : Array Bool)
    (h : WellFormed formula) :
    formula.satisfiedBy model = true ↔
      Std.Sat.CNF.Sat (assignment model) (formulaView formula) := by
  rw [formula_satisfiedBy_eq_eval formula model h]
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

/-- Encoded complementation agrees with standard literal complementation. -/
@[simp] theorem literalView_negate (lit : Lit) :
    literalView lit.negate = (literalView lit).negate := by
  have hmod : (lit ^^^ 1) % 2 = lit % 2 ^^^ 1 := by
    simpa using (Nat.xor_mod_two_pow (a := lit) (b := 1) (n := 1))
  apply Prod.ext
  · simp [literalView, Lit.negate, Lit.var, Nat.xor_div_two, Std.Sat.Literal.negate]
  · rcases Nat.mod_two_eq_zero_or_one lit with hzero | hone
    · simp [literalView, Lit.negate, Std.Sat.Literal.negate, hmod, hzero]
    · simp [literalView, Lit.negate, Std.Sat.Literal.negate, hmod, hone]

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

/-- Clause semantics depends on membership, rather than order or multiplicity. -/
theorem clauseView_sat_iff (clause : Array Lit) (a : Nat → Bool) :
    Std.Sat.CNF.Clause.Sat a (clauseView clause) ↔
      ∃ lit ∈ clause, a lit.var = (lit % 2 == 0) := by
  rw [Std.Sat.CNF.Clause.sat_iff_exists_mem_eq]
  constructor
  · rintro ⟨lit, hmem, hs⟩
    rcases clauseView_mem.mp hmem with ⟨encoded, hencoded, rfl⟩
    exact ⟨encoded, hencoded, hs⟩
  · rintro ⟨encoded, hencoded, hs⟩
    exact ⟨literalView encoded, clauseView_mem.mpr ⟨encoded, hencoded, rfl⟩, hs⟩

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

/-- Restrict an arbitrary logical assignment to the declared finite model. -/
def modelOfAssignment (n : Nat) (a : Nat → Bool) : Array Bool :=
  Array.ofFn fun i : Fin (n + 1) => a i.val

@[simp] theorem modelOfAssignment_covers (n : Nat) (a : Nat → Bool) :
    Covers (modelOfAssignment n a) n := by
  simp [Covers, modelOfAssignment]

theorem assignment_modelOfAssignment {n var : Nat} (a : Nat → Bool) (h : var ≤ n) :
    assignment (modelOfAssignment n a) var = a var := by
  unfold assignment
  rw [← Array.getElem_eq_getD (h := by simpa [modelOfAssignment] using Nat.lt_succ_of_le h)]
  simp [modelOfAssignment]

theorem clauseView_sat_modelOfAssignment {n : Nat} {clause : Array Lit}
    (h : ClauseWellFormed n clause) (a : Nat → Bool) :
    Std.Sat.CNF.Clause.Sat (assignment (modelOfAssignment n a)) (clauseView clause) ↔
      Std.Sat.CNF.Clause.Sat a (clauseView clause) := by
  simp only [clauseView_sat_iff]
  constructor
  · rintro ⟨lit, hlit, hs⟩
    exact ⟨lit, hlit, (assignment_modelOfAssignment a (h lit hlit).2) ▸ hs⟩
  · rintro ⟨lit, hlit, hs⟩
    exact ⟨lit, hlit, (assignment_modelOfAssignment a (h lit hlit).2).symm ▸ hs⟩

theorem formulaView_sat_modelOfAssignment {formula : Formula} (h : WellFormed formula)
    (a : Nat → Bool) :
    Std.Sat.CNF.Sat (assignment (modelOfAssignment formula.numVars a)) (formulaView formula) ↔
      Std.Sat.CNF.Sat a (formulaView formula) := by
  rw [Std.Sat.CNF.sat_iff_all_mem_sat, Std.Sat.CNF.sat_iff_all_mem_sat]
  constructor
  · intro hs clause hc
    rcases Array.mem_map.mp hc with ⟨encoded, hencoded, rfl⟩
    exact (clauseView_sat_modelOfAssignment (h encoded hencoded) a).mp (hs _ hc)
  · intro hs clause hc
    rcases Array.mem_map.mp hc with ⟨encoded, hencoded, rfl⟩
    exact (clauseView_sat_modelOfAssignment (h encoded hencoded) a).mpr (hs _ hc)

/-- Arbitrary standard models and covered executable models express the same
satisfiability problem, including empty formulas and unused declared variables. -/
theorem formulaView_sat_iff_exists_model {formula : Formula} (h : WellFormed formula) :
    (∃ a, Std.Sat.CNF.Sat a (formulaView formula)) ↔
      ∃ model, Covers model formula.numVars ∧ formula.satisfiedBy model = true := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨modelOfAssignment formula.numVars a, modelOfAssignment_covers _ _, ?_⟩
    exact (formula_satisfiedBy_iff_sat _ _ h).mpr
      ((formulaView_sat_modelOfAssignment h a).mpr ha)
  · rintro ⟨model, _, hm⟩
    exact ⟨assignment model, (formula_satisfiedBy_iff_sat _ _ h).mp hm⟩

theorem formulaView_unsat_iff {formula : Formula} (h : WellFormed formula) :
    Std.Sat.CNF.Unsat (formulaView formula) ↔
      ∀ model, Covers model formula.numVars → formula.satisfiedBy model = false := by
  rw [Std.Sat.CNF.unsat_iff_not_sat]
  constructor
  · intro hu model _
    apply Bool.eq_false_iff.mpr
    intro hm
    exact hu (assignment model) ((formula_satisfiedBy_iff_sat _ _ h).mp hm)
  · intro hu a ha
    have hm := hu (modelOfAssignment formula.numVars a) (modelOfAssignment_covers _ _)
    have hs := (formula_satisfiedBy_iff_sat _ _ h).mpr
      ((formulaView_sat_modelOfAssignment h a).mpr ha)
    simp [hm] at hs

end MicrosatLean.Verification.Implementation.Native
