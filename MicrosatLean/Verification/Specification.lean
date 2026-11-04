import MicrosatLean.CDCL.Search
import Std.Sat.CNF

namespace MicrosatLean.Verification

/-!
The specification boundary is a bounded `Formula`, not a DIMACS byte stream.
The views below preserve the original clauses, including duplicates, empty
clauses and tautologies. Normalization belongs to the initialization contract.
This file has no admitted proofs and does not change the executable encoding.
-/

abbrev Assignment := Nat → Bool
abbrev Literal := Std.Sat.Literal Nat
abbrev Clause := Std.Sat.CNF.Clause Nat
abbrev CNF := Std.Sat.CNF Nat

def literalView (lit : Lit) : Literal := (lit.var, lit % 2 == 0)

def clauseView (clause : Array Lit) : Clause :=
  .ofLiterals (clause.toList.map literalView)

def formulaView (formula : Formula) : CNF :=
  ⟨formula.clauses.map clauseView⟩

def assignment (model : Array Bool) : Assignment := fun var => model.getD var false

/-- Bounds for an executable clause, shared by normalization proofs. -/
def ClauseWellFormed (variables : Nat) (clause : Array Lit) : Prop :=
  ∀ lit ∈ clause, 0 < lit.var ∧ lit.var ≤ variables

def WellFormed (formula : Formula) : Prop :=
  ∀ clause ∈ formula.clauses, ∀ lit ∈ clause,
    0 < lit.var ∧ lit.var ≤ formula.numVars

theorem wellFormed_iff_check (formula : Formula) :
    WellFormed formula ↔ formula.wellFormed = true := by
  simp only [WellFormed, Formula.wellFormed, Array.all_eq_true]
  constructor
  · intro valid i hi j hj
    exact decide_eq_true (valid _ (Array.getElem_mem hi) _ (Array.getElem_mem hj))
  · intro checked clause member lit contained
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp member
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.mp contained
    exact of_decide_eq_true (checked i hi j hj)

/-- The decision procedure executes the existing finite bounds check. -/
instance (formula : Formula) : Decidable (WellFormed formula) :=
  if checked : formula.wellFormed = true then
    isTrue ((wellFormed_iff_check formula).mpr checked)
  else
    isFalse (fun valid => checked ((wellFormed_iff_check formula).mp valid))

def Covers (model : Array Bool) (variables : Nat) : Prop := variables < model.size

def Models (formula : Formula) (a : Assignment) : Prop :=
  Std.Sat.CNF.Sat a (formulaView formula)

def EntailsClause (formula : Formula) (clause : Array Lit) : Prop :=
  Std.Sat.CNF.EntailsClause (formulaView formula) (clauseView clause)

/-- Statistics are deliberately outside the functional correctness claim. -/
def ValidResult (formula : Formula) : CDCL.SolveResult → Prop
  | .sat model _ => Covers model formula.numVars ∧ Models formula (assignment model)
  | .unsat _ => Std.Sat.CNF.Unsat (formulaView formula)

theorem clauseView_literals (clause : Array Lit) :
    (clauseView clause).literals = clause.toList.map literalView := by
  simp [clauseView]

theorem clauseView_mem {lit : Literal} {clause : Array Lit} :
    lit ∈ clauseView clause ↔ ∃ encoded ∈ clause, literalView encoded = lit := by
  simp [← Std.Sat.CNF.Clause.mem_literals_iff, clauseView_literals]

theorem clauseView_sat_iff (clause : Array Lit) (a : Assignment) :
    Std.Sat.CNF.Clause.Sat a (clauseView clause) ↔
      ∃ lit ∈ clause, a lit.var = (lit % 2 == 0) := by
  rw [Std.Sat.CNF.Clause.sat_iff_exists_mem_eq]
  constructor
  · rintro ⟨lit, member, truth⟩
    obtain ⟨encoded, contained, rfl⟩ := clauseView_mem.mp member
    exact ⟨encoded, contained, truth⟩
  · rintro ⟨lit, contained, truth⟩
    exact ⟨literalView lit, clauseView_mem.mpr ⟨lit, contained, rfl⟩, truth⟩

theorem models_iff (formula : Formula) (a : Assignment) :
    Models formula a ↔ ∀ clause ∈ formula.clauses,
      ∃ lit ∈ clause, a lit.var = (lit % 2 == 0) := by
  simp only [Models, Std.Sat.CNF.sat_iff_all_mem_sat, formulaView]
  constructor
  · intro satisfied clause member
    exact (clauseView_sat_iff clause a).mp
      (satisfied _ (Array.mem_map.mpr ⟨clause, member, rfl⟩))
  · intro satisfied clause member
    obtain ⟨encoded, contained, rfl⟩ := Array.mem_map.mp member
    exact (clauseView_sat_iff encoded a).mpr (satisfied encoded contained)

@[simp] theorem literalView_negate (lit : Lit) :
    literalView lit.negate = (literalView lit).negate := by
  have remainder : (lit ^^^ 1) % 2 = lit % 2 ^^^ 1 := by
    simpa using (Nat.xor_mod_two_pow (a := lit) (b := 1) (n := 1))
  apply Prod.ext
  · simp [literalView, Lit.negate, Lit.var, Nat.xor_div_two, Std.Sat.Literal.negate]
  · rcases Nat.mod_two_eq_zero_or_one lit with even | odd
    · simp [literalView, Lit.negate, Std.Sat.Literal.negate, remainder, even]
    · simp [literalView, Lit.negate, Std.Sat.Literal.negate, remainder, odd]

theorem satisfiedBy_iff_models {formula : Formula} (valid : WellFormed formula)
    (model : Array Bool) : formula.satisfiedBy model = true ↔ Models formula (assignment model) := by
  rw [models_iff]
  simp only [Formula.satisfiedBy, Array.all_eq_true_iff_forall_mem,
    Array.any_eq_true]
  have literal (clause : Array Lit) (member : clause ∈ formula.clauses)
      (lit : Lit) (contained : lit ∈ clause) :
      lit.satisfiedBy model = true ↔ assignment model lit.var = (lit % 2 == 0) := by
    have nonzero : lit ≠ 0 := by
      intro zero
      have positive := (valid clause member lit contained).1
      simp [zero, Lit.var] at positive
    simp [Lit.satisfiedBy, nonzero, assignment, Array.getElem!_eq_getD]
  constructor
  · intro checked clause member
    obtain ⟨i, hi, truth⟩ := checked clause member
    exact ⟨clause[i], Array.getElem_mem hi,
      (literal clause member clause[i] (Array.getElem_mem hi)).mp truth⟩
  · intro satisfied clause member
    obtain ⟨lit, contained, truth⟩ := satisfied clause member
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp contained
    exact ⟨i, hi, (literal clause member clause[i] (Array.getElem_mem hi)).mpr truth⟩

/-- Restrict a total assignment without losing unused declared variables. -/
def modelOfAssignment (variables : Nat) (a : Assignment) : Array Bool :=
  Array.ofFn fun i : Fin (variables + 1) => a i.val

@[simp] theorem modelOfAssignment_covers (variables : Nat) (a : Assignment) :
    Covers (modelOfAssignment variables a) variables := by
  simp [Covers, modelOfAssignment]

theorem assignment_modelOfAssignment {variables var : Nat} (a : Assignment)
    (bound : var ≤ variables) : assignment (modelOfAssignment variables a) var = a var := by
  unfold assignment
  rw [← Array.getElem_eq_getD (h := by simpa [modelOfAssignment] using Nat.lt_succ_of_le bound)]
  simp [modelOfAssignment]

theorem models_restrict {formula : Formula} (valid : WellFormed formula) (a : Assignment) :
    Models formula (assignment (modelOfAssignment formula.numVars a)) ↔ Models formula a := by
  simp only [models_iff]
  constructor
  · intro satisfied clause member
    obtain ⟨lit, contained, truth⟩ := satisfied clause member
    exact ⟨lit, contained, (assignment_modelOfAssignment a (valid clause member lit contained).2) ▸ truth⟩
  · intro satisfied clause member
    obtain ⟨lit, contained, truth⟩ := satisfied clause member
    exact ⟨lit, contained, (assignment_modelOfAssignment a (valid clause member lit contained).2).symm ▸ truth⟩

theorem satisfiable_iff_complete_model {formula : Formula} (valid : WellFormed formula) :
    (∃ a, Models formula a) ↔
      ∃ model, Covers model formula.numVars ∧ formula.satisfiedBy model = true := by
  constructor
  · rintro ⟨a, satisfied⟩
    exact ⟨modelOfAssignment formula.numVars a, modelOfAssignment_covers _ _,
      (satisfiedBy_iff_models valid _).mpr ((models_restrict valid a).mpr satisfied)⟩
  · rintro ⟨model, _, satisfied⟩
    exact ⟨assignment model, (satisfiedBy_iff_models valid model).mp satisfied⟩

theorem unsat_iff_complete_models {formula : Formula} (valid : WellFormed formula) :
    Std.Sat.CNF.Unsat (formulaView formula) ↔
      ∀ model, Covers model formula.numVars → formula.satisfiedBy model = false := by
  rw [Std.Sat.CNF.unsat_iff_not_sat]
  constructor
  · intro unsat model _
    exact Bool.eq_false_iff.mpr (fun satisfied =>
      unsat (assignment model) ((satisfiedBy_iff_models valid model).mp satisfied))
  · intro unsat a satisfied
    have checked := unsat (modelOfAssignment formula.numVars a) (modelOfAssignment_covers _ _)
    have truth := (satisfiedBy_iff_models valid _).mpr ((models_restrict valid a).mpr satisfied)
    simp [checked] at truth

theorem valid_sat_passes_checker {formula : Formula} (valid : WellFormed formula)
    {model : Array Bool} {stats : CDCL.Stats} (result : ValidResult formula (.sat model stats)) :
    formula.satisfiedBy model = true := (satisfiedBy_iff_models valid model).mpr result.2

end MicrosatLean.Verification
