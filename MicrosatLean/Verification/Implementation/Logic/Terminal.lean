import MicrosatLean.Verification.Transitions

namespace MicrosatLean.Verification.Implementation.Logic

/-!
The two terminal gates use only the logical invariant. Completeness makes a
model-false literal false on the trail; unit closure then excludes a false
nonempty clause. At a root conflict, every trail assignment holds in every
input model, contradicting the input-entailed conflict clause.
-/

private theorem falseIn_of_model_false {state : LogicalState} {valuation : Assignment}
    (complete : Complete state) (compatible : Compatible valuation state.trueTrail)
    {lit : Literal} (bound : LiteralBound state.numVars lit)
    (falseValue : valuation lit.1 ≠ lit.2) : FalseIn state.trueTrail lit := by
  obtain ⟨assigned, member, sameVariable⟩ := complete lit.1 bound.1 bound.2
  have assignedValue := compatible assigned member
  have different : assigned.2 ≠ lit.2 := by
    intro samePolarity
    apply falseValue
    rw [← sameVariable, assignedValue, samePolarity]
  have opposite : assigned.2 = !lit.2 := by
    cases left : assigned.2 <;> cases right : lit.2 <;> simp_all
  have same : assigned = lit.negate := Prod.ext sameVariable opposite
  change lit.negate ∈ state.trueTrail
  rw [← same]
  exact member

private theorem closed_clause_sat {state : LogicalState} {valuation : Assignment}
    (complete : Complete state) (compatible : Compatible valuation state.trueTrail)
    {clause : Clause} (nonempty : clause.literals ≠ [])
    (declared : ∀ lit ∈ clause, LiteralBound state.numVars lit)
    (closed : UnitClosed state.trueTrail clause) : Std.Sat.CNF.Clause.Sat valuation clause := by
  classical
  apply Classical.byContradiction
  intro unsatisfied
  have falseValues := Std.Sat.CNF.Clause.not_sat_iff_forall_mem_ne.mp unsatisfied
  have falseTrail : ∀ lit ∈ clause, FalseIn state.trueTrail lit := by
    intro lit member
    exact falseIn_of_model_false complete compatible (declared lit member) (falseValues lit member)
  cases contents : clause.literals with
  | nil => exact nonempty contents
  | cons head rest =>
    have member : head ∈ clause := by
      rw [← Std.Sat.CNF.Clause.mem_literals_iff, contents]
      exact List.mem_cons_self
    have trueTrail := closed head member (fun lit member _ => falseTrail lit member)
    exact falseValues head member (compatible head trueTrail)

private theorem entailed_entry {input : CNF} {state : LogicalState}
    (valid : SemanticInv input state) {clause : Clause} (member : clause ∈ state.database) :
    Std.Sat.CNF.EntailsClause input clause := by
  intro valuation satisfied
  rcases List.mem_append.mp member with original | learned
  · exact (databaseView_sat_iff state.original valuation).mp (valid.original.1 valuation satisfied)
      clause original
  · exact (databaseView_sat_iff state.learned valuation).mp (valid.learned valuation satisfied)
      clause learned

theorem terminal : TerminalSoundness := by
  intro formula state result valid terminalGate
  cases result with
  | sat model stats =>
    obtain ⟨coverage, compatible, complete, closed⟩ := terminalGate
    refine ⟨coverage, ?_⟩
    apply valid.original.2
    apply (databaseView_sat_iff state.original (assignment model)).mpr
    intro clause member
    have stored : clause ∈ state.database := List.mem_append.mpr (Or.inl member)
    exact closed_clause_sat complete compatible (valid.nonempty clause stored)
      (valid.declaredClauses clause stored) (closed clause stored)
  | unsat stats =>
    obtain ⟨allRoots, clause, stored, conflict⟩ := terminalGate
    apply Std.Sat.CNF.unsat_iff_not_sat.mpr
    intro valuation satisfied
    have compatible : Compatible valuation state.trueTrail := by
      intro lit member
      apply valid.roots lit ?_ valuation satisfied
      simpa only [prefixLiterals, allRoots, List.take_length, LogicalState.trueTrail] using member
    obtain ⟨lit, member, trueValue⟩ := Std.Sat.CNF.Clause.sat_iff_exists_mem_eq.mp
      (entailed_entry valid stored valuation satisfied)
    have falseValue := compatible lit.negate (conflict lit member)
    change valuation lit.1 = !lit.2 at falseValue
    rw [trueValue] at falseValue
    exact (show ∀ polarity : Bool, polarity ≠ !polarity by decide) _ falseValue

end MicrosatLean.Verification.Implementation.Logic
