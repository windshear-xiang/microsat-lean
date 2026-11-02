import MicrosatLean.Verification.Implementation.Native.Search.Decision
import MicrosatLean.Verification.Implementation.Native.Propagation.Closure
import MicrosatLean.Verification.Implementation.Native.Propagation.DatabaseClosure

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation
open Std.Sat

/-- The intended meaning of completed solver results. SAT includes a complete
finite model; UNSAT quantifies over all total standard-library assignments. -/
def ValidResult (formula : Formula) : SolveResult → Prop
  | .sat model _ => Covers model formula.numVars ∧ CNF.Sat (assignment model) (formulaView formula)
  | .unsat _ => CNF.Unsat (formulaView formula)

theorem validResult_sat_check {formula : Formula} (wellFormed : WellFormed formula)
    {model : Array Bool} {stats : Stats} (valid : ValidResult formula (.sat model stats)) :
    formula.satisfiedBy model = true :=
  (formula_satisfiedBy_iff_sat _ _ wellFormed).mpr valid.2

/-- The actual SAT guard is sound under propagation closure, mark/trail
agreement, and coverage of both the traversed suffix and earlier cursor prefix.
These are obligations of the search invariant, not assumptions of termination. -/
theorem validResult_sat_of_decision_zero {formula : Formula} {s : State}
    (wellFormed : WellFormed formula) (variables : formula.numVars ≤ s.nVars)
    (arrays : ArrayBounds s) (marks : MarkedOnTrail s) (phases : TrailPhases s)
    (closed : NoConflict s formula) {order : List Nat} (ordered : MTFOrder s order)
    (start : Nat)
    (hPrefix : ∀ i, i < start → i < order.length → AssignedVariable s (order.getD i 0))
    (finished : nextDecision s (order.getD start 0) = 0) :
    ValidResult formula (.sat s.phases s.stats) := by
  constructor
  · unfold Covers
    rw [arrays.phasesSize]
    omega
  · apply formula_sat_of_complete_closed wellFormed variables (marksSound_of_trail marks phases)
    · exact nextDecision_zero_all_assigned ordered start hPrefix finished
    · exact closed

/-- The packed database version of the SAT rule permits normalized originals
and learned clauses. Its model is transported back to the original input. -/
theorem validResult_sat_of_database {formula : Formula} {s : State}
    (variables : formula.numVars ≤ s.nVars) (arrays : ArrayBounds s)
    (marks : MarkedOnTrail s) (phases : TrailPhases s)
    {original learned : List StoredClause} (database : Database s original learned)
    (meaning : DatabaseMeaning (formulaView formula) original learned)
    (closed : DatabaseNoConflict s (original ++ learned))
    {order : List Nat} (ordered : MTFOrder s order) (start : Nat)
    (hPrefix : ∀ i, i < start → i < order.length → AssignedVariable s (order.getD i 0))
    (finished : nextDecision s (order.getD start 0) = 0) :
    ValidResult formula (.sat s.phases s.stats) := by
  constructor
  · unfold Covers
    rw [arrays.phasesSize]
    omega
  · exact input_sat_of_database_closed database meaning (marksSound_of_trail marks phases)
      (nextDecision_zero_all_assigned ordered start hPrefix finished) closed

/-- The root-conflict rule gives the UNSAT branch of the same result
specification, with no finite-model restriction on its conclusion. -/
theorem validResult_unsat_of_root_clause {formula : Formula} {s : State}
    {conflict : CNF.Clause Nat} (root : RootConsequences (formulaView formula) s)
    (entailed : CNF.EntailsClause (formulaView formula) conflict)
    (falseAtRoot : ∀ a, PrefixCompatible s a s.forced →
      ∀ lit ∈ conflict, a lit.1 ≠ lit.2) :
    ValidResult formula (.unsat s.stats) :=
  unsat_of_root_clause root entailed falseAtRoot

end MicrosatLean.Verification.Implementation.Native.Search
