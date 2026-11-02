import MicrosatLean.Verification.Implementation.Native.Propagation.Closure
import MicrosatLean.Verification.Implementation.Native.Representation.Meaning

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation
open Std.Sat

/-- Propagation closure at a completion boundary concerns genuine stored
clauses, including learned clauses, rather than arbitrary arena suffixes. -/
def DatabaseNoConflict (s : State) (entries : List StoredClause) : Prop :=
  ∀ entry ∈ entries, ∃ lit ∈ entry.lits, s.mark lit = 0

theorem database_sat_of_complete_closed {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (sound : MarksSound s)
    (complete : AllVariablesAssigned s) (closed : DatabaseNoConflict s (original ++ learned)) :
    CNF.Sat (assignment s.phases) (databaseView (original ++ learned)) := by
  apply (databaseView_sat_iff _ _).mpr
  intro entry member
  obtain ⟨lit, hlit, unmarked⟩ := closed entry member
  have bounded := (database.layout.packed member).wellFormed lit hlit
  apply (clauseView_sat_iff _ _).mpr
  exact ⟨lit, hlit, true_of_unmarked sound complete bounded unmarked⟩

theorem input_sat_of_database_closed {s : State} {formula : Std.Sat.CNF Nat}
    {original learned : List StoredClause} (database : Database s original learned)
    (meaning : DatabaseMeaning formula original learned) (sound : MarksSound s)
    (complete : AllVariablesAssigned s) (closed : DatabaseNoConflict s (original ++ learned)) :
    CNF.Sat (assignment s.phases) formula :=
  meaning.combined.2 _ (database_sat_of_complete_closed database sound complete closed)

end MicrosatLean.Verification.Implementation.Native.Propagation
