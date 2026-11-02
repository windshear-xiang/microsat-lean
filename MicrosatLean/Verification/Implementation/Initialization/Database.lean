import MicrosatLean.Verification.Implementation.Initialization.Outcome
import MicrosatLean.Verification.Implementation.Representation.DatabaseUpdates
import MicrosatLean.Verification.Implementation.Representation.Meaning

namespace MicrosatLean.Verification.Implementation.Initialization

open CDCL Representation Std.Sat

/-- Only clauses preceding the current executable loop index have been
represented in the arena. Future clauses impose no invariant yet. -/
def inputPrefix (formula : Formula) (index : Nat) : Std.Sat.CNF Nat :=
  ⟨(formula.clauses.extract 0 index).map clauseView⟩

@[simp] theorem inputPrefix_zero (formula : Formula) : inputPrefix formula 0 = CNF.empty := by
  simp [inputPrefix, CNF.empty]

@[simp] theorem inputPrefix_all (formula : Formula) :
    inputPrefix formula formula.clauses.size = formulaView formula := by
  simp [inputPrefix, formulaView]

theorem inputPrefix_succ {formula : Formula} {index : Nat} (within : index < formula.clauses.size) :
    inputPrefix formula (index + 1) =
      (inputPrefix formula index).add (clauseView formula.clauses[index]!) := by
  rw [CNF.Internal.ext_iff]
  change (formula.clauses.extract 0 (index + 1)).map clauseView =
    ((formula.clauses.extract 0 index).map clauseView).push (clauseView formula.clauses[index]!)
  rw [Array.extract_succ_right (by omega) within]
  simp only [Array.map_push, getElem!_pos formula.clauses index within]

/-- The packed original database represents exactly the input prefix already
visited by initialization. Tautologies need no stored database entry. -/
def DatabasePrefix (formula : Formula) (index : Nat) (s : State) : Prop :=
  ∃ original, Database s original [] ∧
    CNF.BiEntails (inputPrefix formula index) (databaseView original)

theorem prefix_skip {formula : Formula} {index stamp : Nat} {old : Array Nat}
    {normalized : NormalizedClause} {original : List StoredClause}
    (within : index < formula.clauses.size)
    (meaning : CNF.BiEntails (inputPrefix formula index) (databaseView original))
    (spec : NormalizationSpec formula.numVars stamp old formula.clauses[index]! normalized)
    (tautology : normalized.tautology = true) :
    CNF.BiEntails (inputPrefix formula (index + 1)) (databaseView original) := by
  rw [inputPrefix_succ within]
  constructor
  · intro a model
    exact meaning.1 a (CNF.sat_add.mp model).2
  · intro a model
    exact CNF.sat_add.mpr ⟨spec.tautology_sat tautology a, meaning.2 a model⟩

theorem prefix_add {formula : Formula} {index stamp : Nat} {old : Array Nat}
    {normalized : NormalizedClause} {original : List StoredClause} (id : Nat)
    (within : index < formula.clauses.size)
    (meaning : CNF.BiEntails (inputPrefix formula index) (databaseView original))
    (spec : NormalizationSpec formula.numVars stamp old formula.clauses[index]! normalized) :
    CNF.BiEntails (inputPrefix formula (index + 1))
      (databaseView (original ++ [⟨id, normalized.lits⟩])) := by
  rw [inputPrefix_succ within, databaseView_append_singleton]
  constructor
  · intro a model
    obtain ⟨clause, before⟩ := CNF.sat_add.mp model
    exact CNF.sat_add.mpr ⟨(spec.preserves_sat a).mpr clause, meaning.1 a before⟩
  · intro a model
    obtain ⟨clause, before⟩ := CNF.sat_add.mp model
    exact CNF.sat_add.mpr ⟨(spec.preserves_sat a).mp clause, meaning.2 a before⟩

inductive InitializationDatabaseChecked (formula : Formula) (index : Nat) :
    InitializationAccumulator → Prop where
  | stopped (s : State) (stamps : Array Nat) :
      InitializationDatabaseChecked formula index (some none, s, stamps)
  | ready (s : State) (stamps : Array Nat)
      (invariant : InitializationLoopInvariant formula index s stamps)
      (database : DatabasePrefix formula index s) :
      InitializationDatabaseChecked formula index (none, s, stamps)

end MicrosatLean.Verification.Implementation.Initialization
