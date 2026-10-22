import MicrosatLean.Verification.Initialization.Outcome
import MicrosatLean.Verification.Representation.DatabaseUpdates
import MicrosatLean.Verification.Representation.Meaning

namespace MicrosatLean.Verification.Initialization

open CDCL Representation Std.Sat

/-- Only clauses preceding the current executable loop index have been
represented in the arena. Future clauses impose no invariant yet. -/
def inputPrefix (formula : Formula) (index : Nat) : CNF Nat :=
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

theorem initialization_database_step {formula : Formula} (wellFormed : WellFormed formula)
    {index : Nat} (within : index < formula.clauses.size) {s : State} {stamps : Array Nat}
    (invariant : InitializationLoopInvariant formula index s stamps)
    (database : DatabasePrefix formula index s) {next : State} {nextStamps : Array Nat}
    (step : initializationBody formula index (none, s, stamps) =
      .ok (.yield (none, next, nextStamps))) : DatabasePrefix formula (index + 1) next := by
  have clauseMember : formula.clauses[index]! ∈ formula.clauses := by
    rw [getElem!_pos formula.clauses index within]
    exact Array.getElem_mem within
  have fresh : FreshStamp (index + 1) stamps := by
    refine ⟨by omega, ?_⟩
    intro i bound
    have previous := invariant.stampBound i bound
    omega
  obtain ⟨normalized, normalize, spec⟩ := normalizeClause_correct invariant.coverage fresh
    (wellFormed _ clauseMember)
  obtain ⟨original, stored, meaning⟩ := database
  by_cases tautology : normalized.tautology = true
  · have equal : s = next := by
      simpa [initializationBody, normalize, tautology, Bind.bind, Except.bind,
        Pure.pure, Except.pure, Except.map] using
        congrArg (fun result => result.map fun value => value.value.2.1) step
    subst next
    exact ⟨original, stored, prefix_skip within meaning spec tautology⟩
  · have notTautology : normalized.tautology = false := by
      cases equal : normalized.tautology <;> simp_all
    by_cases empty : normalized.lits.isEmpty = true
    · simp [initializationBody, normalize, notTautology, empty, Bind.bind, Except.bind,
        Pure.pure, Except.pure] at step
    · let added := s.addClause normalized.lits true
      have storedAdded : Database added.1
          (original ++ [⟨added.2, normalized.lits⟩]) [] := by
        apply stored.addOriginal invariant.state.reserved
        intro lit member
        have bounds := spec.wellFormed lit member
        exact ⟨bounds.1, Nat.le_trans bounds.2 (by rw [invariant.state.variables]; omega)⟩
      have meaningAdded := prefix_add added.2 within meaning spec
      have keepAdded : DatabasePrefix formula (index + 1) added.1 :=
        ⟨_, storedAdded, meaningAdded⟩
      have keepAssigned : DatabasePrefix formula (index + 1) (added.1.assign added.2 true) :=
        ⟨_, storedAdded.assign _ _, meaningAdded⟩
      by_cases unit : normalized.lits.size = 1
      · have headRead : normalized.lits[0]! = normalized.lits[0] :=
          getElem!_pos normalized.lits 0 (by omega)
        by_cases conflict : added.1.mark normalized.lits[0]! ≠ 0
        · have conflictIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] ≠ 0 := by
            simpa only [added, headRead] using conflict
          simp [initializationBody, normalize, notTautology, empty, unit,
            conflictIndex, Bind.bind, Except.bind, Pure.pure, Except.pure] at step
        · have unmarkedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] = 0 := by
            have unmarked : added.1.mark normalized.lits[0]! = 0 := by simpa using conflict
            simpa only [added, headRead] using unmarked
          by_cases assigned : added.1.mark normalized.lits[0]!.negate = 0
          · have assignedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0].negate = 0 := by
              simpa only [added, headRead] using assigned
            have equal : added.1.assign added.2 true = next := by
              simpa [initializationBody, normalize, notTautology, empty, unit, added,
                unmarkedIndex, assignedIndex, Bind.bind, Except.bind, Pure.pure, Except.pure,
                Except.map] using
                congrArg (fun result => result.map fun value => value.value.2.1) step
            exact equal ▸ keepAssigned
          · have assignedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0].negate ≠ 0 := by
              simpa only [added, headRead] using assigned
            have equal : added.1 = next := by
              simpa [initializationBody, normalize, notTautology, empty, unit, added,
                unmarkedIndex, assignedIndex, Bind.bind, Except.bind, Pure.pure, Except.pure,
                Except.map] using
                congrArg (fun result => result.map fun value => value.value.2.1) step
            exact equal ▸ keepAdded
      · have equal : added.1 = next := by
          simpa [initializationBody, normalize, notTautology, empty, unit, added,
            Bind.bind, Except.bind, Pure.pure, Except.pure, Except.map] using
            congrArg (fun result => result.map fun value => value.value.2.1) step
        exact equal ▸ keepAdded

inductive InitializationDatabaseChecked (formula : Formula) (index : Nat) :
    InitializationAccumulator → Prop where
  | stopped (s : State) (stamps : Array Nat) :
      InitializationDatabaseChecked formula index (some none, s, stamps)
  | ready (s : State) (stamps : Array Nat)
      (invariant : InitializationLoopInvariant formula index s stamps)
      (database : DatabasePrefix formula index s) :
      InitializationDatabaseChecked formula index (none, s, stamps)

/-- Iterate the actual initialization body while extending semantic coverage
one input clause at a time. Early UNSAT cannot produce a successful state. -/
theorem initialization_database_loop {formula : Formula} (wellFormed : WellFormed formula)
    (fuel start : Nat) (endBound : start + fuel ≤ formula.clauses.size)
    (s : State) (stamps : Array Nat) (invariant : InitializationLoopInvariant formula start s stamps)
    (database : DatabasePrefix formula start s) :
    ∃ result, forIn (List.range' start fuel) (none, s, stamps) (initializationBody formula) = .ok result ∧
      InitializationDatabaseChecked formula (start + fuel) result := by
  induction fuel generalizing start s stamps with
  | zero => exact ⟨_, rfl, .ready _ _ (by simpa using invariant) (by simpa using database)⟩
  | succ fuel ih =>
    obtain ⟨stepResult, step, checked⟩ := initialization_step wellFormed (by omega) invariant
    cases checked with
    | unsat next nextStamps _ =>
      exact ⟨_, by rw [List.range'_succ, List.forIn_cons, step]; rfl, .stopped _ _⟩
    | ready next nextStamps nextInvariant =>
      have nextDatabase := initialization_database_step wellFormed (by omega) invariant database step
      obtain ⟨result, run, resultChecked⟩ := ih (start + 1) (by omega) next nextStamps
        nextInvariant nextDatabase
      refine ⟨result, ?_, ?_⟩
      · rw [List.range'_succ, List.forIn_cons, step]
        exact run
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using resultChecked

theorem emptyState_databasePrefix (formula : Formula) (config : Config) :
    DatabasePrefix formula 0 (emptyState formula.numVars config) := by
  refine ⟨[], emptyState_database _ _, ?_⟩
  simp only [inputPrefix_zero, databaseView_nil]
  exact CNF.biEntails_refl

/-- A successful actual initialization has a complete original database whose
models are exactly the input models. No learned clauses have been allocated. -/
theorem initState_some_database {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (success : initState formula config = .ok (some s)) :
    ∃ original, Database s original [] ∧ DatabaseMeaning (formulaView formula) original [] := by
  let initial := emptyState formula.numVars config
  let stamps := Array.replicate (2 * (initial.nVars + 1)) 0
  have initialInvariant : InitializationLoopInvariant formula 0 initial stamps := by
    constructor
    · exact ⟨rfl, (emptyState_arenaBounds _ _).reserved, emptyState_rootMarks _ _ _⟩
    · dsimp [StampCoverage, stamps, initial, emptyState]
      simp
      omega
    · intro i within
      rw [getElem!_pos stamps i within]
      simp [stamps]
  obtain ⟨acc, run, checked⟩ := initialization_database_loop wellFormed formula.clauses.size 0
    (by omega) initial stamps initialInvariant (emptyState_databasePrefix formula config)
  cases checked with
  | stopped next nextStamps =>
    rw [initState_eq_loop, run] at success
    simp [finishInitialization, Functor.map, Except.map] at success
  | ready next nextStamps _ database =>
    have equal : next = s := by
      rw [initState_eq_loop, run] at success
      simpa [finishInitialization, Functor.map, Except.map] using success
    subst s
    obtain ⟨original, stored, meaning⟩ := database
    refine ⟨original, stored, ?_⟩
    constructor
    · simpa only [Nat.zero_add, inputPrefix_all] using meaning
    · simp only [databaseView_nil]
      exact CNF.entails_empty

end MicrosatLean.Verification.Initialization
