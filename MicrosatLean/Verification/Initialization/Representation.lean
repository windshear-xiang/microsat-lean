import MicrosatLean.Verification.Initialization.Outcome
import MicrosatLean.Verification.Representation.Capacity
import MicrosatLean.Verification.Representation.DatabaseUpdates
import MicrosatLean.Verification.Representation.Order

namespace MicrosatLean.Verification.Initialization

open CDCL Representation Propagation

/-- The representation properties established by actual initialization,
independently of the semantic root consequences proved in `Outcome`. -/
structure InitializedRepresentation (s : State) : Prop where
  arrays : ArrayBounds s
  bounds : TrailBounds s
  active : ActiveTrail s
  distinct : DistinctTrailVariables s
  phases : TrailPhases s
  marked : MarkedOnTrail s
  order : MTFCoverage s
  reasons : ReasonClauses s

theorem emptyState_representation (numVars : Nat) (config : Config) :
    InitializedRepresentation (emptyState numVars config) :=
  ⟨emptyState_arrayBounds _ _, emptyState_trailBounds _ _, emptyState_activeTrail _ _,
    emptyState_distinctTrail _ _, emptyState_trailPhases _ _, emptyState_markedOnTrail _ _,
    emptyState_mtfCoverage _ _, emptyState_reasonClauses _ _⟩

theorem MarkedOnTrail.addClause {s : State} (marked : MarkedOnTrail s)
    (lits : Array Lit) (original : Bool) : MarkedOnTrail (s.addClause lits original).1 := by
  simpa only [MarkedOnTrail, State.mark, addClause_marks, addClause_assigned,
    addClause_trail] using marked

theorem ReasonClauses.addClause {s : State} (reasons : ReasonClauses s)
    (lits : Array Lit) (original : Bool) : ReasonClauses (s.addClause lits original).1 := by
  intro i before
  have old := reasons i (by simpa using before)
  rcases old with decision | ⟨reason, packed, member⟩
  · left
    simpa only [State.reason, addClause_reasons, addClause_trail] using decision
  · right
    refine ⟨reason, ?_, ?_⟩
    · simpa only [State.reason, addClause_reasons, addClause_trail] using packed.addClause lits
    · simpa only [addClause_trail] using member

theorem InitializedRepresentation.addClause {s : State} (valid : InitializedRepresentation s)
    (lits : Array Lit) (original : Bool) : InitializedRepresentation (s.addClause lits original).1 :=
  ⟨valid.arrays.addClause, valid.bounds.addClause, valid.active.addClause,
    valid.distinct.addClause, valid.phases.addClause, MarkedOnTrail.addClause valid.marked _ _,
    valid.order.addClause _ _, ReasonClauses.addClause valid.reasons _ _⟩

/-- Equal variables have exactly the two encoded polarities. -/
theorem literal_eq_or_negate_of_var_eq {left right : Lit} (same : left.var = right.var) :
    left = right ∨ left = right.negate := by
  have different := negate_ne right
  have leftEncoding := literal_encoding left
  have rightEncoding := literal_encoding right
  have negativeEncoding := literal_encoding right.negate
  rw [same] at leftEncoding
  rw [negate_var] at negativeEncoding
  rcases leftEncoding with positive | negative
  · rcases rightEncoding with positive' | negative'
    · exact Or.inl (positive.trans positive'.symm)
    · right
      rcases negativeEncoding with positive'' | negative''
      · exact positive.trans positive''.symm
      · exact False.elim (different (negative''.trans negative'.symm))
  · rcases rightEncoding with positive' | negative'
    · right
      rcases negativeEncoding with positive'' | negative''
      · exact False.elim (different (positive''.trans positive'.symm))
      · exact negative.trans negative''.symm
    · exact Or.inl (negative.trans negative'.symm)

theorem freshVariable_of_unmarked_pair {s : State} {lit : Lit} (active : ActiveTrail s)
    (head : s.mark lit = 0) (opposite : s.mark lit.negate = 0) :
    FreshVariable s lit.var := by
  intro i before same
  have marked := (active i before).2.1
  rcases literal_eq_or_negate_of_var_eq same with equal | equal
  · exact marked ((congrArg s.mark equal).trans head)
  · exact marked ((congrArg s.mark equal).trans opposite)

theorem ReasonClauses.assign {s : State} {id : Nat} {lits : Array Lit} {root : Bool}
    (reasons : ReasonClauses s) (arrays : ArrayBounds s)
    (packed : PackedClause s id lits) (member : s.db id ∈ lits)
    (space : s.assigned < s.trail.size) (fresh : FreshVariable s (Lit.var (s.db id))) :
    ReasonClauses (s.assign id root) := by
  have literal := packed.wellFormed _ member
  intro i before
  have bound : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [assign_trail_last space]
    have reason : (s.assign id root).reason (Lit.negate (s.db id)) = id := by
      simpa only [State.reason, negate_var] using
        (assign_reason (root := root) (arrays.variable_index literal.2).1)
    rw [reason]
    exact Or.inr ⟨lits, packed.frame rfl rfl, by simpa using member⟩
  · have earlier : i < s.assigned := by omega
    rw [assign_trail_prefix earlier]
    have reason : (s.assign id root).reason s.trail[i]! = s.reason s.trail[i]! := by
      exact Array.getElem!_set!_ne s.reasons _ _ _ (Ne.symm (fresh i earlier))
    rw [reason]
    rcases reasons i earlier with decision | ⟨oldLits, oldPacked, oldMember⟩
    · exact Or.inl decision
    · exact Or.inr ⟨oldLits, oldPacked.frame rfl rfl, oldMember⟩

/-- Both unmarked polarities imply a fresh variable. Distinct active variables
then provide the real finite array capacity needed by the executable write. -/
theorem InitializedRepresentation.assign {s : State} {id : Nat} {lits : Array Lit}
    (valid : InitializedRepresentation s) (packed : PackedClause s id lits)
    (member : s.db id ∈ lits) (head : s.mark (s.db id) = 0)
    (opposite : s.mark (Lit.negate (s.db id)) = 0) (root : Bool) :
    InitializedRepresentation (s.assign id root) := by
  have literal := packed.wellFormed _ member
  have fresh := freshVariable_of_unmarked_pair valid.active head opposite
  have room := assigned_lt_of_fresh valid.active valid.distinct fresh literal.1 literal.2
  have space : s.assigned < s.trail.size := by rw [valid.arrays.trailSize]; omega
  exact ⟨valid.arrays.assign, valid.bounds.assign room,
    valid.active.assign valid.arrays literal space fresh head,
    valid.distinct.assign fresh space, valid.phases.assign valid.arrays literal space fresh,
    valid.marked.assign space, valid.order.assign _ _,
    ReasonClauses.assign valid.reasons valid.arrays packed member space fresh⟩

/-- Every continuing execution of the exact initialization body preserves
the representation bundle, including the capacity-sensitive unit branch. -/
theorem initializationBody_representation {formula : Formula} (hWF : WellFormed formula)
    {idx : Nat} (hIdx : idx < formula.clauses.size) {s next : State}
    {stamps nextStamps : Array Nat}
    (hInv : InitializationLoopInvariant formula idx s stamps)
    (valid : InitializedRepresentation s)
    (hYield : initializationBody formula idx (none, s, stamps) =
      .ok (.yield (none, next, nextStamps))) : InitializedRepresentation next := by
  have hClause : formula.clauses[idx]! ∈ formula.clauses := by
    rw [getElem!_pos formula.clauses idx hIdx]
    exact Array.getElem_mem hIdx
  have hFresh : FreshStamp (idx + 1) stamps := by
    constructor
    · omega
    · intro i hI
      have bound := hInv.stampBound i hI
      omega
  obtain ⟨normalized, hNormalize, hSpec⟩ := normalizeClause_correct hInv.coverage hFresh
    (hWF _ hClause)
  have finish (current : State) (currentValid : InitializedRepresentation current)
      (execution : initializationBody formula idx (none, s, stamps) =
        .ok (.yield (none, current, normalized.stamps))) : InitializedRepresentation next := by
    have equal := ForInStep.yield.inj (Except.ok.inj (execution.symm.trans hYield))
    have states : current = next := congrArg (fun acc : InitializationAccumulator => acc.2.1) equal
    exact states ▸ currentValid
  by_cases tautology : normalized.tautology = true
  · apply finish s valid
    simp [initializationBody, hNormalize, tautology, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have notTautology : normalized.tautology = false := by
      cases equal : normalized.tautology <;> simp_all
    by_cases empty : normalized.lits.isEmpty = true
    · simp [initializationBody, hNormalize, notTautology, empty,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at hYield
    · let added := s.addClause normalized.lits true
      have hAdded : InitializedRepresentation added.1 := valid.addClause _ _
      by_cases unit : normalized.lits.size = 1
      · have hHeadRead : normalized.lits[0]! = normalized.lits[0] :=
          getElem!_pos normalized.lits 0 (by omega)
        have hPacked : PackedClause added.1 added.2 normalized.lits :=
          addClause_packed hInv.state.reserved (by
            intro lit hLit
            have bounds := hSpec.wellFormed lit hLit
            exact ⟨bounds.1, Nat.le_trans bounds.2 (by rw [hInv.state.variables]; omega)⟩)
        have hDb : added.1.db added.2 = normalized.lits[0]! := by
          simpa using hPacked.literals 0 (by omega)
        have hMember : added.1.db added.2 ∈ normalized.lits := by
          rw [hDb, getElem!_pos normalized.lits 0 (by omega)]
          exact Array.getElem_mem (by omega)
        by_cases conflict : added.1.mark normalized.lits[0]! ≠ 0
        · have conflictIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] ≠ 0 := by
            simpa only [added, hHeadRead] using conflict
          simp [initializationBody, hNormalize, notTautology, empty, unit, conflictIndex,
            Bind.bind, Except.bind, Pure.pure, Except.pure] at hYield
        · have unmarked : added.1.mark normalized.lits[0]! = 0 := by simpa using conflict
          have unmarkedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] = 0 := by
            simpa only [added, hHeadRead] using unmarked
          by_cases assigned : added.1.mark normalized.lits[0]!.negate = 0
          · have hAssigned : InitializedRepresentation (added.1.assign added.2 true) :=
              hAdded.assign hPacked hMember (by rw [hDb]; exact unmarked)
                (by rw [hDb]; exact assigned) true
            have assignedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0].negate = 0 := by
              simpa only [added, hHeadRead] using assigned
            apply finish _ hAssigned
            simp [initializationBody, hNormalize, notTautology, empty, unit, added,
              unmarkedIndex, assignedIndex, Bind.bind, Except.bind, Pure.pure, Except.pure]
          · have assignedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0].negate ≠ 0 := by
              simpa only [added, hHeadRead] using assigned
            apply finish _ hAdded
            simp [initializationBody, hNormalize, notTautology, empty, unit, added,
              unmarkedIndex, assignedIndex, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · apply finish _ hAdded
        simp [initializationBody, hNormalize, notTautology, empty, unit, added,
          Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- Prefix execution is the actual `forIn` iterator used by `initState`.
Only its continuing outcome needs a representation state. -/
theorem initialization_loop_representation {formula : Formula} (hWF : WellFormed formula)
    (fuel start : Nat) (hEnd : start + fuel ≤ formula.clauses.size)
    (s : State) (stamps : Array Nat) (hInv : InitializationLoopInvariant formula start s stamps)
    (valid : InitializedRepresentation s) {acc : InitializationAccumulator}
    (hRun : forIn (List.range' start fuel) (none, s, stamps) (initializationBody formula) = .ok acc)
    (continues : acc.1 = none) : InitializedRepresentation acc.2.1 := by
  induction fuel generalizing start s stamps acc with
  | zero =>
    have equal : (none, s, stamps) = acc := Except.ok.inj hRun
    exact congrArg (fun state : InitializationAccumulator => state.2.1) equal ▸ valid
  | succ fuel ih =>
    obtain ⟨stepResult, hStep, hChecked⟩ := initialization_step hWF (by omega) hInv
    cases hChecked with
    | unsat next nextStamps hUnsat =>
      rw [List.range'_succ, List.forIn_cons, hStep] at hRun
      have equal : (some none, next, nextStamps) = acc := Except.ok.inj hRun
      have flags := congrArg (fun state : InitializationAccumulator => state.1) equal
      simp [continues] at flags
    | ready next nextStamps hNext =>
      have nextValid := initializationBody_representation hWF (by omega) hInv valid hStep
      rw [List.range'_succ, List.forIn_cons, hStep] at hRun
      exact ih (start + 1) (by omega) next nextStamps hNext nextValid hRun continues

/-- Successful execution of the actual initializer establishes all fixed-array,
active-trail, mark, phase, reason-clause and move-to-front representation facts.
No assignment-space hypothesis is assumed: it follows from fresh variables. -/
theorem initState_some_representation {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s)) :
    InitializedRepresentation s := by
  let initial := emptyState formula.numVars config
  let stamps := Array.replicate (2 * (initial.nVars + 1)) 0
  have hInitial : InitializationLoopInvariant formula 0 initial stamps := by
    constructor
    · exact ⟨rfl, (emptyState_arenaBounds _ _).reserved, emptyState_rootMarks _ _ _⟩
    · dsimp [StampCoverage, stamps, initial, emptyState]
      simp
      omega
    · intro i hI
      rw [getElem!_pos stamps i hI]
      simp [stamps]
  obtain ⟨acc, hRun, hChecked⟩ := initialization_loop hWF formula.clauses.size 0 (by omega)
    initial stamps hInitial
  cases hChecked with
  | unsat next nextStamps hUnsat =>
    rw [initState_eq_loop, hRun] at hSome
    cases hSome
  | ready next nextStamps hNext =>
    have nextValid := initialization_loop_representation hWF formula.clauses.size 0 (by omega)
      initial stamps hInitial (emptyState_representation _ _) hRun rfl
    have initialized : initState formula config = .ok (some next) := by
      rw [initState_eq_loop, hRun]
      rfl
    have equal := Option.some.inj (Except.ok.inj (initialized.symm.trans hSome))
    exact equal ▸ nextValid

end MicrosatLean.Verification.Initialization
