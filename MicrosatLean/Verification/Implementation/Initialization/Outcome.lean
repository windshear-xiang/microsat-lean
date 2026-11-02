import MicrosatLean.Verification.Implementation.Initialization.Empty
import MicrosatLean.Verification.Implementation.Initialization.Normalize

namespace MicrosatLean.Verification.Implementation.Initialization

open CDCL Representation
open Std.Sat

/-- Every marked false literal follows unconditionally from the input CNF.
This property concerns initialization, where no decisions have been made. -/
def RootMarks (formula : Std.Sat.CNF Nat) (s : State) : Prop :=
  ∀ lit, s.mark lit ≠ 0 → ∀ a, CNF.Sat a formula → Falsifies a lit

theorem RootMarks.addClause {formula : Std.Sat.CNF Nat} {s : State}
    (h : RootMarks formula s) (lits : Array Lit) (original : Bool) :
    RootMarks formula (s.addClause lits original).1 := by
  simpa only [RootMarks, State.mark, addClause_marks] using h

theorem RootMarks.assign {formula : Std.Sat.CNF Nat} {s : State} {clauseId : Nat}
    (h : RootMarks formula s)
    (hHead : ∀ a, CNF.Sat a formula →
      a (literalView (s.db clauseId)).1 = (literalView (s.db clauseId)).2) :
    RootMarks formula (s.assign clauseId true) := by
  intro lit marked a model
  by_cases same : Lit.negate (s.db clauseId) = lit
  · subst lit
    exact (falsifies_negate_iff a _).mpr (hHead a model)
  · have old : s.mark lit ≠ 0 := by
      simpa only [assign_mark_other same] using marked
    exact h lit old a model

theorem emptyState_rootMarks (numVars : Nat) (config : Config) (formula : Std.Sat.CNF Nat) :
    RootMarks formula (emptyState numVars config) := by
  intro lit marked
  exact False.elim (marked (emptyState_mark numVars config lit))

theorem inputClause_entailed {formula : Formula} {clause : Array Lit}
    (hClause : clause ∈ formula.clauses) :
    CNF.EntailsClause (formulaView formula) (clauseView clause) := by
  intro a model
  exact CNF.sat_of_mem model (Array.mem_map_of_mem hClause)

theorem normalized_entailed {formula : Formula} {stamp : Nat} {old : Array Nat}
    {clause : Array Lit} {result : NormalizedClause}
    (hClause : clause ∈ formula.clauses)
    (hSpec : NormalizationSpec formula.numVars stamp old clause result) :
    CNF.EntailsClause (formulaView formula) (clauseView result.lits) := by
  intro a model
  exact (hSpec.preserves_sat a).mpr (inputClause_entailed hClause a model)

theorem unsat_of_normalized_empty {formula : Formula} {stamp : Nat} {old : Array Nat}
    {clause : Array Lit} {result : NormalizedClause}
    (hClause : clause ∈ formula.clauses)
    (hSpec : NormalizationSpec formula.numVars stamp old clause result)
    (hEmpty : result.lits.isEmpty = true) : CNF.Unsat (formulaView formula) := by
  apply CNF.unsat_iff_not_sat.mpr
  intro a model
  obtain ⟨lit, member, _⟩ := (clauseView_sat_iff _ _).mp
    (normalized_entailed hClause hSpec a model)
  have size : result.lits.size = 0 := by simpa using hEmpty
  have empty : result.lits = #[] := Array.size_eq_zero_iff.mp size
  simp [empty] at member

theorem normalized_unit_head {formula : Formula} {stamp : Nat} {old : Array Nat}
    {clause : Array Lit} {result : NormalizedClause}
    (hClause : clause ∈ formula.clauses)
    (hSpec : NormalizationSpec formula.numVars stamp old clause result)
    (hUnit : result.lits.size = 1) :
    ∀ a, CNF.Sat a (formulaView formula) →
      a (literalView result.lits[0]!).1 = (literalView result.lits[0]!).2 := by
  intro a model
  obtain ⟨lit, member, trueLit⟩ := (clauseView_sat_iff _ _).mp
    (normalized_entailed hClause hSpec a model)
  obtain ⟨i, hI, value⟩ := Array.mem_iff_getElem.mp member
  have zero : i = 0 := by omega
  subst i
  have equal : result.lits[0]! = lit := by
    rw [getElem!_pos result.lits 0 hI]
    exact value
  simpa only [literalView, equal] using trueLit

structure InitializationStateInvariant (formula : Formula) (s : State) : Prop where
  variables : s.nVars = max 1 formula.numVars
  reserved : 2 ≤ s.arena.size
  roots : RootMarks (formulaView formula) s

structure InitializationLoopInvariant (formula : Formula) (index : Nat)
    (s : State) (stamps : Array Nat) : Prop where
  state : InitializationStateInvariant formula s
  coverage : StampCoverage formula.numVars stamps
  stampBound : ∀ i, i < stamps.size → stamps[i]! ≤ index

abbrev InitializationAccumulator := Option (Option State) × State × Array Nat

/-- The exact literal-clause body of `initState`'s range loop, with its early
return accumulator exposed for invariant proofs. It is not a solver entry point. -/
def initializationBody (formula : Formula) (idx : Nat) (acc : InitializationAccumulator) :
    Except String (ForInStep InitializationAccumulator) := do
  let mut s := acc.2.1
  let normalized ← normalizeClause formula.numVars (idx + 1) acc.2.2 formula.clauses[idx]!
  let stamps := normalized.stamps
  let lits := normalized.lits
  if !normalized.tautology then
    if lits.isEmpty then return .done (some none, s, stamps)
    let (nextState, clauseId) := s.addClause lits true
    s := nextState
    if lits.size == 1 then
      let lit := lits[0]!
      if s.mark lit != 0 then return .done (some none, s, stamps)
      if s.mark lit.negate == 0 then s := s.assign clauseId true
  return .yield (none, s, stamps)

inductive InitializationStepChecked (formula : Formula) (index : Nat) :
    ForInStep InitializationAccumulator → Prop where
  | unsat (s : State) (stamps : Array Nat) (h : CNF.Unsat (formulaView formula)) :
      InitializationStepChecked formula index (.done (some none, s, stamps))
  | ready (s : State) (stamps : Array Nat) (h : InitializationLoopInvariant formula index s stamps) :
      InitializationStepChecked formula index (.yield (none, s, stamps))

inductive InitializationLoopChecked (formula : Formula) (index : Nat) : InitializationAccumulator → Prop where
  | unsat (s : State) (stamps : Array Nat) (h : CNF.Unsat (formulaView formula)) :
      InitializationLoopChecked formula index (some none, s, stamps)
  | ready (s : State) (stamps : Array Nat) (h : InitializationLoopInvariant formula index s stamps) :
      InitializationLoopChecked formula index (none, s, stamps)

theorem initialization_step {formula : Formula} (hWF : WellFormed formula)
    {idx : Nat} (hIdx : idx < formula.clauses.size) {s : State} {stamps : Array Nat}
    (hInv : InitializationLoopInvariant formula idx s stamps) :
    ∃ result, initializationBody formula idx (none, s, stamps) = .ok result ∧
      InitializationStepChecked formula (idx + 1) result := by
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
  have hCoverage : StampCoverage formula.numVars normalized.stamps := by
    simpa only [StampCoverage, hSpec.stampsSize] using hInv.coverage
  have hStampBound : ∀ i, i < normalized.stamps.size → normalized.stamps[i]! ≤ idx + 1 :=
    hSpec.stamps_le (fun i hI => Nat.le_trans (hInv.stampBound i hI) (by omega))
  have hKeep (next : State) (hState : InitializationStateInvariant formula next) :
      InitializationLoopInvariant formula (idx + 1) next normalized.stamps :=
    ⟨hState, hCoverage, hStampBound⟩
  by_cases tautology : normalized.tautology = true
  · refine ⟨.yield (none, s, normalized.stamps), ?_, .ready _ _ (hKeep s hInv.state)⟩
    simp [initializationBody, hNormalize, tautology, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have notTautology : normalized.tautology = false := by
      cases equal : normalized.tautology <;> simp_all
    by_cases empty : normalized.lits.isEmpty = true
    · refine ⟨.done (some none, s, normalized.stamps), ?_,
        .unsat _ _ (unsat_of_normalized_empty hClause hSpec empty)⟩
      simp [initializationBody, hNormalize, notTautology, empty,
        Bind.bind, Except.bind, Pure.pure, Except.pure]
    · let added := s.addClause normalized.lits true
      have hAdded : InitializationStateInvariant formula added.1 := by
        constructor
        · simpa [added] using hInv.state.variables
        · have size := addClause_arena_size (s := s) (lits := normalized.lits) (original := true)
          have reserved := hInv.state.reserved
          dsimp [added]
          omega
        · exact hInv.state.roots.addClause _ _
      by_cases unit : normalized.lits.size = 1
      · have hHead := normalized_unit_head hClause hSpec unit
        have hHeadRead : normalized.lits[0]! = normalized.lits[0] :=
          getElem!_pos normalized.lits 0 (by omega)
        have hPacked : PackedClause added.1 added.2 normalized.lits :=
          addClause_packed hInv.state.reserved (by
            intro lit hLit
            have bounds := hSpec.wellFormed lit hLit
            exact ⟨bounds.1, Nat.le_trans bounds.2 (by rw [hInv.state.variables]; omega)⟩)
        have hDb : added.1.db added.2 = normalized.lits[0]! := by
          simpa using hPacked.literals 0 (by omega)
        by_cases conflict : added.1.mark normalized.lits[0]! ≠ 0
        · have hUnsat : CNF.Unsat (formulaView formula) := by
            apply CNF.unsat_iff_not_sat.mpr
            intro a model
            exact hAdded.roots _ conflict a model (hHead a model)
          have conflictIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] ≠ 0 := by
            simpa only [added, hHeadRead] using conflict
          refine ⟨.done (some none, added.1, normalized.stamps), ?_, .unsat _ _ hUnsat⟩
          simp [initializationBody, hNormalize, notTautology, empty, unit, added, conflictIndex,
            Bind.bind, Except.bind, Pure.pure, Except.pure]
        · have unmarkedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] = 0 := by
            have unmarked : added.1.mark normalized.lits[0]! = 0 := by simpa using conflict
            simpa only [added, hHeadRead] using unmarked
          by_cases assigned : added.1.mark normalized.lits[0]!.negate = 0
          · have hAssigned : InitializationStateInvariant formula (added.1.assign added.2 true) := by
              constructor
              · simpa [State.assign] using hAdded.variables
              · exact hAdded.reserved
              · exact hAdded.roots.assign (by simpa only [hDb] using hHead)
            have assignedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0].negate = 0 := by
              simpa only [added, hHeadRead] using assigned
            refine ⟨.yield (none, added.1.assign added.2 true, normalized.stamps), ?_,
              .ready _ _ (hKeep _ hAssigned)⟩
            simp [initializationBody, hNormalize, notTautology, empty, unit, added,
              unmarkedIndex, assignedIndex,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
          · have assignedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0].negate ≠ 0 := by
              simpa only [added, hHeadRead] using assigned
            refine ⟨.yield (none, added.1, normalized.stamps), ?_, .ready _ _ (hKeep _ hAdded)⟩
            simp [initializationBody, hNormalize, notTautology, empty, unit, added,
              unmarkedIndex, assignedIndex,
              Bind.bind, Except.bind, Pure.pure, Except.pure]
      · refine ⟨.yield (none, added.1, normalized.stamps), ?_, .ready _ _ (hKeep _ hAdded)⟩
        simp [initializationBody, hNormalize, notTautology, empty, unit, added,
          Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem initialization_loop {formula : Formula} (hWF : WellFormed formula)
    (fuel start : Nat) (hEnd : start + fuel ≤ formula.clauses.size)
    (s : State) (stamps : Array Nat) (hInv : InitializationLoopInvariant formula start s stamps) :
    ∃ result, forIn (List.range' start fuel) (none, s, stamps) (initializationBody formula) = .ok result ∧
      InitializationLoopChecked formula (start + fuel) result := by
  induction fuel generalizing start s stamps with
  | zero => exact ⟨_, rfl, .ready _ _ (by simpa using hInv)⟩
  | succ fuel ih =>
    obtain ⟨stepResult, hStep, hChecked⟩ := initialization_step hWF (by omega) hInv
    cases hChecked with
    | unsat next nextStamps hUnsat =>
      exact ⟨_, by rw [List.range'_succ, List.forIn_cons, hStep]; rfl,
        .unsat _ _ hUnsat⟩
    | ready next nextStamps hNext =>
      obtain ⟨result, hRun, hResult⟩ := ih (start + 1) (by omega) next nextStamps hNext
      refine ⟨result, ?_, ?_⟩
      · rw [List.range'_succ, List.forIn_cons, hStep]
        exact hRun
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hResult

def finishInitialization (acc : InitializationAccumulator) : Option State :=
  match acc.1 with
  | some result => result
  | none => some acc.2.1

theorem initState_eq_loop (formula : Formula) (config : Config) :
    initState formula config = (do
      let result ← forIn (List.range' 0 formula.clauses.size)
        (none, emptyState formula.numVars config,
          Array.replicate (2 * ((emptyState formula.numVars config).nVars + 1)) 0)
        (initializationBody formula)
      pure (finishInitialization result)) := by
  simp only [initState, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  congr 1
  funext acc
  cases acc with
  | mk result rest => cases result <;> rfl

/-- The actual initialization function never errors on well-formed input.
Early UNSAT is justified by an empty clause or conflicting entailed units;
successful states contain only input-entailed root marks. -/
theorem initState_structured_outcome {formula : Formula} (hWF : WellFormed formula) (config : Config := {}) :
    ∃ result, initState formula config = .ok result ∧
      match result with
      | none => CNF.Unsat (formulaView formula)
      | some s => InitializationStateInvariant formula s := by
  let s := emptyState formula.numVars config
  let stamps := Array.replicate (2 * (s.nVars + 1)) 0
  have hInitial : InitializationLoopInvariant formula 0 s stamps := by
    constructor
    · exact ⟨rfl, (emptyState_arenaBounds _ _).reserved, emptyState_rootMarks _ _ _⟩
    · dsimp [StampCoverage, stamps, s, emptyState]
      simp
      omega
    · intro i hI
      rw [getElem!_pos stamps i hI]
      simp [stamps]
  obtain ⟨acc, hRun, hChecked⟩ := initialization_loop hWF formula.clauses.size 0 (by omega)
    s stamps hInitial
  cases hChecked with
  | unsat next nextStamps hUnsat =>
    refine ⟨none, ?_, hUnsat⟩
    rw [initState_eq_loop]
    rw [hRun]
    rfl
  | ready next nextStamps hNext =>
    refine ⟨some next, ?_, hNext.state⟩
    rw [initState_eq_loop]
    rw [hRun]
    rfl

theorem initState_outcome {formula : Formula} (hWF : WellFormed formula) (config : Config := {}) :
    ∃ result, initState formula config = .ok result ∧
      match result with
      | none => CNF.Unsat (formulaView formula)
      | some s => RootMarks (formulaView formula) s := by
  obtain ⟨result, initialized, checked⟩ := initState_structured_outcome hWF config
  refine ⟨result, initialized, ?_⟩
  cases result with
  | none => exact checked
  | some s => exact checked.roots

theorem initState_some_variables {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (success : initState formula config = .ok (some s)) :
    s.nVars = max 1 formula.numVars := by
  obtain ⟨result, initialized, checked⟩ := initState_structured_outcome wellFormed config
  have equal : result = some s := Except.ok.inj (initialized.symm.trans success)
  subst result
  exact checked.variables

theorem initState_some_rootMarks {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s)) :
    RootMarks (formulaView formula) s := by
  obtain ⟨result, hRun, hResult⟩ := initState_outcome hWF config
  have equal : result = some s := Except.ok.inj (hRun.symm.trans hSome)
  simpa only [equal] using hResult

end MicrosatLean.Verification.Implementation.Initialization
