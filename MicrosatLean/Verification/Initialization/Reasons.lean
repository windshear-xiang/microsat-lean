import MicrosatLean.Verification.Initialization.Representation
import MicrosatLean.Verification.Analysis.ImpliedSound
import MicrosatLean.Verification.Analysis.Resolution

namespace MicrosatLean.Verification.Initialization

open CDCL Representation Propagation Analysis Std.Sat

/-- Initial assignments are all input-entailed units. Their reasons have an
exact head and no tail, rather than merely containing the true literal. -/
def InitialUnitReasons (formula : CNF Nat) (s : State) : Prop :=
  ∀ i, i < s.assigned → ∃ lits,
    PackedClause s (s.reason s.trail[i]!) lits ∧ lits.size = 1 ∧
      lits[0]! = s.trail[i]!.negate ∧ CNF.EntailsClause formula (clauseView lits)

/-- Initialization uses only the unassigned and unconditional-root tags. -/
def InitialTags (s : State) : Prop := ∀ lit, s.mark lit = 0 ∨ s.mark lit = 6

structure InitialAnalysisData (formula : CNF Nat) (s : State) : Prop where
  units : InitialUnitReasons formula s
  tags : InitialTags s

theorem emptyState_analysisData (numVars : Nat) (config : Config) (formula : CNF Nat) :
    InitialAnalysisData formula (emptyState numVars config) := by
  constructor
  · intro i before
    simp [emptyState] at before
  · intro lit
    exact Or.inl (emptyState_mark _ _ _)

theorem InitialAnalysisData.addClause {formula : CNF Nat} {s : State}
    (data : InitialAnalysisData formula s) (lits : Array Lit) (original : Bool) :
    InitialAnalysisData formula (s.addClause lits original).1 := by
  constructor
  · intro i before
    obtain ⟨reason, packed, unit, head, entailed⟩ := data.units i (by simpa using before)
    refine ⟨reason, ?_, unit, ?_, entailed⟩
    · simpa only [State.reason, addClause_reasons, addClause_trail] using packed.addClause lits
    · simpa only [addClause_trail] using head
  · simpa only [InitialTags, State.mark, addClause_marks] using data.tags

theorem InitialAnalysisData.assign {formula : CNF Nat} {s : State} {id : Nat}
    {lits : Array Lit} (data : InitialAnalysisData formula s) (valid : InitializedRepresentation s)
    (packed : PackedClause s id lits) (unit : lits.size = 1)
    (entailed : CNF.EntailsClause formula (clauseView lits))
    (unmarked : s.mark (s.db id) = 0) (opposite : s.mark (Lit.negate (s.db id)) = 0) :
    InitialAnalysisData formula (s.assign id true) := by
  have head : s.db id = lits[0]! := by simpa using packed.literals 0 (by omega)
  have member : s.db id ∈ lits := by
    rw [head, getElem!_pos lits 0 (by omega)]
    exact Array.getElem_mem (by omega)
  have literal := packed.wellFormed _ member
  have fresh := freshVariable_of_unmarked_pair valid.active unmarked opposite
  have room := assigned_lt_of_fresh valid.active valid.distinct fresh literal.1 literal.2
  have space : s.assigned < s.trail.size := by rw [valid.arrays.trailSize]; omega
  constructor
  · intro i before
    have bound : i < s.assigned + 1 := before
    by_cases last : i = s.assigned
    · subst i
      rw [assign_trail_last space]
      have reason : (s.assign id true).reason (Lit.negate (s.db id)) = id := by
        simpa only [State.reason, negate_var] using
          (assign_reason (root := true) (valid.arrays.variable_index literal.2).1)
      rw [reason]
      exact ⟨lits, packed.frame rfl rfl, unit, by simpa only [negate_negate] using head.symm,
        entailed⟩
    · have earlier : i < s.assigned := by omega
      rw [assign_trail_prefix earlier]
      have reason : (s.assign id true).reason s.trail[i]! = s.reason s.trail[i]! :=
        Array.getElem!_set!_ne s.reasons _ _ _ (Ne.symm (fresh i earlier))
      rw [reason]
      obtain ⟨oldLits, oldPacked, oldUnit, oldHead, oldEntailed⟩ := data.units i earlier
      exact ⟨oldLits, oldPacked.frame rfl rfl, oldUnit, oldHead, oldEntailed⟩
  · intro lit
    by_cases same : Lit.negate (s.db id) = lit
    · subst lit
      right
      exact Array.getElem!_set!_self s.marks _ _
        (valid.arrays.literal_index literal.negate).1
    · simpa only [assign_mark_other same] using data.tags lit

/-- Continuing execution of the actual clause loop retains precise singleton
reasons; normalized units supply entailment from the complete input CNF. -/
theorem initializationBody_analysisData {formula : Formula} (hWF : WellFormed formula)
    {idx : Nat} (hIdx : idx < formula.clauses.size) {s next : State}
    {stamps nextStamps : Array Nat} (hInv : InitializationLoopInvariant formula idx s stamps)
    (valid : InitializedRepresentation s) (data : InitialAnalysisData (formulaView formula) s)
    (hYield : initializationBody formula idx (none, s, stamps) =
      .ok (.yield (none, next, nextStamps))) : InitialAnalysisData (formulaView formula) next := by
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
  have finish (current : State) (currentData : InitialAnalysisData (formulaView formula) current)
      (execution : initializationBody formula idx (none, s, stamps) =
        .ok (.yield (none, current, normalized.stamps))) :
      InitialAnalysisData (formulaView formula) next := by
    have equal := ForInStep.yield.inj (Except.ok.inj (execution.symm.trans hYield))
    have states : current = next := congrArg (fun acc : InitializationAccumulator => acc.2.1) equal
    exact states ▸ currentData
  by_cases tautology : normalized.tautology = true
  · apply finish s data
    simp [initializationBody, hNormalize, tautology, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have notTautology : normalized.tautology = false := by
      cases equal : normalized.tautology <;> simp_all
    by_cases empty : normalized.lits.isEmpty = true
    · simp [initializationBody, hNormalize, notTautology, empty,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at hYield
    · let added := s.addClause normalized.lits true
      have hAdded : InitialAnalysisData (formulaView formula) added.1 := data.addClause _ _
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
        by_cases conflict : added.1.mark normalized.lits[0]! ≠ 0
        · have conflictIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] ≠ 0 := by
            simpa only [added, hHeadRead] using conflict
          simp [initializationBody, hNormalize, notTautology, empty, unit, conflictIndex,
            Bind.bind, Except.bind, Pure.pure, Except.pure] at hYield
        · have unmarked : added.1.mark normalized.lits[0]! = 0 := by simpa using conflict
          have unmarkedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] = 0 := by
            simpa only [added, hHeadRead] using unmarked
          by_cases assigned : added.1.mark normalized.lits[0]!.negate = 0
          · have hAssigned : InitialAnalysisData (formulaView formula) (added.1.assign added.2 true) :=
              hAdded.assign (valid.addClause _ _) hPacked unit (normalized_entailed hClause hSpec)
                (by rw [hDb]; exact unmarked) (by rw [hDb]; exact assigned)
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

theorem initialization_loop_analysisData {formula : Formula} (hWF : WellFormed formula)
    (fuel start : Nat) (hEnd : start + fuel ≤ formula.clauses.size)
    (s : State) (stamps : Array Nat) (hInv : InitializationLoopInvariant formula start s stamps)
    (valid : InitializedRepresentation s) (data : InitialAnalysisData (formulaView formula) s)
    {acc : InitializationAccumulator}
    (hRun : forIn (List.range' start fuel) (none, s, stamps) (initializationBody formula) = .ok acc)
    (continues : acc.1 = none) : InitialAnalysisData (formulaView formula) acc.2.1 := by
  induction fuel generalizing start s stamps acc with
  | zero =>
    have equal : (none, s, stamps) = acc := Except.ok.inj hRun
    exact congrArg (fun state : InitializationAccumulator => state.2.1) equal ▸ data
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
      have nextData := initializationBody_analysisData hWF (by omega) hInv valid data hStep
      rw [List.range'_succ, List.forIn_cons, hStep] at hRun
      exact ih (start + 1) (by omega) next nextStamps hNext nextValid nextData hRun continues

theorem initState_some_analysisData {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s)) :
    InitialAnalysisData (formulaView formula) s := by
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
    have nextData := initialization_loop_analysisData hWF formula.clauses.size 0 (by omega)
      initial stamps hInitial (emptyState_representation _ _) (emptyState_analysisData _ _ _)
      hRun rfl
    have initialized : initState formula config = .ok (some next) := by
      rw [initState_eq_loop, hRun]
      rfl
    have equal := Option.some.inj (Except.ok.inj (initialized.symm.trans hSome))
    exact equal ▸ nextData

/-- A proof-only rank is the unique active trail position of a literal.
Its arbitrary value away from that snapshot has no semantic role. -/
noncomputable def initialTrailRank (s : State) (lit : Lit) : Nat := by
  classical
  exact if member : ∃ i, i < s.assigned ∧ s.trail[i]! = lit then Classical.choose member else 0

theorem initialTrailRank_eq {s : State} (distinct : DistinctTrailVariables s)
    (i : Nat) (before : i < s.assigned) : initialTrailRank s s.trail[i]! = i := by
  classical
  have member : ∃ j, j < s.assigned ∧ s.trail[j]! = s.trail[i]! := ⟨i, before, rfl⟩
  rw [initialTrailRank, dite_eq_left member]
  have chosen := Classical.choose_spec member
  exact distinct _ i chosen.1 before (congrArg Lit.var chosen.2)

theorem initState_some_reasonGraph {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s)) :
    ReasonGraph (formulaView formula) s s.assigned (initialTrailRank s) := by
  have valid := initState_some_representation hWF hSome
  have data := initState_some_analysisData hWF hSome
  constructor
  · rw [valid.arrays.trailSize]
    have := valid.bounds.assignedVars
    omega
  · exact initialTrailRank_eq valid.distinct
  · exact valid.distinct
  · intro i before _
    obtain ⟨lits, packed, unit, head, entailed⟩ := data.units i before
    refine ⟨lits, packed, by omega, head, entailed, ?_⟩
    intro j positive bound
    omega

theorem initState_some_rootTagConsequences {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s)) :
    RootTagConsequences (formulaView formula) s s.assigned s := by
  intro lit _ tag
  exact initState_some_rootMarks hWF hSome lit (by omega)

/-- Initial tag-six entries are unconditional input consequences, so the
analysis cache is valid even with no original MARK leaves. -/
theorem initState_some_impliedCache {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s))
    (rank : Lit → Nat) (leaves : Lit → Prop) :
    ImpliedCache (formulaView formula) s s.assigned rank leaves s := by
  have data := initState_some_analysisData hWF hSome
  have roots := initState_some_rootMarks hWF hSome
  constructor
  · intro lit _
    rcases data.tags lit with tag | tag
    · exact Or.inl tag
    · exact Or.inr (Or.inr (Or.inr (Or.inr tag)))
  · intro lit _ tag
    rcases data.tags lit with zero | root <;> omega
  · intro lit _ tag a model _
    exact roots lit (by omega) a model

/-- A closed semantic entry point: the graph, the empty-leaf cache, and root
tags all follow from actual successful initialization of well-formed input. -/
theorem initState_some_analysisEntry {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s)) :
    ReasonGraph (formulaView formula) s s.assigned (initialTrailRank s) ∧
      ImpliedCache (formulaView formula) s s.assigned (initialTrailRank s) (fun _ => False) s ∧
      RootTagConsequences (formulaView formula) s s.assigned s :=
  ⟨initState_some_reasonGraph hWF hSome, initState_some_impliedCache hWF hSome _ _,
    initState_some_rootTagConsequences hWF hSome⟩

/-- The existing actual `implied` soundness theorem can now be instantiated
at initialization without assuming its graph or cache hypotheses. -/
theorem initState_some_implied_sound {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s))
    (fuel : Nat) {lit : Lit} (member : TrailMember s s.assigned lit)
    (successful : (implied fuel s lit).2 = true) :
    ∀ a, CNF.Sat a (formulaView formula) → Falsifies a lit := by
  have entry := initState_some_analysisEntry hWF hSome
  have sound := implied_sound entry.1 fuel s lit (.refl s) entry.2.1 member
  intro a model
  exact sound.2 successful a model (by intro leaf impossible; cases impossible)

end MicrosatLean.Verification.Initialization
