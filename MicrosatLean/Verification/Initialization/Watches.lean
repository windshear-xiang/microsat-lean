import MicrosatLean.Verification.Initialization.Representation
import MicrosatLean.Verification.Initialization.Database
import MicrosatLean.Verification.Representation.ClauseWatches
import MicrosatLean.Verification.Representation.ReasonDatabase

namespace MicrosatLean.Verification.Initialization

open CDCL Representation Std.Sat

/-- Every actual list is linked, every long stored clause owns its two
watches, and every reference belongs to a genuine long database entry. -/
structure InitialWatchState (s : State) (original : List StoredClause)
    (heads : Nat → List Nat) : Prop where
  lists : ∀ lit, WatchList s lit (heads lit)
  covered : ∀ entry ∈ original, 1 < entry.lits.size →
    ClauseWatches heads entry.id entry.lits[0]! entry.lits[1]!
  references : ∀ lit ref, ref ∈ heads lit →
    ∃ entry ∈ original, 1 < entry.lits.size ∧ (ref = 2 * entry.id ∨ ref = 2 * entry.id + 1)
  nonempty : ∀ entry ∈ original, 0 < entry.lits.size
  unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other
  nodup : ∀ entry ∈ original, entry.lits.toList.Nodup

def InitialWatchDatabase (formula : Formula) (index : Nat) (s : State) : Prop :=
  ∃ original heads, Database s original [] ∧
    CNF.BiEntails (inputPrefix formula index) (databaseView original) ∧
      InitialWatchState s original heads ∧ ReasonDatabase s original

theorem emptyState_watchDatabase (formula : Formula) (config : Config) :
    InitialWatchDatabase formula 0 (emptyState formula.numVars config) := by
  refine ⟨[], fun _ => [], emptyState_database _ _, ?_, ?_, ?_⟩
  · simpa only [inputPrefix_zero, databaseView_nil] using CNF.biEntails_refl
  · constructor
    · exact emptyState_watchList _ _
    · intro entry impossible
      simp at impossible
    · intro lit ref impossible
      simp at impossible
    · intro entry impossible
      simp at impossible
    · intro lit other ref impossible
      simp at impossible
    · intro entry impossible
      simp at impossible
  · intro i before
    simp only [emptyState] at before
    omega

theorem initial_watchList_assign {s : State} {lit : Lit} {refs : List Nat}
    (list : WatchList s lit refs) (id : Nat) (root : Bool) :
    WatchList (s.assign id root) lit refs := by
  exact list

theorem InitialWatchState.assign {s : State} {original : List StoredClause}
    {heads : Nat → List Nat} (watched : InitialWatchState s original heads) (id : Nat) (root : Bool) :
    InitialWatchState (s.assign id root) original heads :=
  ⟨fun lit => initial_watchList_assign (watched.lists lit) id root,
    watched.covered, watched.references, watched.nonempty, watched.unique, watched.nodup⟩

theorem normalized_first_two_ne {lits : Array Lit} (noDuplicates : lits.toList.Nodup)
    (wide : 1 < lits.size) : lits[0]! ≠ lits[1]! := by
  intro same
  have first : 0 < lits.toList.length := by simp only [Array.length_toList]; omega
  have second : 1 < lits.toList.length := by simpa only [Array.length_toList] using wide
  have listSame : lits.toList[0] = lits.toList[1] := by
    simpa only [Array.getElem_toList, getElem!_pos lits 0 (by omega),
      getElem!_pos lits 1 wide] using same
  have equal := noDuplicates.eq_of_getElem_eq first second listSame
  omega

private theorem clauseWatchHeads_source {heads : Nat → List Nat} {id first second lit ref : Nat}
    (member : ref ∈ clauseWatchHeads heads id first second lit) :
    ref ∈ heads lit ∨ ref = 2 * id ∨ ref = 2 * id + 1 := by
  unfold clauseWatchHeads at member
  split at member
  · rcases List.mem_cons.mp member with same | old
    · exact Or.inr (Or.inl same)
    · exact Or.inl old
  · split at member
    · rcases List.mem_cons.mp member with same | old
      · exact Or.inr (Or.inr same)
      · exact Or.inl old
    · exact Or.inl member

private theorem clauseWatchHeads_source_head {heads : Nat → List Nat} {id first second lit ref : Nat}
    (member : ref ∈ clauseWatchHeads heads id first second lit) :
    ref ∈ heads lit ∨ (ref = 2 * id ∧ lit = first) ∨ (ref = 2 * id + 1 ∧ lit = second) := by
  unfold clauseWatchHeads at member
  split at member
  · rcases List.mem_cons.mp member with same | old
    · exact Or.inr (Or.inl ⟨same, by assumption⟩)
    · exact Or.inl old
  · split at member
    · rcases List.mem_cons.mp member with same | old
      · exact Or.inr (Or.inr ⟨same, by assumption⟩)
      · exact Or.inl old
    · exact Or.inl member

private theorem clauseWatchHeads_unique {s : State} {heads : Nat → List Nat}
    (lists : ∀ lit, WatchList s lit (heads lit))
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    (first second : Lit) :
    ∀ lit other ref,
      ref ∈ clauseWatchHeads heads (s.arena.size + 2) first second lit →
      ref ∈ clauseWatchHeads heads (s.arena.size + 2) first second other → lit = other := by
  intro lit other ref left right
  rcases clauseWatchHeads_source_head left with oldLeft | firstLeft | secondLeft
  · rcases clauseWatchHeads_source_head right with oldRight | firstRight | secondRight
    · exact unique lit other ref oldLeft oldRight
    · exact False.elim ((lists lit).newRef_not_mem 0 (by decide) (firstRight.1 ▸ oldLeft))
    · exact False.elim ((lists lit).newRef_not_mem 1 (by decide) (secondRight.1 ▸ oldLeft))
  · rcases clauseWatchHeads_source_head right with oldRight | firstRight | secondRight
    · exact False.elim ((lists other).newRef_not_mem 0 (by decide) (firstLeft.1 ▸ oldRight))
    · exact firstLeft.2.trans firstRight.2.symm
    · omega
  · rcases clauseWatchHeads_source_head right with oldRight | firstRight | secondRight
    · exact False.elim ((lists other).newRef_not_mem 1 (by decide) (secondLeft.1 ▸ oldRight))
    · omega
    · exact secondLeft.2.trans secondRight.2.symm

/-- The ghost heads follow exactly the allocator's width test. Their reference
sources and clause coverage are extended with the same stored database entry. -/
theorem InitialWatchState.addClause {s : State} {original : List StoredClause}
    {heads : Nat → List Nat} {lits : Array Lit} (watched : InitialWatchState s original heads)
    (arrays : ArrayBounds s) (reserved : 2 ≤ s.arena.size)
    (wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit)
    (nonempty : 0 < lits.size) (noDuplicates : lits.toList.Nodup) :
    InitialWatchState (s.addClause lits true).1
      (original ++ [⟨(s.addClause lits true).2, lits⟩])
      (fun lit => if 1 < lits.size then
        clauseWatchHeads heads (s.arena.size + 2) lits[0]! lits[1]! lit else heads lit) := by
  have distinct := normalized_first_two_ne noDuplicates
  constructor
  · exact addClause_watchLists_all heads watched.lists arrays reserved wellFormed distinct
  · intro entry member wideEntry
    rcases List.mem_append.mp member with old | new
    · have covered := watched.covered entry old wideEntry
      by_cases wide : 1 < lits.size
      · simpa only [ite_eq_left wide] using covered.clauseWatchHeads
          (s.arena.size + 2) lits[0]! lits[1]!
      · simpa only [ite_eq_right wide] using covered
    · have same : entry = ⟨(s.addClause lits true).2, lits⟩ := List.mem_singleton.mp new
      subst entry
      simpa only [ite_eq_left wideEntry, addClause_id] using
        (addClause_watchLists (original := true) heads watched.lists arrays reserved wellFormed wideEntry
          (distinct wideEntry)).2
  · intro lit ref member
    by_cases wide : 1 < lits.size
    · rw [ite_eq_left wide] at member
      rcases clauseWatchHeads_source member with old | first | second
      · obtain ⟨entry, stored, long, source⟩ := watched.references lit ref old
        exact ⟨entry, List.mem_append_left _ stored, long, source⟩
      · exact ⟨⟨(s.addClause lits true).2, lits⟩, by simp, wide,
          Or.inl (by simpa only [addClause_id] using first)⟩
      · exact ⟨⟨(s.addClause lits true).2, lits⟩, by simp, wide,
          Or.inr (by simpa only [addClause_id] using second)⟩
    · rw [ite_eq_right wide] at member
      obtain ⟨entry, stored, long, source⟩ := watched.references lit ref member
      exact ⟨entry, List.mem_append_left _ stored, long, source⟩
  · intro entry member
    rcases List.mem_append.mp member with old | new
    · exact watched.nonempty entry old
    · have same : entry = ⟨(s.addClause lits true).2, lits⟩ := List.mem_singleton.mp new
      simpa only [same] using nonempty
  · by_cases wide : 1 < lits.size
    · simpa only [ite_eq_left wide] using
        clauseWatchHeads_unique watched.lists watched.unique lits[0]! lits[1]!
    · simpa only [ite_eq_right wide] using watched.unique
  · intro entry member
    rcases List.mem_append.mp member with old | new
    · exact watched.nodup entry old
    · have same : entry = ⟨(s.addClause lits true).2, lits⟩ := List.mem_singleton.mp new
      simpa only [same] using noDuplicates

/-- This clause loop carries the database entries and represented watch heads
together, so later theorems do not conflate separate existential witnesses. -/
theorem initializationBody_watchDatabase {formula : Formula} (hWF : WellFormed formula)
    {idx : Nat} (hIdx : idx < formula.clauses.size) {s next : State}
    {stamps nextStamps : Array Nat} (hInv : InitializationLoopInvariant formula idx s stamps)
    (valid : InitializedRepresentation s) (database : InitialWatchDatabase formula idx s)
    (hYield : initializationBody formula idx (none, s, stamps) =
      .ok (.yield (none, next, nextStamps))) : InitialWatchDatabase formula (idx + 1) next := by
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
  obtain ⟨original, heads, stored, meaning, watched, proper⟩ := database
  have finish (current : State) (currentDatabase : InitialWatchDatabase formula (idx + 1) current)
      (execution : initializationBody formula idx (none, s, stamps) =
        .ok (.yield (none, current, normalized.stamps))) :
      InitialWatchDatabase formula (idx + 1) next := by
    have equal := ForInStep.yield.inj (Except.ok.inj (execution.symm.trans hYield))
    have states : current = next := congrArg (fun acc : InitializationAccumulator => acc.2.1) equal
    exact states ▸ currentDatabase
  by_cases tautology : normalized.tautology = true
  · apply finish s ⟨original, heads, stored, prefix_skip hIdx meaning hSpec tautology, watched, proper⟩
    simp [initializationBody, hNormalize, tautology, Bind.bind, Except.bind, Pure.pure, Except.pure]
  · have notTautology : normalized.tautology = false := by
      cases equal : normalized.tautology <;> simp_all
    by_cases empty : normalized.lits.isEmpty = true
    · simp [initializationBody, hNormalize, notTautology, empty,
        Bind.bind, Except.bind, Pure.pure, Except.pure] at hYield
    · let added := s.addClause normalized.lits true
      have hNonempty : 0 < normalized.lits.size := by
        have nonzero : normalized.lits.size ≠ 0 := by simpa using empty
        omega
      have hWellFormed : ∀ lit ∈ normalized.lits, LiteralBound s.nVars lit := by
        intro lit member
        have bounds := hSpec.wellFormed lit member
        exact ⟨bounds.1, Nat.le_trans bounds.2 (by rw [hInv.state.variables]; omega)⟩
      have storedAdded := stored.addOriginal hInv.state.reserved hWellFormed
      have meaningAdded := prefix_add added.2 hIdx meaning hSpec
      have watchedAdded := watched.addClause valid.arrays hInv.state.reserved hWellFormed
        hNonempty hSpec.noDuplicates
      have properAdded : ReasonDatabase added.1 (original ++ [⟨added.2, normalized.lits⟩]) := by
        simpa only [added, addClause_assigned] using proper.addClause normalized.lits true
      have keepAdded : InitialWatchDatabase formula (idx + 1) added.1 :=
        ⟨_, _, storedAdded, meaningAdded, watchedAdded, properAdded⟩
      have keepAssigned (unmarked : added.1.mark normalized.lits[0]! = 0)
          (opposite : added.1.mark normalized.lits[0]!.negate = 0) :
          InitialWatchDatabase formula (idx + 1) (added.1.assign added.2 true) := by
        have packed : PackedClause added.1 added.2 normalized.lits :=
          addClause_packed hInv.state.reserved hWellFormed
        have head : added.1.db added.2 = normalized.lits[0]! := by
          simpa only [Nat.add_zero] using packed.literals 0 hNonempty
        have member : added.1.db added.2 ∈ normalized.lits := by
          rw [head, getElem!_pos normalized.lits 0 hNonempty]
          exact Array.getElem_mem hNonempty
        have addedValid := valid.addClause normalized.lits true
        have assignedProper := properAdded.assign (entry := ⟨added.2, normalized.lits⟩)
          (by simp) true addedValid.arrays addedValid.active addedValid.distinct
          (packed.wellFormed _ member) (by simpa only [head] using unmarked)
          (by simpa only [head] using opposite)
        exact ⟨_, _, storedAdded.assign _ _, meaningAdded, watchedAdded.assign _ _, assignedProper⟩
      by_cases unit : normalized.lits.size = 1
      · have hHeadRead : normalized.lits[0]! = normalized.lits[0] :=
          getElem!_pos normalized.lits 0 (by omega)
        by_cases conflict : added.1.mark normalized.lits[0]! ≠ 0
        · have conflictIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] ≠ 0 := by
            simpa only [added, hHeadRead] using conflict
          simp [initializationBody, hNormalize, notTautology, empty, unit, conflictIndex,
            Bind.bind, Except.bind, Pure.pure, Except.pure] at hYield
        · have unmarkedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0] = 0 := by
            have unmarked : added.1.mark normalized.lits[0]! = 0 := by simpa using conflict
            simpa only [added, hHeadRead] using unmarked
          by_cases assigned : added.1.mark normalized.lits[0]!.negate = 0
          · have assignedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0].negate = 0 := by
              simpa only [added, hHeadRead] using assigned
            apply finish _ (keepAssigned (by simpa using conflict) assigned)
            simp [initializationBody, hNormalize, notTautology, empty, unit, added,
              unmarkedIndex, assignedIndex, Bind.bind, Except.bind, Pure.pure, Except.pure]
          · have assignedIndex : (s.addClause normalized.lits true).1.mark normalized.lits[0].negate ≠ 0 := by
              simpa only [added, hHeadRead] using assigned
            apply finish _ keepAdded
            simp [initializationBody, hNormalize, notTautology, empty, unit, added,
              unmarkedIndex, assignedIndex, Bind.bind, Except.bind, Pure.pure, Except.pure]
      · apply finish _ keepAdded
        simp [initializationBody, hNormalize, notTautology, empty, unit, added,
          Bind.bind, Except.bind, Pure.pure, Except.pure]

theorem initialization_loop_watchDatabase {formula : Formula} (hWF : WellFormed formula)
    (fuel start : Nat) (hEnd : start + fuel ≤ formula.clauses.size)
    (s : State) (stamps : Array Nat) (hInv : InitializationLoopInvariant formula start s stamps)
    (valid : InitializedRepresentation s) (database : InitialWatchDatabase formula start s)
    {acc : InitializationAccumulator}
    (hRun : forIn (List.range' start fuel) (none, s, stamps) (initializationBody formula) = .ok acc)
    (continues : acc.1 = none) : InitialWatchDatabase formula (start + fuel) acc.2.1 := by
  induction fuel generalizing start s stamps acc with
  | zero =>
    have equal : (none, s, stamps) = acc := Except.ok.inj hRun
    exact congrArg (fun state : InitializationAccumulator => state.2.1) equal ▸ database
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
      have nextDatabase := initializationBody_watchDatabase hWF (by omega) hInv valid database hStep
      rw [List.range'_succ, List.forIn_cons, hStep] at hRun
      have final := ih (start + 1) (by omega) next nextStamps hNext nextValid nextDatabase hRun continues
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final

/-- Successful actual initialization supplies one common database/head witness
with complete linked lists, every long clause's two distinct watches, and no
references whose source is a unit or empty clause. -/
theorem initState_some_watchReasons {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s)) :
    ∃ original heads, Database s original [] ∧ DatabaseMeaning (formulaView formula) original [] ∧
      InitialWatchState s original heads ∧ ReasonDatabase s original := by
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
    have nextDatabase := initialization_loop_watchDatabase hWF formula.clauses.size 0 (by omega)
      initial stamps hInitial (emptyState_representation _ _) (emptyState_watchDatabase _ _) hRun rfl
    have initialized : initState formula config = .ok (some next) := by
      rw [initState_eq_loop, hRun]
      rfl
    have equal := Option.some.inj (Except.ok.inj (initialized.symm.trans hSome))
    subst s
    obtain ⟨original, heads, stored, meaning, watched, proper⟩ := nextDatabase
    refine ⟨original, heads, stored, ?_, watched, proper⟩
    constructor
    · simpa only [Nat.zero_add, inputPrefix_all] using meaning
    · simp only [databaseView_nil]
      exact CNF.entails_empty

theorem initState_some_watches {formula : Formula} (hWF : WellFormed formula)
    {config : Config} {s : State} (hSome : initState formula config = .ok (some s)) :
    ∃ original heads, Database s original [] ∧ DatabaseMeaning (formulaView formula) original [] ∧
      InitialWatchState s original heads := by
  obtain ⟨original, heads, database, meaning, watched, _⟩ := initState_some_watchReasons hWF hSome
  exact ⟨original, heads, database, meaning, watched⟩

/-- No slot belonging to a short genuine stored clause appears on any watch
list. Packed nonzero literals rule out confusing two different clause ends. -/
theorem InitialWatchState.short_not_mem {s : State} {original : List StoredClause}
    {heads : Nat → List Nat} (watched : InitialWatchState s original heads)
    (database : Database s original []) {entry : StoredClause} (stored : entry ∈ original)
    (short : entry.lits.size ≤ 1) (lit slot : Nat) (slotBound : slot ≤ 1) :
    2 * entry.id + slot ∉ heads lit := by
  intro member
  obtain ⟨other, otherStored, long, source⟩ := watched.references lit _ member
  have sameId : entry.id = other.id := by rcases source with first | second <;> omega
  have entryPacked := database.layout.packed (by simpa using stored)
  have otherPacked := database.layout.packed (by simpa using otherStored)
  have before : entry.lits.size < other.lits.size := by omega
  have literalMember : other.lits[entry.lits.size]! ∈ other.lits := by
    rw [getElem!_pos other.lits entry.lits.size before]
    exact Array.getElem_mem before
  have nonzero := (otherPacked.wellFormed _ literalMember).nonzero
  have read := otherPacked.literals entry.lits.size before
  rw [← sameId] at read
  exact nonzero (read.symm.trans entryPacked.terminator)

end MicrosatLean.Verification.Initialization
