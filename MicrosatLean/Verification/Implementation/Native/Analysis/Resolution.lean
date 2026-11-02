import MicrosatLean.Verification.Implementation.Native.Analysis.Mark
import MicrosatLean.Verification.Implementation.Native.Analysis.ReasonGraph

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation
open Std.Sat

/-- The current MARK set is read from the fixed original trail, including
entries whose active cursor has already been popped during analysis. -/
def markedLiterals (snapshot : State) (count : Nat) (s : State) : Array Lit :=
  (((List.range count).map fun i => snapshot.trail[i]!).filter fun lit => s.mark lit == 2).toArray

def markedClause (snapshot : State) (count : Nat) (s : State) : CNF.Clause Nat :=
  clauseView (markedLiterals snapshot count s)

@[simp] theorem markedLiterals_mem {snapshot s : State} {count : Nat} {lit : Lit} :
    lit ∈ markedLiterals snapshot count s ↔ TrailMember snapshot count lit ∧ s.mark lit = 2 := by
  simp only [markedLiterals, List.mem_toArray, List.mem_filter, List.mem_map,
    List.mem_range, beq_iff_eq, TrailMember]

/-- Tag six is justified independently of the changing MARK clause. During
resolution these are root consequences; minimization has not run yet. -/
def RootTagConsequences (formula : CNF Nat) (snapshot : State) (count : Nat) (s : State) : Prop :=
  ∀ lit, TrailMember snapshot count lit → s.mark lit = 6 →
    ∀ a, CNF.Sat a formula → Falsifies a lit

def MarksBefore (snapshot : State) (count : Nat) (s : State) : Prop :=
  ∀ i, i < count → s.mark snapshot.trail[i]! = 2 → i < s.assigned

def MarksThrough (snapshot : State) (count : Nat) (s : State) : Prop :=
  ∀ i, i < count → s.mark snapshot.trail[i]! = 2 → i ≤ s.assigned

private theorem unassign_mark_self_zero (s : State) (lit : Lit) :
    (s.unassign lit).mark lit = 0 := by
  by_cases bound : lit < s.marks.size
  · exact unassign_mark_same bound
  · simp [State.unassign, State.setMark, State.mark, Array.setIfInBounds, bound]

private theorem unassign_mark_two_iff (s : State) (target query : Lit) :
    (s.unassign target).mark query = 2 ↔ query ≠ target ∧ s.mark query = 2 := by
  by_cases same : query = target
  · subst query
    simp [unassign_mark_self_zero]
  · rw [unassign_mark_other (Ne.symm same)]
    exact ⟨fun h => ⟨same, h⟩, fun h => h.2⟩

private theorem unassign_rootTag {formula : CNF Nat} {snapshot s : State} {count : Nat}
    (root : RootTagConsequences formula snapshot count s) (target : Lit) :
    RootTagConsequences formula snapshot count (s.unassign target) := by
  intro lit member tag
  by_cases same : lit = target
  · subst lit
    rw [unassign_mark_self_zero] at tag
    contradiction
  · rw [unassign_mark_other (Ne.symm same)] at tag
    exact root lit member tag

private theorem marked_entails_of_inclusion {formula : CNF Nat} {snapshot before after : State}
    {count : Nat} (entailed : CNF.EntailsClause formula (markedClause snapshot count before))
    (included : ∀ lit, TrailMember snapshot count lit → before.mark lit = 2 → after.mark lit = 2) :
    CNF.EntailsClause formula (markedClause snapshot count after) := by
  intro a model
  obtain ⟨viewed, member, value⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp (entailed a model)
  obtain ⟨lit, old, equal⟩ := clauseView_mem.mp member
  obtain ⟨known, marked⟩ := markedLiterals_mem.mp old
  apply CNF.Clause.sat_of_mem_of_eq (lit := viewed) _ value
  exact clauseView_mem.mpr ⟨lit, markedLiterals_mem.mpr ⟨known, included lit known marked⟩, equal⟩

theorem ReasonStorage.packed {snapshot s : State} (storage : ReasonStorage snapshot s)
    (vars : s.nVars = snapshot.nVars) {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause snapshot clauseId lits) : PackedClause s clauseId lits := by
  refine ⟨packed.startLower, ?_, ?_, ?_, ?_⟩
  · simpa only [storage.arena] using packed.endBound
  · intro i before
    rw [storage.db]
    exact packed.literals i before
  · rw [storage.db]
    exact packed.terminator
  · simpa only [vars] using packed.wellFormed

theorem markClause_rootTag {formula : CNF Nat} {snapshot s : State} {count : Nat}
    {clauseId : Nat} {lits : Array Lit} (packed : PackedClause s clauseId lits)
    (arrays : ArrayBounds s) (root : RootTagConsequences formula snapshot count s)
    (offset : Nat) (inside : offset ≤ lits.size) :
    RootTagConsequences formula snapshot count (markClause s (clauseId + offset)) := by
  intro lit member tag
  exact root lit member ((markClause_mark_six_iff packed arrays offset inside lit).mp tag)

def resolutionBody (s : State) : Id (ForInStep State) := Id.run do
  let candidate := s.assigned - 1
  let mut s := { s with assigned := candidate }
  let lit := s.trail[candidate]!
  if s.reason lit == 0 then return .done s
  if s.mark lit == 2 then
    if firstUIP s candidate then return .done s
    s := markClause s (s.reason lit + 1)
  return .yield (s.unassign lit)

def resolutionScan : Nat → State → State
  | 0, s => s
  | fuel + 1, s =>
    match resolutionBody s with
    | .done next => next
    | .yield next => resolutionScan fuel next

private theorem resolutionRange_eq (fuel : Nat) (start : Nat) (s : State) :
    forIn (m := Id) (List.range' start fuel) s (fun _ state => resolutionBody state) =
      resolutionScan fuel s := by
  induction fuel generalizing start s with
  | zero => rfl
  | succ fuel ih =>
    rw [List.range'_succ, List.forIn_cons]
    simp only [bind, pure]
    cases hb : resolutionBody s <;> simp only [resolutionScan, hb, ih]

/-- The proof recursion is definitionally the real loop body, with the same
early exits and the same initial iteration budget. -/
theorem resolveToUIP_eq_scan (s : State) :
    resolveToUIP s = resolutionScan s.assigned s := by
  change (forIn (m := Id) [:s.assigned] s (fun _ state => resolutionBody state)) = _
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simpa only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] using
    resolutionRange_eq s.assigned 0 s

/-- Resolution only pops the active cursor, updates MARK tags, and bumps the
variable order. In particular all database and capacity metadata survive. -/
structure ResolutionFrame (before after : State) : Prop where
  restore : { after with
    marks := before.marks
    assigned := before.assigned
    previous := before.previous
    next := before.next
    head := before.head } = before
  marksSize : after.marks.size = before.marks.size
  previousSize : after.previous.size = before.previous.size
  nextSize : after.next.size = before.next.size

theorem ResolutionFrame.refl (s : State) : ResolutionFrame s s := ⟨rfl, rfl, rfl, rfl⟩

theorem ResolutionFrame.trans {first middle last : State}
    (before : ResolutionFrame first middle) (after : ResolutionFrame middle last) :
    ResolutionFrame first last := by
  constructor
  · exact (congrArg (fun s : State => { s with
      marks := first.marks
      assigned := first.assigned
      previous := first.previous
      next := first.next
      head := first.head }) after.restore).trans before.restore
  · exact after.marksSize.trans before.marksSize
  · exact after.previousSize.trans before.previousSize
  · exact after.nextSize.trans before.nextSize

theorem resolutionFrame_setAssigned (s : State) (assigned : Nat) :
    ResolutionFrame s { s with assigned := assigned } := ⟨rfl, rfl, rfl, rfl⟩

theorem resolutionFrame_setMark (s : State) (lit value : Nat) :
    ResolutionFrame s (s.setMark lit value) := by
  constructor
  · rfl
  · simp [State.setMark]
  · rfl
  · rfl

theorem resolutionFrame_markClause (s : State) (start : Nat) :
    ResolutionFrame s (markClause s start) := by
  have frame := markClause_frame s start
  refine ⟨?_, frame.marksSize, frame.previousSize, frame.nextSize⟩
  exact congrArg (fun after : State => { after with assigned := s.assigned }) frame.restore

theorem resolutionBody_frame (s : State) : ResolutionFrame s (resolutionBody s).value := by
  simp only [resolutionBody, Id.run, pure]
  split
  · exact resolutionFrame_setAssigned s _
  · split
    · split
      · exact resolutionFrame_setAssigned s _
      · exact ((resolutionFrame_setAssigned s _).trans (resolutionFrame_markClause _ _)).trans
          (resolutionFrame_setMark _ _ 0)
    · exact (resolutionFrame_setAssigned s _).trans (resolutionFrame_setMark _ _ 0)

private theorem resolutionScan_frame (fuel : Nat) (s : State) :
    ResolutionFrame s (resolutionScan fuel s) := by
  induction fuel generalizing s with
  | zero => exact ResolutionFrame.refl s
  | succ fuel ih =>
    have body := resolutionBody_frame s
    cases result : resolutionBody s with
    | done next => simpa only [resolutionScan, result, ForInStep.value_done] using body
    | yield next =>
      have nextFrame : ResolutionFrame s next := by simpa only [result, ForInStep.value_yield] using body
      simpa only [resolutionScan, result] using nextFrame.trans (ih next)

theorem resolveToUIP_frame (s : State) : ResolutionFrame s (resolveToUIP s) := by
  rw [resolveToUIP_eq_scan]
  exact resolutionScan_frame _ _

theorem ResolutionFrame.reasonStorage {snapshot before after : State}
    (frame : ResolutionFrame before after) (storage : ReasonStorage snapshot before) :
    ReasonStorage snapshot after := by
  constructor
  · exact (congrArg State.arena frame.restore).trans storage.arena
  · exact (congrArg State.reasons frame.restore).trans storage.reasons

theorem ResolutionFrame.trail {before after : State} (frame : ResolutionFrame before after) :
    after.trail = before.trail := by simpa only using congrArg State.trail frame.restore

theorem ResolutionFrame.nVars {before after : State} (frame : ResolutionFrame before after) :
    after.nVars = before.nVars := by simpa only using congrArg State.nVars frame.restore

theorem ResolutionFrame.nLemmas {before after : State} (frame : ResolutionFrame before after) :
    after.nLemmas = before.nLemmas := by simpa only using congrArg State.nLemmas frame.restore

theorem ResolutionFrame.maxLemmas {before after : State} (frame : ResolutionFrame before after) :
    after.maxLemmas = before.maxLemmas := by simpa only using congrArg State.maxLemmas frame.restore

theorem ResolutionFrame.arrayBounds {before after : State} (frame : ResolutionFrame before after)
    (arrays : ArrayBounds before) : ArrayBounds after := by
  have old : ArrayBounds { after with
      marks := before.marks
      assigned := before.assigned
      previous := before.previous
      next := before.next
      head := before.head } := by
    rw [frame.restore]
    exact arrays
  exact ⟨old.firstSize, frame.marksSize.trans old.marksSize, old.reasonsSize, old.phasesSize,
    old.trailSize, frame.previousSize.trans old.previousSize, frame.nextSize.trans old.nextSize⟩

private structure ResolutionFacts (formula : CNF Nat) (snapshot : State) (count : Nat) (s : State) : Prop where
  storage : ReasonStorage snapshot s
  trail : s.trail = snapshot.trail
  vars : s.nVars = snapshot.nVars
  arrays : ArrayBounds s
  root : RootTagConsequences formula snapshot count s
  entailed : CNF.EntailsClause formula (markedClause snapshot count s)

private theorem ResolutionFacts.transport {formula : CNF Nat} {snapshot before after : State} {count : Nat}
    (facts : ResolutionFacts formula snapshot count before) (frame : ResolutionFrame before after)
    (root : RootTagConsequences formula snapshot count after)
    (entailed : CNF.EntailsClause formula (markedClause snapshot count after)) :
    ResolutionFacts formula snapshot count after :=
  ⟨frame.reasonStorage facts.storage, frame.trail.trans facts.trail, frame.nVars.trans facts.vars,
    frame.arrayBounds facts.arrays, root, entailed⟩

private theorem ResolutionFacts.setAssigned {formula : CNF Nat} {snapshot s : State} {count : Nat}
    (facts : ResolutionFacts formula snapshot count s) (assigned : Nat) :
    ResolutionFacts formula snapshot count { s with assigned := assigned } :=
  facts.transport (resolutionFrame_setAssigned s assigned) facts.root facts.entailed

private theorem tail_mem_iff {lits : Array Lit} {lit : Lit} :
    lit ∈ lits.toList.drop 1 ↔ ∃ j, 0 < j ∧ j < lits.size ∧ lits[j]! = lit := by
  rw [List.mem_drop_iff_getElem]
  constructor
  · rintro ⟨j, bound, value⟩
    have before : 1 + j < lits.size := by simpa only [Array.length_toList, Nat.add_comm] using bound
    refine ⟨1 + j, by omega, before, ?_⟩
    simpa only [Array.getElem_toList, getElem!_pos lits (1 + j) before] using value
  · rintro ⟨j, positive, before, value⟩
    refine ⟨j - 1, by simp only [Array.length_toList]; omega, ?_⟩
    have index : 1 + (j - 1) = j := by omega
    simpa only [index, Array.getElem_toList, getElem!_pos lits j before] using value

private theorem resolveUnmarked_correct {formula : CNF Nat} {snapshot s : State} {count : Nat}
    (facts : ResolutionFacts formula snapshot count s) (p : Nat) (candidate : s.assigned = p)
    (through : MarksThrough snapshot count s) (notMarked : s.mark snapshot.trail[p]! ≠ 2) :
    ResolutionFacts formula snapshot count (s.unassign snapshot.trail[p]!) ∧
      MarksBefore snapshot count (s.unassign snapshot.trail[p]!) := by
  constructor
  · apply facts.transport (resolutionFrame_setMark s _ 0) (unassign_rootTag facts.root _)
    apply marked_entails_of_inclusion facts.entailed
    intro lit _ marked
    apply (unassign_mark_two_iff s _ lit).mpr
    refine ⟨?_, marked⟩
    intro equal
    exact notMarked (equal ▸ marked)
  · intro i before marked
    obtain ⟨different, old⟩ := (unassign_mark_two_iff s _ _).mp marked
    have atMost := through i before old
    have notEqual : i ≠ p := by
      intro equal
      exact different (equal ▸ rfl)
    change i < s.assigned
    rw [candidate] at atMost ⊢
    omega

private theorem resolveMarked_correct {formula : CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (facts : ResolutionFacts formula snapshot count s) (p : Nat) (before : p < count)
    (candidate : s.assigned = p) (through : MarksThrough snapshot count s)
    (nondecision : s.reason snapshot.trail[p]! ≠ 0) :
    let lit := snapshot.trail[p]!
    let next := (markClause s (s.reason lit + 1)).unassign lit
    ResolutionFacts formula snapshot count next ∧ MarksBefore snapshot count next := by
  let lit := snapshot.trail[p]!
  have known : TrailMember snapshot count lit := ⟨p, before, rfl⟩
  have reasonId := facts.storage.reason lit
  have snapshotReason : snapshot.reason lit ≠ 0 := by rw [← reasonId]; exact nondecision
  obtain ⟨lits, packed, nonempty, head, reasonEntailed, tails⟩ := graph.clause_of_member known snapshotReason
  have packedCurrent : PackedClause s (s.reason lit) lits := by
    rw [reasonId]
    exact facts.storage.packed facts.vars packed
  have inside : 1 ≤ lits.size := by omega
  let expanded := markClause s (s.reason lit + 1)
  let next := expanded.unassign lit
  have tags : ∀ query, next.mark query = 2 ↔ query ≠ lit ∧
      (s.mark query = 2 ∨ (query ∈ lits.toList.drop 1 ∧ s.mark query ≠ 6)) := by
    intro query
    rw [unassign_mark_two_iff, markClause_mark_two_iff packedCurrent facts.arrays 1 inside]
  have tailEarlier : ∀ query, query ∈ lits.toList.drop 1 →
      TrailMember snapshot count query ∧ rank query < p := by
    intro query member
    obtain ⟨j, positive, bound, equal⟩ := tail_mem_iff.mp member
    have result := tails j positive bound
    rw [equal, graph.ranks p before] at result
    exact result
  have tailDifferent : ∀ query, query ∈ lits.toList.drop 1 → query ≠ lit := by
    intro query member equal
    have earlier := (tailEarlier query member).2
    rw [equal, graph.ranks p before] at earlier
    omega
  have rootExpanded : RootTagConsequences formula snapshot count expanded :=
    markClause_rootTag packedCurrent facts.arrays facts.root 1 inside
  have entailment : CNF.EntailsClause formula (markedClause snapshot count next) := by
    intro a model
    by_cases satisfied : CNF.Clause.Sat a (markedClause snapshot count next)
    · exact satisfied
    · have newFalse : ∀ query, TrailMember snapshot count query → next.mark query = 2 →
          Falsifies a query := by
        intro query member marked
        apply CNF.Clause.not_sat_iff_forall_mem_ne.mp satisfied (literalView query)
        exact clauseView_mem.mpr ⟨query, markedLiterals_mem.mpr ⟨member, marked⟩, rfl⟩
      have tailFalse : ∀ query, query ∈ lits.toList.drop 1 → Falsifies a query := by
        intro query member
        have earlier := tailEarlier query member
        by_cases root : s.mark query = 6
        · exact facts.root query earlier.1 root a model
        · exact newFalse query earlier.1 ((tags query).mpr
            ⟨tailDifferent query member, Or.inr ⟨member, root⟩⟩)
      have headTrue : a (literalView lit.negate).1 = (literalView lit.negate).2 := by
        apply Logic.forced_of_sat (reasonEntailed a model)
        intro viewed member different
        obtain ⟨encoded, encodedMember, equal⟩ := clauseView_mem.mp member
        obtain ⟨j, bound, value⟩ := Array.mem_iff_getElem.mp encodedMember
        have value' : lits[j]! = encoded := by simpa only [getElem!_pos lits j bound] using value
        by_cases first : j = 0
        · subst j
          exact False.elim (different (equal.symm.trans (congrArg literalView (value'.symm.trans head))))
        · have original : encoded ∈ lits.toList.drop 1 :=
            tail_mem_iff.mpr ⟨j, by omega, bound, value'⟩
          simpa only [Falsifies, equal] using tailFalse encoded original
      have pivotFalse : Falsifies a lit := by
        have h := (falsifies_negate_iff a lit.negate).mpr headTrue
        simpa only [negate_negate] using h
      have oldFalse : ¬ CNF.Clause.Sat a (markedClause snapshot count s) := by
        apply CNF.Clause.not_sat_iff_forall_mem_ne.mpr
        intro viewed member
        obtain ⟨query, oldMember, equal⟩ := clauseView_mem.mp member
        obtain ⟨known, marked⟩ := markedLiterals_mem.mp oldMember
        have falseQuery : Falsifies a query := by
          by_cases same : query = lit
          · exact same ▸ pivotFalse
          · exact newFalse query known ((tags query).mpr ⟨same, Or.inl marked⟩)
        simpa only [Falsifies, equal] using falseQuery
      exact False.elim (oldFalse (facts.entailed a model))
  constructor
  · exact facts.transport ((resolutionFrame_markClause s _).trans (resolutionFrame_setMark expanded lit 0))
      (unassign_rootTag rootExpanded lit) entailment
  · intro i inRange marked
    obtain ⟨different, old | added⟩ := (tags snapshot.trail[i]!).mp marked
    · have atMost := through i inRange old
      have notEqual : i ≠ p := by
        intro same
        exact different (same ▸ rfl)
      simp only [State.unassign, State.setMark, markClause_assigned]
      rw [candidate] at atMost ⊢
      omega
    · have earlier := (tailEarlier snapshot.trail[i]! added.1).2
      rw [graph.ranks i inRange] at earlier
      simp only [State.unassign, State.setMark, markClause_assigned]
      rw [candidate]
      exact earlier

private def ResolutionStep (formula : CNF Nat) (snapshot : State) (count before : Nat)
    (result : ForInStep State) : Prop :=
  match result with
  | .done next => ResolutionFacts formula snapshot count next ∧
      MarksThrough snapshot count next ∧ next.assigned < before
  | .yield next => ResolutionFacts formula snapshot count next ∧
      MarksBefore snapshot count next ∧ next.assigned + 1 = before

private theorem resolutionBody_correct {formula : CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (facts : ResolutionFacts formula snapshot count s) (positive : 0 < s.assigned)
    (bound : s.assigned ≤ count) (below : MarksBefore snapshot count s) :
    ResolutionStep formula snapshot count s.assigned (resolutionBody s) := by
  let p := s.assigned - 1
  let popped := { s with assigned := p }
  let lit := s.trail[p]!
  have read : lit = snapshot.trail[p]! := by simp only [lit, facts.trail]
  have pBound : p < count := by dsimp only [p]; omega
  have cursor : p + 1 = s.assigned := by dsimp only [p]; omega
  have popFacts : ResolutionFacts formula snapshot count popped := facts.setAssigned p
  have through : MarksThrough snapshot count popped := by
    intro i before marked
    have old := below i before marked
    change i ≤ p
    omega
  simp only [resolutionBody, Id.run, pure]
  change ResolutionStep formula snapshot count s.assigned
    (if popped.reason lit == 0 then .done popped
    else if popped.mark lit == 2 then
      if firstUIP popped p then .done popped
      else .yield ((markClause popped (popped.reason lit + 1)).unassign lit)
    else .yield (popped.unassign lit))
  split
  · exact ⟨popFacts, through, by change p < s.assigned; omega⟩
  · have nondecision : popped.reason lit ≠ 0 := by
      simpa using ‹¬ (popped.reason lit == 0) = true›
    split
    · split
      · exact ⟨popFacts, through, by change p < s.assigned; omega⟩
      · have next := resolveMarked_correct graph popFacts p pBound rfl through
          (by simpa only [← read] using nondecision)
        rw [← read] at next
        refine ⟨next.1, next.2, ?_⟩
        simpa only [State.unassign, State.setMark, markClause_assigned] using cursor
    · have notMarked : popped.mark lit ≠ 2 := by
        simpa using ‹¬ (popped.mark lit == 2) = true›
      have next := resolveUnmarked_correct popFacts p rfl through (by simpa only [← read] using notMarked)
      rw [← read] at next
      exact ⟨next.1, next.2, cursor⟩

private theorem resolutionScan_correct {formula : CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank) (fuel : Nat) (s : State)
    (facts : ResolutionFacts formula snapshot count s) (assigned : s.assigned = fuel)
    (bound : fuel ≤ count) (below : MarksBefore snapshot count s) :
    ResolutionFacts formula snapshot count (resolutionScan fuel s) ∧
      MarksThrough snapshot count (resolutionScan fuel s) ∧
      (resolutionScan fuel s).assigned ≤ s.assigned := by
  induction fuel generalizing s with
  | zero =>
    refine ⟨facts, ?_, Nat.le_refl _⟩
    intro i before marked
    exact Nat.le_of_lt (below i before marked)
  | succ fuel ih =>
    have step := resolutionBody_correct graph facts (by omega) (by omega) below
    cases result : resolutionBody s with
    | done next =>
      have final : ResolutionFacts formula snapshot count next ∧
          MarksThrough snapshot count next ∧ next.assigned < s.assigned := by
        simpa only [result, ResolutionStep] using step
      simpa only [resolutionScan, result] using
        And.intro final.1 (And.intro final.2.1 (Nat.le_of_lt final.2.2))
    | yield next =>
      have final : ResolutionFacts formula snapshot count next ∧
          MarksBefore snapshot count next ∧ next.assigned + 1 = s.assigned := by
        simpa only [result, ResolutionStep] using step
      have after := ih next final.1 (by omega) (by omega) final.2.1
      have monotone : (resolutionScan fuel next).assigned ≤ s.assigned := by omega
      simpa only [resolutionScan, result] using And.intro after.1 (And.intro after.2.1 monotone)

/-- The actual first-UIP resolution phase preserves entailment of its concrete
MARK clause. Each expanded reason is entailed and has strictly earlier tails;
omitted tag-six tails are independently false in every input model. The
returned MARK entries are all at or below the returned candidate cursor. -/
theorem resolveToUIP_sound {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (s : State)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (vars : s.nVars = snapshot.nVars) (arrays : ArrayBounds s)
    (root : RootTagConsequences formula snapshot count s)
    (entailed : CNF.EntailsClause formula (markedClause snapshot count s))
    (assignedBound : s.assigned ≤ count) (below : MarksBefore snapshot count s) :
    CNF.EntailsClause formula (markedClause snapshot count (resolveToUIP s)) ∧
      RootTagConsequences formula snapshot count (resolveToUIP s) ∧
      MarksThrough snapshot count (resolveToUIP s) ∧ (resolveToUIP s).assigned ≤ s.assigned := by
  have final := resolutionScan_correct graph s.assigned s
    ⟨storage, trail, vars, arrays, root, entailed⟩ rfl assignedBound below
  rw [resolveToUIP_eq_scan]
  exact ⟨final.1.entailed, final.1.root, final.2⟩

/-- At the initial conflict-analysis entry, `assigned` still counts the whole
fixed snapshot prefix, so confinement before that cursor is automatic. -/
theorem resolveToUIP_sound_of_count {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (s : State)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (vars : s.nVars = snapshot.nVars) (arrays : ArrayBounds s)
    (root : RootTagConsequences formula snapshot count s)
    (entailed : CNF.EntailsClause formula (markedClause snapshot count s))
    (assigned : s.assigned = count) :
    CNF.EntailsClause formula (markedClause snapshot count (resolveToUIP s)) ∧
      RootTagConsequences formula snapshot count (resolveToUIP s) ∧
      MarksThrough snapshot count (resolveToUIP s) ∧ (resolveToUIP s).assigned ≤ count := by
  have below : MarksBefore snapshot count s := by
    intro i before _
    simpa only [assigned] using before
  simpa only [assigned] using resolveToUIP_sound graph s storage trail vars arrays root entailed
    (Nat.le_of_eq assigned) below

/-- Marking a covered entailed conflict supplies the initial MARK-clause
entailment. Root-tag omissions are discharged from independent consequences;
no entailment assumption about the resulting MARK set is needed. -/
theorem markClause_entails_of_clause {formula : CNF Nat} {snapshot s : State} {count clauseId : Nat}
    {lits : Array Lit} (packed : PackedClause s clauseId lits) (arrays : ArrayBounds s)
    (root : RootTagConsequences formula snapshot count s)
    (covered : ∀ lit ∈ lits, TrailMember snapshot count lit)
    (entailed : CNF.EntailsClause formula (clauseView lits)) :
    CNF.EntailsClause formula (markedClause snapshot count (markClause s clauseId)) := by
  intro a model
  obtain ⟨viewed, member, value⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp (entailed a model)
  obtain ⟨lit, original, equal⟩ := clauseView_mem.mp member
  by_cases rootTag : s.mark lit = 6
  · have falseLit := root lit (covered lit original) rootTag a model
    exact False.elim (falseLit (by simpa only [equal] using value))
  · have marked : (markClause s clauseId).mark lit = 2 := by
      simpa only [Nat.add_zero] using markClause_mark_member packed arrays 0 (Nat.zero_le _)
        (by simpa using original) rootTag
    apply CNF.Clause.sat_of_mem_of_eq (lit := viewed) _ value
    exact clauseView_mem.mpr ⟨lit, markedLiterals_mem.mpr ⟨covered lit original, marked⟩, equal⟩

theorem resolutionBody_assigned (s : State) : (resolutionBody s).value.assigned = s.assigned - 1 := by
  simp only [resolutionBody, Id.run, pure]
  split <;> repeat first
    | split
    | rfl
    | simp only [ForInStep.value_yield, State.unassign, State.setMark, markClause_assigned]

theorem resolutionScan_assigned_le (fuel : Nat) (s : State) :
    (resolutionScan fuel s).assigned ≤ s.assigned := by
  induction fuel generalizing s with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    have cursor := resolutionBody_assigned s
    cases result : resolutionBody s with
    | done next => simpa only [resolutionScan, result, ForInStep.value_done] using
        Nat.le_trans (Nat.le_of_eq cursor) (Nat.sub_le s.assigned 1)
    | yield next =>
      have nextCursor : next.assigned = s.assigned - 1 := by simpa only [result, ForInStep.value_yield] using cursor
      simpa only [resolutionScan, result] using
        Nat.le_trans (ih next) (Nat.le_trans (Nat.le_of_eq nextCursor) (Nat.sub_le s.assigned 1))

theorem resolveToUIP_assigned_lt (s : State) (positive : 0 < s.assigned) :
    (resolveToUIP s).assigned < s.assigned := by
  rw [resolveToUIP_eq_scan]
  cases assigned : s.assigned with
  | zero => omega
  | succ fuel =>
    have cursor := resolutionBody_assigned s
    cases result : resolutionBody s with
    | done next =>
      have nextCursor : next.assigned = fuel := by simpa only [result, ForInStep.value_done, assigned,
        Nat.add_sub_cancel] using cursor
      simpa only [resolutionScan, result, nextCursor] using Nat.lt_succ_self fuel
    | yield next =>
      have nextCursor : next.assigned = fuel := by simpa only [result, ForInStep.value_yield, assigned,
        Nat.add_sub_cancel] using cursor
      have bound := resolutionScan_assigned_le fuel next
      simpa only [resolutionScan, result] using Nat.lt_of_le_of_lt bound (by omega : next.assigned < fuel + 1)

end MicrosatLean.Verification.Implementation.Native.Analysis
