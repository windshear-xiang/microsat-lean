import MicrosatLean.Verification.Implementation.Search.Concrete.Decision
import MicrosatLean.Verification.Implementation.Propagation.DatabaseClosure
import MicrosatLean.Verification.Implementation.Search.Concrete.AnalysisProgress

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation
open Std.Sat

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

end MicrosatLean.Verification.Implementation.Search.Concrete

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Std.Sat

/-- The reusable decision cursor names a position in the actual MTF list.
Every entry before it has already been assigned; entries at or after it are
checked by the next concrete scan. Starts beyond the list denote zero. -/
def DecisionCursor (s : State) (cursor : Nat) : Prop :=
  ∃ order start, MTFOrder s order ∧ cursor = order.getD start 0 ∧
    ∀ i, i < start → i < order.length → AssignedVariable s (order.getD i 0)

private theorem getD_mem {order : List Nat} {i : Nat} (before : i < order.length) :
    order.getD i 0 ∈ order := by
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem before, Option.getD_some]
    using List.getElem_mem before

private theorem getD_zero {order : List Nat} {i : Nat} (after : order.length ≤ i) :
    order.getD i 0 = 0 := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none after, Option.getD_none]

theorem DecisionCursor.head {s : State} (coverage : MTFCoverage s) : DecisionCursor s s.head := by
  obtain ⟨order, valid⟩ := coverage
  refine ⟨order, 0, valid, valid.2.2.1.trans List.headD_eq_getD, ?_⟩
  intro i before
  omega

theorem DecisionCursor.declared_or_zero {s : State} {cursor : Nat} (covered : DecisionCursor s cursor) :
    cursor = 0 ∨ (1 ≤ cursor ∧ cursor ≤ s.nVars) := by
  obtain ⟨order, start, valid, value, _⟩ := covered
  by_cases before : start < order.length
  · exact Or.inr (value ▸ (valid.2.1 _).mp (getD_mem before))
  · exact Or.inl (value.trans (getD_zero (by omega)))

private theorem scan_succ {s : State} {cursor fuel : Nat} (nonzero : cursor ≠ 0) :
    nextDecisionScan (fuel + 1) s cursor =
      if UnassignedVariable s cursor then cursor else nextDecisionScan fuel s s.previous[cursor]! := by
  simp only [nextDecisionScan, Bool.and_eq_true, beq_iff_eq, nonzero, ite_false, UnassignedVariable]
  rfl

/-- A successful actual scan returns a later position of the same list and
has marked every skipped entry assigned. This is proved from the executable
recursive branches, including the real previous-link values. -/
theorem nextDecisionScan_selected_prefix {s : State} {order : List Nat}
    (valid : MTFOrder s order) (fuel start : Nat)
    (nonzero : nextDecisionScan fuel s (order.getD start 0) ≠ 0) :
    ∃ selected, start ≤ selected ∧ selected < order.length ∧ selected < start + fuel ∧
      nextDecisionScan fuel s (order.getD start 0) = order.getD selected 0 ∧
      ∀ i, start ≤ i → i < selected → AssignedVariable s (order.getD i 0) := by
  induction fuel generalizing start with
  | zero => simp only [nextDecisionScan, ne_eq, not_true_eq_false] at nonzero
  | succ fuel ih =>
    have before : start < order.length := by
      by_cases before : start < order.length
      · exact before
      · have zero := getD_zero (order := order) (i := start) (by omega)
        simp only [nextDecisionScan, zero, beq_self_eq_true, ite_true, ne_eq, not_true_eq_false] at nonzero
    have cursorNonzero := Representation.Order.order_getD_ne_zero valid before
    by_cases unset : UnassignedVariable s (order.getD start 0)
    · refine ⟨start, Nat.le_refl _, before, by omega, ?_, ?_⟩
      · rw [scan_succ cursorNonzero, ite_eq_left unset]
      · intro i lower upper
        omega
    · have tailNonzero : nextDecisionScan fuel s (order.getD (start + 1) 0) ≠ 0 := by
        rw [scan_succ cursorNonzero, ite_eq_right unset, (valid.2.2.2 start before).1] at nonzero
        exact nonzero
      obtain ⟨selected, lower, upper, budget, value, skipped⟩ := ih (start + 1) tailNonzero
      refine ⟨selected, by omega, upper, by omega, ?_, ?_⟩
      · rw [scan_succ cursorNonzero, ite_eq_right unset, (valid.2.2.2 start before).1]
        exact value
      · intro i atStart beforeSelected
        by_cases first : i = start
        · subst i
          exact assignedVariable_of_not_unassigned unset
        · exact skipped i (by omega) beforeSelected

theorem DecisionCursor.advance {s : State} {cursor : Nat} (covered : DecisionCursor s cursor)
    (nonzero : nextDecision s cursor ≠ 0) : DecisionCursor s (nextDecision s cursor) := by
  obtain ⟨order, start, valid, value, prefixAssigned⟩ := covered
  have selected := nextDecisionScan_selected_prefix valid (s.nVars + 1) start (by simpa only [CDCL.nextDecision, ← value] using nonzero)
  obtain ⟨position, lower, upper, _, actual, skipped⟩ := selected
  refine ⟨order, position, valid, ?_, ?_⟩
  · simpa only [nextDecision, value] using actual
  · intro i beforePosition within
    by_cases old : i < start
    · exact prefixAssigned i old within
    · exact skipped i (by omega) beforePosition

private theorem setMark_preserves_nonzero {s : State} {lit target value : Nat}
    (nonzero : value ≠ 0) (marked : s.mark lit ≠ 0) : (s.setMark target value).mark lit ≠ 0 := by
  by_cases same : target = lit
  · subst target
    by_cases bound : lit < s.marks.size
    · simpa only [setMark_mark_same bound] using nonzero
    · have zero : s.mark lit = 0 := by
        simp only [State.mark, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
          Array.getElem?_eq_none (by omega : s.marks.size ≤ lit), Option.getD_none]
        rfl
      exact False.elim (marked zero)
  · simpa only [setMark_mark_other same] using marked

theorem AssignedVariable.setMark {s : State} {var : Nat} (assigned : AssignedVariable s var)
    (target value : Nat) (nonzero : value ≠ 0) : AssignedVariable (s.setMark target value) var := by
  rcases assigned with positive | negative
  · exact Or.inl (setMark_preserves_nonzero nonzero positive)
  · exact Or.inr (setMark_preserves_nonzero nonzero negative)

theorem AssignedVariable.assign {s : State} {var : Nat} (assigned : AssignedVariable s var)
    (id : Nat) (root : Bool) : AssignedVariable (s.assign id root) var := by
  change AssignedVariable (s.setMark (Lit.negate (s.db id)) (if root then 6 else 1)) var
  exact assigned.setMark _ _ (by cases root <;> decide)

theorem AssignedVariable.decide {s : State} {var : Nat} (assigned : AssignedVariable s var)
    (selected : Nat) : AssignedVariable (s.decide selected) var := by
  change AssignedVariable (s.setMark (decisionLiteral s selected).negate 1) var
  exact assigned.setMark _ _ (by decide)

theorem DecisionCursor.assign {s : State} {cursor : Nat} (covered : DecisionCursor s cursor)
    (id : Nat) (root : Bool) : DecisionCursor (s.assign id root) cursor := by
  obtain ⟨order, start, valid, value, prefixAssigned⟩ := covered
  exact ⟨order, start, valid.assign id root, value,
    fun i before within => (prefixAssigned i before within).assign id root⟩

theorem DecisionCursor.decide {s : State} {cursor : Nat} (covered : DecisionCursor s cursor)
    (selected : Nat) : DecisionCursor (s.decide selected) cursor := by
  obtain ⟨order, start, valid, value, prefixAssigned⟩ := covered
  exact ⟨order, start, valid.decide selected, value,
    fun i before within => (prefixAssigned i before within).decide selected⟩

/-- The real choose/decide branch advances coverage to its chosen variable.
Its newly assigned mark also preserves all previously covered entries. -/
theorem DecisionCursor.choose {s : State} {cursor : Nat} (covered : DecisionCursor s cursor)
    (nonzero : nextDecision s cursor ≠ 0) :
    DecisionCursor (s.decide (nextDecision s cursor)) (nextDecision s cursor) :=
  (covered.advance nonzero).decide _

theorem DecisionCursor.frame {before after : State} {cursor : Nat} (covered : DecisionCursor before cursor)
    (variables : after.nVars = before.nVars) (head : after.head = before.head)
    (previous : after.previous = before.previous) (next : after.next = before.next)
    (assigned : ∀ var, AssignedVariable before var → AssignedVariable after var) :
    DecisionCursor after cursor := by
  obtain ⟨order, start, valid, value, prefixAssigned⟩ := covered
  exact ⟨order, start, valid.frame variables head previous next, value,
    fun i before within => assigned _ (prefixAssigned i before within)⟩

theorem DecisionCursor.frameMarks {before after : State} {cursor : Nat} (covered : DecisionCursor before cursor)
    (variables : after.nVars = before.nVars) (head : after.head = before.head)
    (previous : after.previous = before.previous) (next : after.next = before.next)
    (marks : after.marks = before.marks) : DecisionCursor after cursor := by
  apply covered.frame variables head previous next
  intro var assigned
  simpa only [AssignedVariable, State.mark, marks] using assigned

theorem DecisionCursor.restoreWatchArrays {s : State} {cursor : Nat} (covered : DecisionCursor s cursor)
    (arena first : Array Nat) : DecisionCursor (restoreWatchArrays s arena first) cursor :=
  covered.frameMarks rfl rfl rfl rfl rfl

theorem DecisionCursor.addClause {s : State} {cursor : Nat} (covered : DecisionCursor s cursor)
    (lits : Array Lit) (original : Bool) : DecisionCursor (s.addClause lits original).1 cursor := by
  obtain ⟨order, start, valid, value, prefixAssigned⟩ := covered
  refine ⟨order, start, valid.addClause lits original, value, ?_⟩
  intro i before within
  simpa only [AssignedVariable, State.mark, addClause_marks] using prefixAssigned i before within

theorem DecisionCursor.zero_all_assigned {s : State} {cursor : Nat} (covered : DecisionCursor s cursor)
    (finished : nextDecision s cursor = 0) :
    ∀ var, 1 ≤ var → var ≤ s.nVars → AssignedVariable s var := by
  obtain ⟨order, start, valid, value, prefixAssigned⟩ := covered
  exact nextDecision_zero_all_assigned valid start prefixAssigned (by simpa only [← value] using finished)

/-- The concrete cursor witness discharges the SAT rule's earlier-prefix
obligation; only the independent propagation-closure obligation remains. -/
theorem validResult_sat_of_decisionCursor {formula : Formula} {s : State} {cursor : Nat}
    (variables : formula.numVars ≤ s.nVars) (arrays : ArrayBounds s)
    (marks : MarkedOnTrail s) (phases : TrailPhases s)
    {original learned : List StoredClause} (database : Database s original learned)
    (meaning : DatabaseMeaning (formulaView formula) original learned)
    (closed : DatabaseNoConflict s (original ++ learned)) (covered : DecisionCursor s cursor)
    (finished : nextDecision s cursor = 0) : ValidResult formula (.sat s.phases s.stats) := by
  obtain ⟨order, start, valid, value, prefixAssigned⟩ := covered
  exact validResult_sat_of_database variables arrays marks phases database meaning closed valid start
    prefixAssigned (by simpa only [← value] using finished)

/-- The actual watch traversal preserves a reusable decision cursor on
every running return without learning. Array rewiring leaves the MTF order
alone; the unit branch only adds a nonzero mark. An analyzed return is
excluded by its concrete learned-clause counter increase. -/
theorem propagateWatches_decisionCursor (fuel : Nat) (s : State) (arena first : Array Nat)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat)
    (covered : DecisionCursor s decision) {after : Machine}
    (running : propagateWatches fuel s arena first decision oldLemmas root lit previous = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) :
    DecisionCursor after.solver after.decision := by
  induction fuel generalizing arena first previous with
  | zero =>
    simp only [propagateWatches] at running
    cases running
    exact covered.restoreWatchArrays arena first
  | succ fuel ih =>
    simp only [propagateWatches, Id.run, pure] at running
    generalize refEq : (if previous == 0 then first[lit]! else arena[watchLinkPos previous]!) = ref at running
    split at running
    · cases running
      exact covered.restoreWatchArrays arena first
    · generalize orientedEq : (if arena[watchClause ref]! == lit then
          arena.set! (watchClause ref) arena[watchClause ref + 1]! else arena) = oriented at running
      cases found : replacement oriented s.marks (watchClause ref) with
      | some pos =>
        simp only [found] at running
        exact ih _ _ _ running
      | none =>
        simp only [found] at running
        split at running
        · exact ih _ _ _ running
        · split at running
          · cases running
            exact (covered.restoreWatchArrays _ _).assign _ _
          · split at running
            · cases running
            · cases running
              have learned := analyze_nLemmas
                (restoreWatchArrays s (oriented.set! (watchClause ref + 1) lit) first) (watchClause ref)
              simp only [State.assign, Id.run, pure, restoreWatchArrays] at noAnalysis
              simp only [restoreWatchArrays] at learned
              omega

/-- This is the concrete `.watch` branch of `step`, including its temporary
array detachment and actual arena-sized traversal budget. -/
theorem step_watch_decisionCursor (s : State) (decision oldLemmas : Nat) (root : Bool)
    (lit : Lit) (previous : Nat) (covered : DecisionCursor s decision) {after : Machine}
    (running : step ⟨s, decision, .watch, oldLemmas, root, lit, previous⟩ = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) :
    DecisionCursor after.solver after.decision := by
  change propagateWatches s.arena.size { s with arena := #[], first := #[] } s.arena s.first
    decision oldLemmas root lit previous = .running after at running
  exact propagateWatches_decisionCursor s.arena.size { s with arena := #[], first := #[] }
    s.arena s.first decision oldLemmas root lit previous
    (covered.frameMarks rfl rfl rfl rfl rfl) running noAnalysis

end MicrosatLean.Verification.Implementation.Search.Concrete
