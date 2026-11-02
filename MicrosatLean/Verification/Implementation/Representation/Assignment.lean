import MicrosatLean.Verification.Implementation.Representation.State

namespace MicrosatLean.Verification.Implementation.Representation

open CDCL

/-- The variable is absent from the active trail, independently of stale
reason or phase entries belonging to an earlier assignment. -/
def FreshVariable (s : State) (var : Nat) : Prop :=
  ∀ i, i < s.assigned → s.trail[i]!.var ≠ var

variable {s : State} {lit other : Lit} {clauseId var i : Nat} {root : Bool}

/-- The executable unassigned test implies freshness on a consistent trail. -/
theorem freshVariable_of_unmarked (active : ActiveTrail s)
    (positive : s.mark (2 * var) = 0) (negative : s.mark (2 * var + 1) = 0) :
    FreshVariable s var := by
  intro i before same
  have marked := (active i before).2.1
  rcases literal_encoding s.trail[i]! with encoded | encoded
  · rw [same] at encoded
    exact marked ((congrArg s.mark encoded).trans positive)
  · rw [same] at encoded
    exact marked ((congrArg s.mark encoded).trans negative)

theorem assign_mark_other (different : Lit.negate (s.db clauseId) ≠ other) :
    (s.assign clauseId root).mark other = s.mark other := by
  exact Array.getElem!_set!_ne s.marks _ other _ different

theorem assign_falseAssignment (bound : Lit.negate (s.db clauseId) < s.marks.size)
    (unmarked : s.mark (s.db clauseId) = 0) :
    FalseAssignment (s.assign clauseId root) (Lit.negate (s.db clauseId)) := by
  change FalseAssignment (s.setMark (Lit.negate (s.db clauseId)) (if root then 6 else 1)) _
  apply setMark_falseAssignment bound
  · cases root <;> decide
  · simpa using unmarked

theorem assign_saved_phase (bound : Lit.var (s.db clauseId) < s.phases.size) :
    (s.assign clauseId root).phases[(Lit.negate (s.db clauseId)).var]! =
      (Lit.negate (s.db clauseId) % 2 == 1) := by
  rw [negate_var, assign_phase bound]
  rcases Nat.mod_two_eq_zero_or_one (s.db clauseId) with h | h <;>
    simp [negate_mod_two, h]

theorem FreshVariable.ne_literal (fresh : FreshVariable s var) (before : i < s.assigned)
    (sameVariable : lit.var = var) : lit ≠ s.trail[i]! := by
  intro equal
  apply fresh i before
  rw [← equal, sameVariable]

theorem FreshVariable.ne_negated_literal (fresh : FreshVariable s var) (before : i < s.assigned)
    (sameVariable : lit.var = var) : lit ≠ s.trail[i]!.negate := by
  intro equal
  apply fresh i before
  have := congrArg Lit.var equal
  simpa [sameVariable] using this.symm

theorem ActiveTrail.assign (active : ActiveTrail s) (arrays : ArrayBounds s)
    (literal : LiteralBound s.nVars (s.db clauseId)) (space : s.assigned < s.trail.size)
    (fresh : FreshVariable s (Lit.var (s.db clauseId))) (unmarked : s.mark (s.db clauseId) = 0) :
    ActiveTrail (s.assign clauseId root) := by
  intro i before
  have before' : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [assign_trail_last space]
    constructor
    · exact literal.negate
    · exact assign_falseAssignment (arrays.literal_index literal.negate).1 unmarked
  · have earlier : i < s.assigned := by omega
    rw [assign_trail_prefix earlier]
    have old := active i earlier
    constructor
    · exact old.1
    · constructor
      · rw [assign_mark_other (fresh.ne_literal earlier (negate_var _))]
        exact old.2.1
      · rw [assign_mark_other (fresh.ne_negated_literal earlier (negate_var _))]
        exact old.2.2

theorem TrailPhases.assign (phases : TrailPhases s) (arrays : ArrayBounds s)
    (literal : LiteralBound s.nVars (s.db clauseId)) (space : s.assigned < s.trail.size)
    (fresh : FreshVariable s (Lit.var (s.db clauseId))) : TrailPhases (s.assign clauseId root) := by
  intro i before
  have before' : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [assign_trail_last space]
    exact assign_saved_phase (arrays.variable_index literal.2).2.1
  · have earlier : i < s.assigned := by omega
    rw [assign_trail_prefix earlier]
    change (s.phases.set! (Lit.var (s.db clauseId)) _)[s.trail[i]!.var]! = _
    rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm (fresh i earlier))]
    exact phases i earlier

/-- The exact literal selected by the runtime's phase-saving decision. -/
def decisionLiteral (s : State) (var : Nat) : Lit :=
  2 * var + if s.phases[var]! then 0 else 1

@[simp] theorem decisionLiteral_var (s : State) (var : Nat) :
    (decisionLiteral s var).var = var := by
  unfold decisionLiteral Lit.var
  split <;> omega

theorem decisionLiteral_bound (lower : 1 ≤ var) (upper : var ≤ s.nVars) :
    LiteralBound s.nVars (decisionLiteral s var) := by
  simpa [LiteralBound] using And.intro lower upper

theorem decide_trail_last (space : s.assigned < s.trail.size) :
    (s.decide var).trail[s.assigned]! = (decisionLiteral s var).negate := by
  exact Array.getElem!_set!_self s.trail s.assigned _ space

theorem decide_mark_other (different : (decisionLiteral s var).negate ≠ other) :
    (s.decide var).mark other = s.mark other := by
  exact Array.getElem!_set!_ne s.marks _ other _ different

theorem decide_falseAssignment (bound : (decisionLiteral s var).negate < s.marks.size)
    (unmarked : s.mark (decisionLiteral s var) = 0) :
    FalseAssignment (s.decide var) (decisionLiteral s var).negate := by
  change FalseAssignment (s.setMark (decisionLiteral s var).negate 1) _
  apply setMark_falseAssignment bound (by decide)
  simpa using unmarked

theorem decide_saved_phase : s.phases[(decisionLiteral s var).negate.var]! =
    ((decisionLiteral s var).negate % 2 == 1) := by
  simp only [negate_var, decisionLiteral_var, negate_mod_two]
  unfold decisionLiteral
  cases s.phases[var]! <;> simp

theorem ActiveTrail.decide (active : ActiveTrail s) (arrays : ArrayBounds s)
    (lower : 1 ≤ var) (upper : var ≤ s.nVars) (space : s.assigned < s.trail.size)
    (fresh : FreshVariable s var) (unmarked : s.mark (decisionLiteral s var) = 0) :
    ActiveTrail (s.decide var) := by
  intro i before
  have before' : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [decide_trail_last space]
    have literal := decisionLiteral_bound lower upper
    constructor
    · exact literal.negate
    · exact decide_falseAssignment (arrays.literal_index literal.negate).1 unmarked
  · have earlier : i < s.assigned := by omega
    rw [decide_trail_prefix earlier]
    have old := active i earlier
    constructor
    · exact old.1
    · constructor
      · rw [decide_mark_other (fresh.ne_literal earlier (by simp))]
        exact old.2.1
      · rw [decide_mark_other (fresh.ne_negated_literal earlier (by simp))]
        exact old.2.2

theorem TrailPhases.decide (phases : TrailPhases s) (space : s.assigned < s.trail.size) :
    TrailPhases (s.decide var) := by
  intro i before
  have before' : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [decide_trail_last space, decide_phases]
    exact decide_saved_phase
  · have earlier : i < s.assigned := by omega
    rw [decide_trail_prefix earlier, decide_phases]
    exact phases i earlier

/-- Appending a fresh variable preserves uniqueness independently of a
particular state operation. The callers below instantiate the actual writes. -/
theorem DistinctTrailVariables.extend (distinct : DistinctTrailVariables s)
    (fresh : FreshVariable s var) (next : State) (cursor : next.assigned = s.assigned + 1)
    (earlier : ∀ i, i < s.assigned → next.trail[i]! = s.trail[i]!)
    (last : next.trail[s.assigned]!.var = var) : DistinctTrailVariables next := by
  intro i j beforeI beforeJ same
  rw [cursor] at beforeI beforeJ
  by_cases lastI : i = s.assigned
  · subst i
    by_cases lastJ : j = s.assigned
    · exact lastJ.symm
    · have before : j < s.assigned := by omega
      rw [last, earlier j before] at same
      exact False.elim (fresh j before same.symm)
  · have before : i < s.assigned := by omega
    by_cases lastJ : j = s.assigned
    · subst j
      rw [earlier i before, last] at same
      exact False.elim (fresh i before same)
    · have before' : j < s.assigned := by omega
      rw [earlier i before, earlier j before'] at same
      exact distinct i j before before' same

theorem DistinctTrailVariables.assign (distinct : DistinctTrailVariables s)
    (fresh : FreshVariable s (Lit.var (s.db clauseId))) (space : s.assigned < s.trail.size) :
    DistinctTrailVariables (s.assign clauseId root) := by
  apply distinct.extend fresh (s.assign clauseId root) rfl
  · exact fun _ before => assign_trail_prefix before
  · rw [assign_trail_last space, negate_var]

theorem DistinctTrailVariables.decide (distinct : DistinctTrailVariables s)
    (fresh : FreshVariable s var) (space : s.assigned < s.trail.size) :
    DistinctTrailVariables (s.decide var) := by
  apply distinct.extend fresh (s.decide var) rfl
  · exact fun _ before => decide_trail_prefix before
  · rw [decide_trail_last space, negate_var, decisionLiteral_var]

end MicrosatLean.Verification.Implementation.Representation
