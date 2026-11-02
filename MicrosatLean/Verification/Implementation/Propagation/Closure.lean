import MicrosatLean.Verification.Implementation.Representation.Semantics
import MicrosatLean.Verification.Implementation.Representation.Assignment
import MicrosatLean.Verification.Implementation.Representation.Restart

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL
open Representation
open Std.Sat

/-- Every nonzero mark in a stable search state belongs to its active trail. -/
def MarkedOnTrail (s : State) : Prop :=
  ∀ lit, s.mark lit ≠ 0 → ∃ i, i < s.assigned ∧ s.trail[i]! = lit

/-- Saved phases agree with every marked false literal. -/
def MarksSound (s : State) : Prop :=
  ∀ lit, LiteralBound s.nVars lit → s.mark lit ≠ 0 → Falsifies (assignment s.phases) lit

/-- A complete assignment marks one of the two polarities of every variable. -/
def AllVariablesAssigned (s : State) : Prop :=
  ∀ var, 1 ≤ var → var ≤ s.nVars → s.mark (2 * var) ≠ 0 ∨ s.mark (2 * var + 1) ≠ 0

/-- A conflict-free propagation boundary has a nonfalse literal in every
original clause. This property must be established by the watch refinement. -/
def NoConflict (s : State) (formula : Formula) : Prop :=
  ∀ clause ∈ formula.clauses, ∃ lit ∈ clause, s.mark lit = 0

theorem MarkedOnTrail.assign {s : State} (coverage : MarkedOnTrail s)
    {clauseId : Nat} {root : Bool} (space : s.assigned < s.trail.size) :
    MarkedOnTrail (s.assign clauseId root) := by
  intro lit marked
  by_cases same : Lit.negate (s.db clauseId) = lit
  · exact ⟨s.assigned, by simp [State.assign], (assign_trail_last space).trans same⟩
  · have old : s.mark lit ≠ 0 := by simpa only [assign_mark_other same] using marked
    obtain ⟨i, before, equal⟩ := coverage lit old
    exact ⟨i, by simpa [State.assign] using Nat.lt_succ_of_lt before,
      (assign_trail_prefix before).trans equal⟩

theorem MarkedOnTrail.decide {s : State} (coverage : MarkedOnTrail s)
    {var : Nat} (space : s.assigned < s.trail.size) : MarkedOnTrail (s.decide var) := by
  intro lit marked
  by_cases same : (decisionLiteral s var).negate = lit
  · exact ⟨s.assigned, by simp [State.decide], (decide_trail_last space).trans same⟩
  · have old : s.mark lit ≠ 0 := by simpa only [decide_mark_other same] using marked
    obtain ⟨i, before, equal⟩ := coverage lit old
    exact ⟨i, by simpa [State.decide] using Nat.lt_succ_of_lt before,
      (decide_trail_prefix before).trans equal⟩

theorem MarkedOnTrail.restart {s : State} (coverage : MarkedOnTrail s)
    (arrays : ArrayBounds s) (bounds : TrailBounds s) (active : ActiveTrail s) :
    MarkedOnTrail s.restart := by
  intro lit marked
  obtain ⟨i, root, equal⟩ := restart_marked_prefix arrays bounds active coverage lit marked
  exact ⟨i, by simpa only [restart_assigned bounds] using root,
    by simpa only [restart_trail] using equal⟩

theorem NoConflict.restart {s : State} {formula : Formula} (closed : NoConflict s formula) :
    NoConflict s.restart formula := by
  intro clause member
  obtain ⟨lit, hlit, unmarked⟩ := closed clause member
  exact ⟨lit, hlit, restart_mark_unmarked unmarked⟩

theorem marksSound_of_trail {s : State} (coverage : MarkedOnTrail s)
    (phases : TrailPhases s) : MarksSound s := by
  intro lit _ marked
  obtain ⟨i, hi, equal⟩ := coverage lit marked
  have phase := phases i hi
  rw [equal] at phase
  have opposite : s.phases[lit.var]! ≠ (lit % 2 == 0) := by
    rw [phase]
    rcases Nat.mod_two_eq_zero_or_one lit with parity | parity <;> simp [parity]
  simpa [Falsifies, literalView, assignment, Array.getElem!_eq_getD] using opposite

theorem marked_polarity_of_complete {s : State} (complete : AllVariablesAssigned s)
    {lit : Lit} (bound : LiteralBound s.nVars lit) :
    s.mark lit ≠ 0 ∨ s.mark lit.negate ≠ 0 := by
  have assigned := complete lit.var bound.1 bound.2
  have negVar := negate_var lit
  have negMod := negate_mod_two lit
  have litMod := Nat.mod_two_eq_zero_or_one lit
  have litValue := Nat.mod_add_div lit 2
  have negValue := Nat.mod_add_div lit.negate 2
  dsimp only [Lit.var] at *
  rcases litMod with parity | parity
  · rw [parity, Nat.zero_add] at litValue
    rw [parity, Nat.sub_zero] at negMod
    rw [negMod, negVar] at negValue
    have positive : s.mark lit = s.mark (2 * (lit / 2)) := congrArg s.mark litValue.symm
    have negative : s.mark lit.negate = s.mark (2 * (lit / 2) + 1) :=
      congrArg s.mark (show lit.negate = 2 * (lit / 2) + 1 from
        negValue.symm.trans (Nat.add_comm _ _))
    rwa [positive, negative]
  · rw [parity] at litValue negMod
    simp only [Nat.sub_self] at negMod
    rw [negMod, Nat.zero_add, negVar] at negValue
    have negative : s.mark lit = s.mark (2 * (lit / 2) + 1) :=
      congrArg s.mark (show lit = 2 * (lit / 2) + 1 from
        litValue.symm.trans (Nat.add_comm _ _))
    have positive : s.mark lit.negate = s.mark (2 * (lit / 2)) := congrArg s.mark negValue.symm
    rwa [negative, positive, or_comm]

/-- Once all variables are assigned, a literal that is not false is true in
the saved model. This connects the mark-based watch tests to Std semantics. -/
theorem true_of_unmarked {s : State} (sound : MarksSound s)
    (complete : AllVariablesAssigned s) {lit : Lit} (bound : LiteralBound s.nVars lit)
    (unmarked : s.mark lit = 0) :
    assignment s.phases (literalView lit).1 = (literalView lit).2 := by
  rcases marked_polarity_of_complete complete bound with marked | opposite
  · exact False.elim (marked unmarked)
  · exact (falsifies_negate_iff _ _).mp (sound lit.negate bound.negate opposite)

end MicrosatLean.Verification.Implementation.Propagation
