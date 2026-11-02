import MicrosatLean.Verification.Implementation.Native.Search.Decision
import MicrosatLean.Verification.Implementation.Native.Representation.Assignment
import MicrosatLean.Verification.Implementation.Native.Representation.Semantics

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation
open Std.Sat

/-- The decision literal expresses precisely the variable's saved phase. -/
@[simp] theorem decisionLiteral_view (s : State) (var : Nat) :
    literalView (decisionLiteral s var) = (var, s.phases[var]!) := by
  apply Prod.ext
  · exact decisionLiteral_var s var
  · cases phase : s.phases[var]! <;>
      simp [literalView, decisionLiteral, phase, Nat.add_mod]

/-- Deciding a variable preserves every old trail-prefix assumption. -/
theorem prefixCompatible_decide_iff {s : State} {a : Nat → Bool} {var count : Nat}
    (before : count ≤ s.assigned) :
    PrefixCompatible (s.decide var) a count ↔ PrefixCompatible s a count := by
  constructor <;> intro h i hi
  · have old : i < s.assigned := Nat.lt_of_lt_of_le hi before
    simpa only [decide_trail_prefix old] using h i hi
  · have old : i < s.assigned := Nat.lt_of_lt_of_le hi before
    simpa only [decide_trail_prefix old] using h i hi

/-- A concrete decision adds its chosen phase as an assumption; it does not
claim that the input formula entails that phase. -/
theorem trailCompatible_decide_iff {s : State} {a : Nat → Bool} {var : Nat}
    (space : s.assigned < s.trail.size) :
    TrailCompatible (s.decide var) a ↔
      TrailCompatible s a ∧ a var = s.phases[var]! := by
  constructor
  · intro h
    constructor
    · exact (prefixCompatible_decide_iff (Nat.le_refl _)).mp
        (h.mono (by simp [State.decide]))
    · have last := h s.assigned (by simp [State.decide])
      rw [decide_trail_last space, falsifies_negate_iff, decisionLiteral_view] at last
      exact last
  · rintro ⟨old, phase⟩ i hi
    have before : i < s.assigned + 1 := hi
    by_cases last : i = s.assigned
    · subst i
      rw [decide_trail_last space, falsifies_negate_iff, decisionLiteral_view]
      exact phase
    · have earlier : i < s.assigned := by omega
      simpa only [decide_trail_prefix earlier] using old i earlier

/-- Writing a decision reason yields zero even if the slot is out of bounds:
the logical total array access then has its zero default. Reachable states
separately establish all executable accesses are within their allocated arrays. -/
theorem decide_reason_at_decision (s : State) (var : Nat) :
    (s.decide var).reason (decisionLiteral s var).negate = 0 := by
  change (s.reasons.set! var 0)[(decisionLiteral s var).negate.var]! = 0
  rw [negate_var, decisionLiteral_var]
  by_cases bound : var < s.reasons.size
  · exact Array.getElem!_set!_self s.reasons var 0 bound
  · simp [Array.setIfInBounds, bound]

/-- Existing propagated entries retain their semantic dependencies. The newly
appended entry is a decision, so it introduces no new reason obligation. -/
theorem reasonConsequences_decide {s : State} {formula : CNF Nat} {var : Nat}
    (reasons : ReasonConsequences formula s) (fresh : FreshVariable s var)
    (space : s.assigned < s.trail.size) :
    ReasonConsequences formula (s.decide var) := by
  intro i before nondecision a model compatible
  have before' : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [decide_trail_last space, decide_reason_at_decision] at nondecision
    exact False.elim (nondecision rfl)
  · have old : i < s.assigned := by omega
    have reasonFrame : (s.decide var).reason s.trail[i]! = s.reason s.trail[i]! := by
      exact Array.getElem!_set!_ne s.reasons _ _ _ (Ne.symm (fresh i old))
    have oldReason : s.reason s.trail[i]! ≠ 0 := by
      simpa only [decide_trail_prefix old, reasonFrame] using nondecision
    have oldCompatible := (prefixCompatible_decide_iff (Nat.le_of_lt old)).mp compatible
    simpa only [decide_trail_prefix old] using reasons i old oldReason a model oldCompatible

/-- The actual bounded decision scan supplies the freshness needed above. -/
theorem nextDecision_fresh {s : State} {cursor : Nat}
    (active : ActiveTrail s) (nonzero : nextDecision s cursor ≠ 0) :
    FreshVariable s (nextDecision s cursor) := by
  have unmarked := nextDecisionScan_nonzero_unassigned (s.nVars + 1) s cursor nonzero
  exact freshVariable_of_unmarked active unmarked.1 unmarked.2

theorem reasonConsequences_decide_nextDecision {s : State} {formula : CNF Nat} {cursor : Nat}
    (reasons : ReasonConsequences formula s) (active : ActiveTrail s)
    (nonzero : nextDecision s cursor ≠ 0) (space : s.assigned < s.trail.size) :
    ReasonConsequences formula (s.decide (nextDecision s cursor)) :=
  reasonConsequences_decide reasons (nextDecision_fresh active nonzero) space

end MicrosatLean.Verification.Implementation.Native.Search
