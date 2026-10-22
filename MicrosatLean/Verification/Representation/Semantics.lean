import MicrosatLean.Verification.Specification
import MicrosatLean.Verification.Representation.State
import MicrosatLean.Verification.Logic.Resolution

namespace MicrosatLean.Verification.Representation

open CDCL
open Std.Sat

/-- The trail stores falsified literals, rather than the true signed decisions. -/
def Falsifies (a : Nat → Bool) (lit : Lit) : Prop :=
  a (literalView lit).1 ≠ (literalView lit).2

@[simp] theorem falsifies_negate_iff (a : Nat → Bool) (lit : Lit) :
    Falsifies a lit.negate ↔ a (literalView lit).1 = (literalView lit).2 := by
  simp only [Falsifies, literalView_negate, Literal.negate]
  cases a (literalView lit).1 <;> cases (literalView lit).2 <;> decide

/-- Agreement with a trail prefix records decision assumptions as well as
propagations. It makes no unconditional entailment claim about decisions. -/
def PrefixCompatible (s : State) (a : Nat → Bool) (count : Nat) : Prop :=
  ∀ i, i < count → Falsifies a s.trail[i]!

def TrailCompatible (s : State) (a : Nat → Bool) : Prop :=
  PrefixCompatible s a s.assigned

theorem PrefixCompatible.mono {s : State} {a : Nat → Bool} {short long : Nat}
    (h : PrefixCompatible s a long) (hle : short ≤ long) : PrefixCompatible s a short :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hle)

@[simp] theorem prefixCompatible_zero (s : State) (a : Nat → Bool) :
    PrefixCompatible s a 0 := by
  intro i hi
  omega

@[simp] theorem prefixCompatible_setMark (s : State) (a : Nat → Bool)
    (lit value count : Nat) :
    PrefixCompatible (s.setMark lit value) a count ↔ PrefixCompatible s a count := Iff.rfl

@[simp] theorem prefixCompatible_unassign (s : State) (a : Nat → Bool)
    (lit count : Nat) :
    PrefixCompatible (s.unassign lit) a count ↔ PrefixCompatible s a count := Iff.rfl

/-- The concrete assignment update extends precisely the old trail assumptions
with the true head of its reason clause. -/
theorem trailCompatible_assign_iff {s : State} {a : Nat → Bool}
    {clauseId : Nat} {root : Bool} (space : s.assigned < s.trail.size) :
    TrailCompatible (s.assign clauseId root) a ↔
      TrailCompatible s a ∧
        a (literalView (s.db clauseId)).1 = (literalView (s.db clauseId)).2 := by
  constructor
  · intro h
    constructor
    · intro i hi
      have hh := h i (by simpa [State.assign] using Nat.lt_succ_of_lt hi)
      simpa only [assign_trail_prefix hi] using hh
    · have hh := h s.assigned (by simp [State.assign])
      rw [assign_trail_last space] at hh
      exact (falsifies_negate_iff a _).mp hh
  · rintro ⟨h, hhead⟩ i hi
    have hi' : i < s.assigned + 1 := by simpa [State.assign] using hi
    by_cases before : i < s.assigned
    · simpa only [assign_trail_prefix before] using h i before
    · have equal : i = s.assigned := by omega
      subst i
      rw [assign_trail_last space]
      exact (falsifies_negate_iff a _).mpr hhead

/-- Semantic reason dependencies: a propagated entry follows from the input
and the earlier trail assumptions. A decision is identified by reason zero. -/
def ReasonConsequences (formula : CNF Nat) (s : State) : Prop :=
  ∀ i, i < s.assigned → s.reason s.trail[i]! ≠ 0 →
    ∀ a, CNF.Sat a formula → PrefixCompatible s a i → Falsifies a s.trail[i]!

/-- Every entry in the forced prefix is a propagation, never a decision. -/
def RootReasons (s : State) : Prop :=
  ∀ i, i < s.forced → s.reason s.trail[i]! ≠ 0

/-- Root assignments hold in every model of the input. -/
def RootConsequences (formula : CNF Nat) (s : State) : Prop :=
  ∀ a, CNF.Sat a formula → PrefixCompatible s a s.forced

/-- Acyclic reason dependencies and the absence of root decisions justify all
root assignments. The induction follows the executable trail order. -/
theorem rootConsequences_of_reasons {formula : CNF Nat} {s : State}
    (bounds : s.forced ≤ s.assigned) (root : RootReasons s)
    (reasons : ReasonConsequences formula s) : RootConsequences formula s := by
  intro a ha i hi
  induction i using Nat.strongRecOn with
  | ind i ih =>
    apply reasons i (Nat.lt_of_lt_of_le hi bounds) (root i hi) a ha
    intro j hj
    exact ih j hj (Nat.lt_trans hj hi)

/-- An entailed reason whose non-head literals are falsified by earlier trail
assumptions supplies the corresponding reason dependency. -/
theorem reason_consequence_of_clause {formula : CNF Nat} {s : State} {i : Nat}
    {reason : CNF.Clause Nat}
    (entailed : CNF.EntailsClause formula reason)
    (tail : ∀ a, CNF.Sat a formula → PrefixCompatible s a i →
      ∀ lit ∈ reason, lit ≠ literalView s.trail[i]!.negate → a lit.1 ≠ lit.2) :
    ∀ a, CNF.Sat a formula → PrefixCompatible s a i → Falsifies a s.trail[i]! := by
  intro a ha hp
  have head := Logic.forced_of_sat (entailed a ha) (tail a ha hp)
  have hn := (falsifies_negate_iff a s.trail[i]!.negate).mpr head
  simpa only [negate_negate] using hn

/-- The root-conflict return rule once the watch scan supplies a clause whose
literals are false under the forced prefix. -/
theorem unsat_of_root_clause {formula : CNF Nat} {s : State}
    {conflict : CNF.Clause Nat} (root : RootConsequences formula s)
    (entailed : CNF.EntailsClause formula conflict)
    (falseAtRoot : ∀ a, PrefixCompatible s a s.forced →
      ∀ lit ∈ conflict, a lit.1 ≠ lit.2) : CNF.Unsat formula :=
  Logic.unsat_of_root_conflict entailed (fun a ha => falseAtRoot a (root a ha))

end MicrosatLean.Verification.Representation
