import MicrosatLean.Verification.Implementation.Native.Propagation.Closure
import MicrosatLean.Verification.Implementation.Native.Propagation.Replacement

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation
open Std.Sat

/-- Trail coverage lets a mark-based unit test speak about every model that
agrees with the current decision assumptions, rather than only saved phases. -/
theorem marked_falsifies_of_trail {s : State} {a : Nat → Bool}
    (coverage : MarkedOnTrail s) (compatible : TrailCompatible s a)
    {lit : Lit} (marked : s.mark lit ≠ 0) : Falsifies a lit := by
  obtain ⟨i, before, equal⟩ := coverage lit marked
  simpa only [equal] using compatible i before

/-- A unit clause entailed by the input forces its head under the current
trail assumptions. The concrete watch scan must supply `unit`. -/
theorem head_true_of_unit {s : State} {formula : Std.Sat.CNF Nat} {lits : Array Lit} {head : Lit}
    (entailed : CNF.EntailsClause formula (clauseView lits))
    (coverage : MarkedOnTrail s)
    (unit : ∀ lit ∈ lits, lit ≠ head → s.mark lit ≠ 0)
    {a : Nat → Bool} (model : CNF.Sat a formula) (compatible : TrailCompatible s a) :
    a (literalView head).1 = (literalView head).2 := by
  apply Logic.forced_of_sat (entailed a model)
  intro viewed member different
  obtain ⟨lit, hlit, equal⟩ := clauseView_mem.mp member
  have ne : lit ≠ head := by
    intro same
    exact different (equal.symm.trans (congrArg literalView same))
  have falseLit := marked_falsifies_of_trail coverage compatible (unit lit hlit ne)
  simpa only [Falsifies, equal] using falseLit

theorem trailCompatible_assign_of_unit {s : State} {formula : Std.Sat.CNF Nat}
    {lits : Array Lit} {clauseId : Nat} {root : Bool}
    (entailed : CNF.EntailsClause formula (clauseView lits))
    (coverage : MarkedOnTrail s)
    (unit : ∀ lit ∈ lits, lit ≠ s.db clauseId → s.mark lit ≠ 0)
    (space : s.assigned < s.trail.size)
    {a : Nat → Bool} (model : CNF.Sat a formula) (compatible : TrailCompatible s a) :
    TrailCompatible (s.assign clauseId root) a :=
  (trailCompatible_assign_iff space).mpr
    ⟨compatible, head_true_of_unit entailed coverage unit model compatible⟩

theorem prefixCompatible_assign_iff {s : State} {a : Nat → Bool}
    {clauseId count : Nat} {root : Bool} (before : count ≤ s.assigned) :
    PrefixCompatible (s.assign clauseId root) a count ↔ PrefixCompatible s a count := by
  constructor <;> intro h i hi
  · have old : i < s.assigned := Nat.lt_of_lt_of_le hi before
    simpa only [assign_trail_prefix old] using h i hi
  · have old : i < s.assigned := Nat.lt_of_lt_of_le hi before
    simpa only [assign_trail_prefix old] using h i hi

/-- A failed concrete replacement scan and a false second watch establish the
unit premise used by propagation. The packed clause ties that premise to the
actual arena head read by `State.assign`. -/
theorem unit_of_replacement_none {s : State} {lits : Array Lit} {clauseId : Nat}
    (packed : PackedClause s clauseId lits)
    (missing : replacement s.arena s.marks clauseId = none)
    (secondFalse : s.mark lits[1]! ≠ 0) :
    ∀ lit ∈ lits, lit ≠ s.db clauseId → s.mark lit ≠ 0 := by
  intro lit member different
  obtain ⟨i, hi, value⟩ := Array.mem_iff_getElem.mp member
  have equal : lits[i]! = lit := by simpa only [getElem!_pos lits i hi] using value
  by_cases first : i = 0
  · subst i
    have head := packed.literals 0 (by omega)
    simp only [Nat.add_zero] at head
    exact False.elim (different (equal.symm.trans head.symm))
  · by_cases second : i = 1
    · subst i
      simpa only [equal] using secondFalse
    · simpa only [equal] using replacement_none_of_packed packed missing (by omega : 2 ≤ i) hi

/-- Actual assignment following a failed replacement scan preserves every
input model compatible with the old trail. -/
theorem trailCompatible_assign_of_replacement_none {s : State} {formula : Std.Sat.CNF Nat}
    {lits : Array Lit} {clauseId : Nat} {root : Bool}
    (packed : PackedClause s clauseId lits)
    (entailed : CNF.EntailsClause formula (clauseView lits))
    (coverage : MarkedOnTrail s) (missing : replacement s.arena s.marks clauseId = none)
    (secondFalse : s.mark lits[1]! ≠ 0) (space : s.assigned < s.trail.size)
    {a : Nat → Bool} (model : CNF.Sat a formula) (compatible : TrailCompatible s a) :
    TrailCompatible (s.assign clauseId root) a :=
  trailCompatible_assign_of_unit entailed coverage
    (unit_of_replacement_none packed missing secondFalse) space model compatible

/-- Actual unit assignment extends the semantic reason invariant. Freshness
protects earlier reason entries; propagation supplies the new dependency. -/
theorem reasonConsequences_assign {s : State} {formula : Std.Sat.CNF Nat} {lits : Array Lit}
    {clauseId : Nat} {root : Bool} (reasons : ReasonConsequences formula s)
    (entailed : CNF.EntailsClause formula (clauseView lits))
    (coverage : MarkedOnTrail s)
    (unit : ∀ lit ∈ lits, lit ≠ s.db clauseId → s.mark lit ≠ 0)
    (fresh : FreshVariable s (Lit.var (s.db clauseId))) (space : s.assigned < s.trail.size) :
    ReasonConsequences formula (s.assign clauseId root) := by
  intro i before nondecision a model compatible
  have before' : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [assign_trail_last space]
    apply (falsifies_negate_iff a _).mpr
    apply head_true_of_unit entailed coverage unit model
    exact (prefixCompatible_assign_iff (Nat.le_refl _)).mp compatible
  · have old : i < s.assigned := by omega
    have reasonFrame : (s.assign clauseId root).reason s.trail[i]! = s.reason s.trail[i]! := by
      exact Array.getElem!_set!_ne s.reasons _ _ _ (Ne.symm (fresh i old))
    have oldReason : s.reason s.trail[i]! ≠ 0 := by
      simpa only [assign_trail_prefix old, reasonFrame] using nondecision
    have oldCompatible := (prefixCompatible_assign_iff (Nat.le_of_lt old)).mp compatible
    simpa only [assign_trail_prefix old] using reasons i old oldReason a model oldCompatible

end MicrosatLean.Verification.Implementation.Native.Propagation
