import MicrosatLean.Verification.Implementation.Native.Representation.Assignment
import Init.Data.List.OfFn

namespace MicrosatLean.Verification.Implementation.Native.Representation

open CDCL

/-- The active variables, in trail order, independently of stale array cells. -/
def trailVariables (s : State) : List Nat :=
  List.ofFn fun i : Fin s.assigned => s.trail[i.val]!.var

@[simp] theorem trailVariables_length (s : State) : (trailVariables s).length = s.assigned := by
  simp [trailVariables]

theorem trailVariables_mem {s : State} {var : Nat} :
    var ∈ trailVariables s ↔ ∃ i, i < s.assigned ∧ s.trail[i]!.var = var := by
  simp only [trailVariables, List.mem_ofFn]
  constructor
  · rintro ⟨i, equal⟩
    exact ⟨i.val, i.isLt, equal⟩
  · rintro ⟨i, before, equal⟩
    exact ⟨⟨i, before⟩, equal⟩

theorem trailVariables_nodup {s : State} (distinct : DistinctTrailVariables s) :
    (trailVariables s).Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j hi hj same
  have beforeI : i < s.assigned := by simpa using hi
  have beforeJ : j < s.assigned := by simpa using hj
  apply distinct i j beforeI beforeJ
  simpa only [trailVariables, List.getElem_ofFn] using same

theorem trailVariables_subset {s : State} (active : ActiveTrail s) :
    trailVariables s ⊆ List.range' 1 s.nVars := by
  intro var member
  obtain ⟨i, before, equal⟩ := trailVariables_mem.mp member
  have bound := (active i before).1
  change 1 ≤ s.trail[i]!.var ∧ s.trail[i]!.var ≤ s.nVars at bound
  rw [equal] at bound
  apply List.mem_range'_1.mpr
  exact ⟨bound.1, by omega⟩

/-- A fresh declared variable witnesses unused trail capacity. This discharges
the assignment-space precondition from semantic representation invariants. -/
theorem assigned_lt_of_fresh {s : State} {var : Nat} (active : ActiveTrail s)
    (distinct : DistinctTrailVariables s) (fresh : FreshVariable s var)
    (lower : 1 ≤ var) (upper : var ≤ s.nVars) : s.assigned < s.nVars := by
  have absent : var ∉ trailVariables s := by
    intro member
    obtain ⟨i, before, equal⟩ := trailVariables_mem.mp member
    exact fresh i before equal
  have noDuplicates : (var :: trailVariables s).Nodup :=
    List.nodup_cons.mpr ⟨absent, trailVariables_nodup distinct⟩
  have included : var :: trailVariables s ⊆ List.range' 1 s.nVars := by
    intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact List.mem_range'_1.mpr ⟨lower, by omega⟩
    · exact trailVariables_subset active member
  have bound := noDuplicates.length_le_of_subset included
  simp only [List.length_cons, trailVariables_length, List.length_range'] at bound
  omega

theorem assignment_space_of_unmarked {s : State} {var : Nat}
    (arrays : ArrayBounds s) (active : ActiveTrail s) (distinct : DistinctTrailVariables s)
    (lower : 1 ≤ var) (upper : var ≤ s.nVars)
    (positive : s.mark (2 * var) = 0) (negative : s.mark (2 * var + 1) = 0) :
    s.assigned < s.trail.size := by
  have bound := assigned_lt_of_fresh active distinct
    (freshVariable_of_unmarked active positive negative) lower upper
  rw [arrays.trailSize]
  omega

end MicrosatLean.Verification.Implementation.Native.Representation
