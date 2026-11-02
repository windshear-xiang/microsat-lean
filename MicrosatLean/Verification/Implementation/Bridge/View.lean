import MicrosatLean.Verification.Implementation.Bridge.Representation

namespace MicrosatLean.Verification.Implementation.Bridge

def representationWitness (original learned : List StoredClause) (heads : Lit → List Nat)
    (order : List Nat) : RepresentationWitness :=
  ⟨original, learned, heads, order⟩

def reasonView (s : CDCL.State) (entries : List StoredClause) (i : Nat) : Option Clause :=
  if s.reason s.trail[i]! = 0 then none
  else (entries.find? (fun entry => entry.id == s.reason s.trail[i]!)).map Representation.StoredClause.view

def trailView (s : CDCL.State) (entries : List StoredClause) : List TrailEntry :=
  (List.range s.assigned).map fun i => ⟨(literalView s.trail[i]!).negate, reasonView s entries i⟩

def logicalView (s : CDCL.State) (original learned : List StoredClause) : LogicalState :=
  ⟨s.nVars, original.map Representation.StoredClause.view,
    learned.map Representation.StoredClause.view,
    trailView s (original ++ learned), s.forced⟩

@[simp] theorem trailView_length (s : CDCL.State) (entries : List StoredClause) :
    (trailView s entries).length = s.assigned := by simp [trailView]

theorem trailView_get (s : CDCL.State) (entries : List StoredClause) {i : Nat}
    (before : i < s.assigned) :
    (trailView s entries)[i]! =
      ⟨(literalView s.trail[i]!).negate, reasonView s entries i⟩ := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using before)]
  simp [trailView]

theorem reasonView_some {s : CDCL.State} {entries : List StoredClause}
    (proper : Representation.ReasonDatabase s entries) {i : Nat}
    (before : i < s.assigned) (nonzero : s.reason s.trail[i]! ≠ 0) :
    ∃ entry ∈ entries, s.reason s.trail[i]! = entry.id ∧
      reasonView s entries i = some entry.view := by
  obtain ⟨old, member, id⟩ := proper i before nonzero
  cases found : entries.find? (fun entry => entry.id == s.reason s.trail[i]!) with
  | none =>
    have absent := (List.find?_eq_none.mp found) old member
    exact False.elim (absent (by simp only [id, beq_self_eq_true]))
  | some entry =>
    have selected : entry.id = s.reason s.trail[i]! := by
      simpa only [beq_iff_eq] using List.find?_some found
    exact ⟨entry, List.mem_of_find?_eq_some found, selected.symm,
      by simp only [reasonView, nonzero, ↓reduceIte, found, Option.map_some]⟩

theorem reasonView_none_iff {s : CDCL.State} {entries : List StoredClause}
    (proper : Representation.ReasonDatabase s entries) {i : Nat}
    (before : i < s.assigned) :
    reasonView s entries i = none ↔ s.reason s.trail[i]! = 0 := by
  constructor
  · intro absent
    by_cases zero : s.reason s.trail[i]! = 0
    · exact zero
    · obtain ⟨entry, _, _, selected⟩ := reasonView_some proper before zero
      rw [absent] at selected
      cases selected
  · intro zero
    simp only [reasonView, zero, ↓reduceIte]

theorem view_rep {input : CNF} {m : CDCL.Machine}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate input m.solver original learned heads rank)
    {order : List Nat} (ordered : Representation.MTFOrder m.solver order) :
    Rep m (logicalView m.solver original learned) (representationWitness original learned heads order) := by
  let s := m.solver
  let entries := original ++ learned
  have members : (representationWitness original learned heads order).entries = entries := by
    simp [representationWitness, RepresentationWitness.entries, entries]
  have size := base.database.layout.size
  refine ⟨rfl, ⟨base.arrays.firstSize, base.arrays.marksSize, base.arrays.reasonsSize,
    base.arrays.phasesSize, base.arrays.trailSize, base.arrays.previousSize, base.arrays.nextSize⟩,
    by omega, ?_, ?_, by simpa [representationWitness] using base.database.learnedCount,
    rfl,
    rfl,
    trailView_length _ _, rfl,
    ⟨base.bounds.forcedProcessed, base.bounds.processedAssigned, base.bounds.assignedVars⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [members]
    exact base.database.layout
  · simpa only [representationWitness, List.map_map, Function.comp_def]
      using base.database.fixed
  · intro i before
    exact congrArg TrailEntry.literal (trailView_get _ _ before)
  · intro i before
    exact (base.active i before).2
  · intro lit
    constructor
    · exact base.marked lit
    · rintro ⟨i, before, rfl⟩
      exact (base.active i before).2.1
  · intro i before
    have bounded : i < s.assigned := by simpa only [logicalView, trailView_length] using before
    change s.phases[(trailView s entries)[i]!.literal.1]! = (trailView s entries)[i]!.literal.2
    rw [trailView_get _ _ bounded]
    have phase := base.phases i bounded
    change s.phases[s.trail[i]!.var]! = (s.trail[i]! % 2 == 1) at phase
    rcases Nat.mod_two_eq_zero_or_one s.trail[i]! with even | odd
    · simpa [literalView, Std.Sat.Literal.negate, even] using phase
    · simpa [literalView, Std.Sat.Literal.negate, odd] using phase
  · intro i before
    change match (trailView s entries)[i]!.reason with
      | none => s.reason s.trail[i]! = 0
      | some clause => ∃ entry ∈ (representationWitness original learned heads order).entries,
          entry.id = s.reason s.trail[i]! ∧ entry.view = clause
    rw [trailView_get _ _ before]
    by_cases zero : s.reason s.trail[i]! = 0
    · have absent : reasonView s entries i = none := by simp only [reasonView, zero, ↓reduceIte]
      change match reasonView s entries i with
        | none => s.reason s.trail[i]! = 0
        | some clause => ∃ entry ∈ (representationWitness original learned heads order).entries,
            entry.id = s.reason s.trail[i]! ∧ entry.view = clause
      rw [absent]
      exact zero
    · obtain ⟨entry, member, id, selected⟩ := reasonView_some base.reasons before zero
      rw [selected]
      exact ⟨entry, by rw [members]; exact member,
        id.symm, rfl⟩
  · simpa only [WatchRepresentation, representationWitness, RepresentationWitness.entries,
      List.map_id] using base.watches
  · exact ordered

end MicrosatLean.Verification.Implementation.Bridge
