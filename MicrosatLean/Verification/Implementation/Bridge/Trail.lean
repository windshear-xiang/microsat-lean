import MicrosatLean.Verification.Implementation.Bridge.View

namespace MicrosatLean.Verification.Implementation.Bridge

/-! Observation lemmas for the deterministic true-literal view of a trail. -/

theorem reasonView_eq_of_code {before after : CDCL.State}
    {entries : List Representation.StoredClause} {i j : Nat}
    (same : after.reason after.trail[j]! = before.reason before.trail[i]!) :
    reasonView after entries j = reasonView before entries i := by
  simp only [reasonView, same]

theorem trailView_append_of_get {before after : CDCL.State}
    {entries nextEntries : List Representation.StoredClause} (last : TrailEntry)
    (size : after.assigned = before.assigned + 1)
    (unchanged : ∀ i, i < before.assigned →
      (literalView after.trail[i]!).negate = (literalView before.trail[i]!).negate ∧
      reasonView after nextEntries i = reasonView before entries i)
    (lastLiteral : (literalView after.trail[before.assigned]!).negate = last.literal)
    (lastReason : reasonView after nextEntries before.assigned = last.reason) :
    trailView after nextEntries = trailView before entries ++ [last] := by
  have samePrefix :
      ((List.range before.assigned).map fun i =>
        (⟨(literalView after.trail[i]!).negate, reasonView after nextEntries i⟩ : TrailEntry)) =
      trailView before entries := by
    apply List.map_congr_left
    intro i member
    obtain ⟨literal, reason⟩ := unchanged i (List.mem_range.mp member)
    simp only [literal, reason]
  have sameLast :
      (⟨(literalView after.trail[before.assigned]!).negate,
        reasonView after nextEntries before.assigned⟩ : TrailEntry) = last := by
    cases last
    simp_all
  simp only [trailView, size, List.range_succ, List.map_append, List.map_singleton,
    samePrefix, sameLast]

theorem trailView_prefix_of_get {before after : CDCL.State}
    {entries nextEntries : List Representation.StoredClause}
    (size : after.assigned ≤ before.assigned)
    (unchanged : ∀ i, i < after.assigned →
      (literalView after.trail[i]!).negate = (literalView before.trail[i]!).negate ∧
      reasonView after nextEntries i = reasonView before entries i) :
    trailView after nextEntries = (trailView before entries).take after.assigned := by
  apply List.ext_getElem (by simp only [trailView_length, List.length_take, Nat.min_eq_left size])
  intro i leftBound rightBound
  have active : i < after.assigned := by simpa only [trailView_length] using leftBound
  have old : i < before.assigned := Nat.lt_of_lt_of_le active size
  have left := trailView_get after nextEntries active
  have right := trailView_get before entries old
  obtain ⟨literal, reason⟩ := unchanged i active
  have same : (trailView after nextEntries)[i]! = (trailView before entries)[i]! := by
    rw [left, right, literal, reason]
  simpa only [List.getElem_take, getElem!_pos (trailView after nextEntries) i leftBound,
    getElem!_pos (trailView before entries) i (by simpa only [trailView_length] using old)] using same

end MicrosatLean.Verification.Implementation.Bridge
