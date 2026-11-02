import MicrosatLean.Verification.Implementation.Bridge.FromNativeBase

namespace MicrosatLean.Verification.Implementation.Bridge

/-! Observation lemmas for the deterministic true-literal view of a trail. -/

theorem nativeReason_eq_of_code {before after : CDCL.State}
    {entries : List Native.Representation.StoredClause} {i j : Nat}
    (same : after.reason after.trail[j]! = before.reason before.trail[i]!) :
    nativeReason after entries j = nativeReason before entries i := by
  simp only [nativeReason, same]

theorem nativeTrail_append_of_get {before after : CDCL.State}
    {entries nextEntries : List Native.Representation.StoredClause} (last : TrailEntry)
    (size : after.assigned = before.assigned + 1)
    (unchanged : ∀ i, i < before.assigned →
      (literalView after.trail[i]!).negate = (literalView before.trail[i]!).negate ∧
      nativeReason after nextEntries i = nativeReason before entries i)
    (lastLiteral : (literalView after.trail[before.assigned]!).negate = last.literal)
    (lastReason : nativeReason after nextEntries before.assigned = last.reason) :
    nativeTrail after nextEntries = nativeTrail before entries ++ [last] := by
  have samePrefix :
      ((List.range before.assigned).map fun i =>
        (⟨(literalView after.trail[i]!).negate, nativeReason after nextEntries i⟩ : TrailEntry)) =
      nativeTrail before entries := by
    apply List.map_congr_left
    intro i member
    obtain ⟨literal, reason⟩ := unchanged i (List.mem_range.mp member)
    simp only [literal, reason]
  have sameLast :
      (⟨(literalView after.trail[before.assigned]!).negate,
        nativeReason after nextEntries before.assigned⟩ : TrailEntry) = last := by
    cases last
    simp_all
  simp only [nativeTrail, size, List.range_succ, List.map_append, List.map_singleton,
    samePrefix, sameLast]

theorem nativeTrail_prefix_of_get {before after : CDCL.State}
    {entries nextEntries : List Native.Representation.StoredClause}
    (size : after.assigned ≤ before.assigned)
    (unchanged : ∀ i, i < after.assigned →
      (literalView after.trail[i]!).negate = (literalView before.trail[i]!).negate ∧
      nativeReason after nextEntries i = nativeReason before entries i) :
    nativeTrail after nextEntries = (nativeTrail before entries).take after.assigned := by
  apply List.ext_getElem (by simp only [nativeTrail_length, List.length_take, Nat.min_eq_left size])
  intro i leftBound rightBound
  have active : i < after.assigned := by simpa only [nativeTrail_length] using leftBound
  have old : i < before.assigned := Nat.lt_of_lt_of_le active size
  have left := nativeTrail_get after nextEntries active
  have right := nativeTrail_get before entries old
  obtain ⟨literal, reason⟩ := unchanged i active
  have same : (nativeTrail after nextEntries)[i]! = (nativeTrail before entries)[i]! := by
    rw [left, right, literal, reason]
  simpa only [List.getElem_take, getElem!_pos (nativeTrail after nextEntries) i leftBound,
    getElem!_pos (nativeTrail before entries) i (by simpa only [nativeTrail_length] using old)] using same

end MicrosatLean.Verification.Implementation.Bridge
