import MicrosatLean.Verification.Implementation.Bridge.Assignment
import MicrosatLean.Verification.Implementation.Native.Search.AnalysisState

namespace MicrosatLean.Verification.Implementation.Bridge

private abbrev NativeEntry := Native.Representation.StoredClause

/-- Appending a clause cannot change an already owned reason lookup. -/
theorem nativeReason_append {s : CDCL.State} {entries : List NativeEntry}
    (proper : Native.Representation.ReasonDatabase s entries) (extra : List NativeEntry)
    {i : Nat} (before : i < s.assigned) :
    nativeReason s (entries ++ extra) i = nativeReason s entries i := by
  by_cases zero : s.reason s.trail[i]! = 0
  · simp only [nativeReason, zero, ↓reduceIte]
  · obtain ⟨old, member, same⟩ := proper i before zero
    simp only [nativeReason, zero, ↓reduceIte, List.find?_append]
    cases selected : entries.find? (fun entry => entry.id == s.reason s.trail[i]!) with
    | none =>
      have absent := (List.find?_eq_none.mp selected) old member
      exact False.elim (absent (by simp only [same, beq_self_eq_true]))
    | some entry => rfl

theorem nativeTrail_append_entries {s : CDCL.State} {entries : List NativeEntry}
    (proper : Native.Representation.ReasonDatabase s entries) (extra : List NativeEntry) :
    nativeTrail s (entries ++ extra) = nativeTrail s entries := by
  apply List.ext_getElem
  · simp only [nativeTrail_length]
  · intro i left right
    have before : i < s.assigned := by simpa only [nativeTrail_length] using left
    have first := nativeTrail_get s (entries ++ extra) before
    have second := nativeTrail_get s entries before
    rw [getElem!_pos _ i left] at first
    rw [getElem!_pos _ i right] at second
    rw [first, second, nativeReason_append proper extra before]

theorem nativeState_learn {s : CDCL.State} {original learned : List NativeEntry}
    (proper : Native.Representation.ReasonDatabase s (original ++ learned)) (added : NativeEntry) :
    nativeState s original (learned ++ [added]) =
      { nativeState s original learned with learned :=
          (nativeState s original learned).learned ++ [added.view] } := by
  have unchanged := nativeTrail_append_entries proper [added]
  simp only [List.append_assoc] at unchanged
  simp only [nativeState, List.map_append, List.map_cons, List.map_nil]
  rw [unchanged]

theorem nativeState_analyze_prefix {input : CNF} {s : CDCL.State}
    {original learned : List NativeEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (_base : Native.Search.StateCertificate input s original learned heads rank)
    (entry : Native.Analysis.AnalysisTransitionEntry input s conflict lits rank decision) :
    let added : NativeEntry := ⟨(CDCL.analyze s conflict).2, Native.Analysis.analysisLearned s conflict⟩
    nativeState (CDCL.analyze s conflict).1 original (learned ++ [added]) =
      { nativeState s original (learned ++ [added]) with
        trail := (nativeState s original (learned ++ [added])).trail.take
          (CDCL.analyze s conflict).1.assigned } := by
  dsimp only
  have truncated := nativeTrail_prefix_of_get
    (before := s) (after := (CDCL.analyze s conflict).1)
    (entries := original ++ (learned ++ [⟨(CDCL.analyze s conflict).2,
      Native.Analysis.analysisLearned s conflict⟩]))
    (nextEntries := original ++ (learned ++ [⟨(CDCL.analyze s conflict).2,
      Native.Analysis.analysisLearned s conflict⟩]))
    (Nat.le_of_lt (Native.Analysis.analyze_assigned_lt entry.decisionEntry))
    (by
      intro i before
      constructor
      · rw [Native.Analysis.analyze_trail]
      · apply nativeReason_eq_of_code
        simp only [CDCL.State.reason, Native.Analysis.analyze_trail,
          Native.Analysis.analyze_reasons])
  simp only [nativeState, Native.Search.analyze_nVars, Native.Analysis.analyze_forced]
  rw [truncated]

theorem nativeState_false_iff (s : CDCL.State) (original learned : List NativeEntry) (lit : Lit) :
    FalseIn (nativeState s original learned).trueTrail (literalView lit) ↔
      Native.Analysis.TrailMember s s.assigned lit := by
  change (literalView lit).negate ∈
    ((List.range s.assigned).map fun i =>
      (⟨(literalView s.trail[i]!).negate, nativeReason s (original ++ learned) i⟩ : TrailEntry)).map
        TrailEntry.literal ↔ ∃ i, i < s.assigned ∧ s.trail[i]! = lit
  simp only [List.map_map, Function.comp_def, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, before, same⟩
    refine ⟨i, before, view_injective ?_⟩
    simpa only [Std.Sat.Literal.negate, Bool.not_not] using congrArg Std.Sat.Literal.negate same
  · rintro ⟨i, before, same⟩
    exact ⟨i, before, by rw [same]⟩

theorem nativeState_fresh {s : CDCL.State} {original learned : List NativeEntry} {lit : Lit}
    (fresh : Native.Representation.FreshVariable s lit.var) :
    Unassigned (nativeState s original learned).trueTrail (literalView lit).1 := by
  intro other member
  change other ∈
    ((List.range s.assigned).map fun i =>
      (⟨(literalView s.trail[i]!).negate, nativeReason s (original ++ learned) i⟩ : TrailEntry)).map
        TrailEntry.literal at member
  simp only [List.map_map, Function.comp_def, List.mem_map, List.mem_range] at member
  obtain ⟨i, before, rfl⟩ := member
  exact fresh i before

end MicrosatLean.Verification.Implementation.Bridge
