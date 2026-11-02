import MicrosatLean.Verification.Implementation.Bridge.Assignment

namespace MicrosatLean.Verification.Implementation.Bridge

/-- Appending a clause cannot change an already owned reason lookup. -/
theorem reasonView_append {s : CDCL.State} {entries : List StoredClause}
    (proper : Representation.ReasonDatabase s entries) (extra : List StoredClause)
    {i : Nat} (before : i < s.assigned) :
    reasonView s (entries ++ extra) i = reasonView s entries i := by
  by_cases zero : s.reason s.trail[i]! = 0
  · simp only [reasonView, zero, ↓reduceIte]
  · obtain ⟨old, member, same⟩ := proper i before zero
    simp only [reasonView, zero, ↓reduceIte, List.find?_append]
    cases selected : entries.find? (fun entry => entry.id == s.reason s.trail[i]!) with
    | none =>
      have absent := (List.find?_eq_none.mp selected) old member
      exact False.elim (absent (by simp only [same, beq_self_eq_true]))
    | some entry => rfl

theorem trailView_append_entries {s : CDCL.State} {entries : List StoredClause}
    (proper : Representation.ReasonDatabase s entries) (extra : List StoredClause) :
    trailView s (entries ++ extra) = trailView s entries := by
  apply List.ext_getElem
  · simp only [trailView_length]
  · intro i left right
    have before : i < s.assigned := by simpa only [trailView_length] using left
    have first := trailView_get s (entries ++ extra) before
    have second := trailView_get s entries before
    rw [getElem!_pos _ i left] at first
    rw [getElem!_pos _ i right] at second
    rw [first, second, reasonView_append proper extra before]

theorem logicalView_learn {s : CDCL.State} {original learned : List StoredClause}
    (proper : Representation.ReasonDatabase s (original ++ learned)) (added : StoredClause) :
    logicalView s original (learned ++ [added]) =
      { logicalView s original learned with learned :=
          (logicalView s original learned).learned ++ [added.view] } := by
  have unchanged := trailView_append_entries proper [added]
  simp only [List.append_assoc] at unchanged
  simp only [logicalView, List.map_append, List.map_cons, List.map_nil]
  rw [unchanged]

theorem logicalView_analyze_prefix {input : CNF} {s : CDCL.State}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (_base : Search.Concrete.StateCertificate input s original learned heads rank)
    (entry : Analysis.AnalysisTransitionEntry input s conflict lits rank decision) :
    let added : StoredClause := ⟨(CDCL.analyze s conflict).2, Analysis.analysisLearned s conflict⟩
    logicalView (CDCL.analyze s conflict).1 original (learned ++ [added]) =
      { logicalView s original (learned ++ [added]) with
        trail := (logicalView s original (learned ++ [added])).trail.take
          (CDCL.analyze s conflict).1.assigned } := by
  dsimp only
  have truncated := trailView_prefix_of_get
    (before := s) (after := (CDCL.analyze s conflict).1)
    (entries := original ++ (learned ++ [⟨(CDCL.analyze s conflict).2,
      Analysis.analysisLearned s conflict⟩]))
    (nextEntries := original ++ (learned ++ [⟨(CDCL.analyze s conflict).2,
      Analysis.analysisLearned s conflict⟩]))
    (Nat.le_of_lt (Analysis.analyze_assigned_lt entry.decisionEntry))
    (by
      intro i before
      constructor
      · rw [Analysis.analyze_trail]
      · apply reasonView_eq_of_code
        simp only [CDCL.State.reason, Analysis.analyze_trail,
          Analysis.analyze_reasons])
  simp only [logicalView, Search.Concrete.analyze_nVars, Analysis.analyze_forced]
  rw [truncated]

theorem logicalView_false_iff (s : CDCL.State) (original learned : List StoredClause) (lit : Lit) :
    FalseIn (logicalView s original learned).trueTrail (literalView lit) ↔
      Analysis.TrailMember s s.assigned lit := by
  change (literalView lit).negate ∈
    ((List.range s.assigned).map fun i =>
      (⟨(literalView s.trail[i]!).negate, reasonView s (original ++ learned) i⟩ : TrailEntry)).map
        TrailEntry.literal ↔ ∃ i, i < s.assigned ∧ s.trail[i]! = lit
  simp only [List.map_map, Function.comp_def, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, before, same⟩
    refine ⟨i, before, literalView_injective ?_⟩
    simpa only [Std.Sat.Literal.negate, Bool.not_not] using congrArg Std.Sat.Literal.negate same
  · rintro ⟨i, before, same⟩
    exact ⟨i, before, by rw [same]⟩

theorem logicalView_fresh {s : CDCL.State} {original learned : List StoredClause} {lit : Lit}
    (fresh : Representation.FreshVariable s lit.var) :
    Unassigned (logicalView s original learned).trueTrail (literalView lit).1 := by
  intro other member
  change other ∈
    ((List.range s.assigned).map fun i =>
      (⟨(literalView s.trail[i]!).negate, reasonView s (original ++ learned) i⟩ : TrailEntry)).map
        TrailEntry.literal at member
  simp only [List.map_map, Function.comp_def, List.mem_map, List.mem_range] at member
  obtain ⟨i, before, rfl⟩ := member
  exact fresh i before

end MicrosatLean.Verification.Implementation.Bridge
