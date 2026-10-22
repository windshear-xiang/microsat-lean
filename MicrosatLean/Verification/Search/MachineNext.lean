import MicrosatLean.Verification.Search.MachineInvariant

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Std.Sat

theorem MachineCertificate.nextLiteral_pending {formula : Formula} {s : State} {decision old : Nat}
    {root : Bool} {lit previous : Nat} {original learned : List StoredClause}
    {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : MachineCertificate formula ⟨s, decision, .nextLiteral, old, root, lit, previous⟩
      original learned heads rank) (pending : s.processed < s.assigned) :
    MachineCertificate formula
      ⟨{ s with processed := s.processed + 1 }, decision, .watch, old, root, s.trail[s.processed]!, 0⟩
      original learned heads rank := by
  have phase := certificate.phase
  change NextMode s root ∧ lit = 0 ∧ previous = 0 ∧ SettledPrefix s (original ++ learned) heads s.processed at phase
  have mode := phase.1.pending certificate.base.bounds pending
  have afterMode : PropagationMode { s with processed := s.processed + 1 } root := by
    refine ⟨mode.roots, ?_⟩
    intro falseRoot
    have nonroot := mode.nonroot falseRoot
    exact ⟨nonroot.levels, nonroot.caches, nonroot.nonroot⟩
  refine ⟨certificate.base.processNext pending, certificate.variables,
    DecisionHistory.frame certificate.history rfl rfl rfl rfl,
    DecisionWatchHistory.frame certificate.saved rfl rfl rfl rfl, certificate.units, ?_, ?_, certificate.oldCount⟩
  · intro noLearning
    exact (certificate.cursor noLearning).setCursors (s.processed + 1) s.forced
  · refine ⟨afterMode, by dsimp; omega, ?_, ?_⟩
    · simp only [Nat.add_sub_cancel]
    · refine ⟨heads s.trail[s.processed]!, .head _ rfl, settledCursor_head _ _ _ _, ?_⟩
      simpa only [SettledPrefix, SettledWatch, FalseBefore, TrueBefore, Nat.add_sub_cancel] using phase.2.2.2

theorem MachineCertificate.nextLiteral_complete {formula : Formula} {s : State} {decision old : Nat}
    {root : Bool} {lit previous : Nat} {original learned : List StoredClause}
    {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : MachineCertificate formula ⟨s, decision, .nextLiteral, old, root, lit, previous⟩
      original learned heads rank) (complete : ¬s.processed < s.assigned) :
    MachineCertificate formula
      ⟨(if root then { s with forced := s.processed } else s), decision, .choose, old, root, 0, 0⟩
      original learned heads rank := by
  have phase := certificate.phase
  change NextMode s root ∧ lit = 0 ∧ previous = 0 ∧ SettledPrefix s (original ++ learned) heads s.processed at phase
  have bounds : TrailBounds s := certificate.base.bounds
  have quiet : s.processed = s.assigned := by have := bounds.processedAssigned; omega
  cases root with
  | false =>
    have levels : LevelCover s := by
      rcases phase.1.nonroot rfl with empty | nonroot
      · exact LevelCover.root (Nat.le_of_eq empty)
      · exact nonroot.levels
    have six : SixBefore s := by
      rcases phase.1.nonroot rfl with empty | nonroot
      · intro i before _
        omega
      · exact nonroot.caches
    refine ⟨certificate.base, certificate.variables, certificate.history, certificate.saved,
      certificate.units, certificate.cursor, ?_, certificate.oldCount⟩
    exact ⟨quiet, rfl, rfl, levels, six, phase.2.2.2⟩
  | true =>
    have rootTags : ∀ i, i < s.processed → s.mark s.trail[i]! = 6 := by
      intro i before
      exact phase.1.roots rfl i (by omega)
    have base := certificate.base.finishRootPropagation rootTags
    have history : DecisionHistory { s with forced := s.processed } (original ++ learned) := by
      apply DecisionHistory.truncate (after := { s with forced := s.processed }) certificate.history
        (Nat.le_refl _) bounds.forcedProcessed
      · exact fun _ _ => rfl
      · exact fun _ _ => rfl
    have saved : DecisionWatchHistory { s with forced := s.processed } (original ++ learned) heads := by
      apply DecisionWatchHistory.truncate (after := { s with forced := s.processed }) certificate.saved
        (Nat.le_refl _) bounds.forcedProcessed
      · exact fun _ _ => rfl
      · exact fun _ _ zero => zero
    have levels : LevelCover { s with forced := s.processed } := LevelCover.root (Nat.le_of_eq quiet.symm)
    have six : SixBefore { s with forced := s.processed } := by
      intro i before _
      change i < s.assigned at before
      change i < s.processed
      omega
    refine ⟨base, certificate.variables, history, saved, certificate.units, ?_, ?_, certificate.oldCount⟩
    · intro noLearning
      exact (certificate.cursor noLearning).setCursors s.processed s.processed
    · exact ⟨quiet, rfl, rfl, levels, six, phase.2.2.2⟩

theorem step_nextLiteral_invariant {formula : Formula} {machine : Machine}
    (invariant : MachineInvariant formula machine) (phase : machine.phase = .nextLiteral) :
    InvariantProgress formula (step machine) := by
  obtain ⟨original, learned, heads, rank, certificate⟩ := invariant
  rcases machine with ⟨s, decision, current, old, root, lit, previous⟩
  dsimp only at phase
  subst current
  by_cases pending : s.processed < s.assigned
  · simpa only [step, Id.run, pending, ite_true, pure, InvariantProgress] using
      (show MachineInvariant formula
        ⟨{ s with processed := s.processed + 1 }, decision, .watch, old, root, s.trail[s.processed]!, 0⟩ from
        ⟨original, learned, heads, rank, certificate.nextLiteral_pending pending⟩)
  · simpa only [step, Id.run, pending, ite_false, pure, InvariantProgress] using
      (show MachineInvariant formula
        ⟨(if root then { s with forced := s.processed } else s), decision, .choose, old, root, 0, 0⟩ from
        ⟨original, learned, heads, rank, certificate.nextLiteral_complete pending⟩)

end MicrosatLean.Verification.Search
