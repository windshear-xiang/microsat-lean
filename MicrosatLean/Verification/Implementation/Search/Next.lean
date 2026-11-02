import MicrosatLean.Verification.Implementation.Search.NextFrame

namespace MicrosatLean.Verification.Implementation.Search

/-!
The next-literal phase either begins one exact watch list or commits completed
root propagation. No clause, mark, assignment or reason is changed here.
-/

theorem next_literal : PhaseCorrect .nextLiteral := by
  intro formula machine a w certificate phase
  rcases machine with ⟨s, decision, current, old, root, lit, previous⟩
  dsimp only at phase
  subst current
  have before := certificate.control.phase
  change NextMode _ a ∧ lit = 0 ∧ previous = 0 ∧ SettledPrefix a w s.processed at before
  have r := certificate.representation
  have bounds : s.forced ≤ s.processed ∧ s.processed ≤ s.assigned ∧ s.assigned ≤ s.nVars := r.cursors
  have assignedLength : a.trail.length = s.assigned := r.trailLength
  have rootForced : a.rootSize = s.forced := r.rootSize
  by_cases pending : s.processed < s.assigned
  · let after : CDCL.Machine := ⟨{ s with processed := s.processed + 1 }, decision,
      .watch, old, root, s.trail[s.processed]!, 0⟩
    have represented : Rep after a w :=
      rep_change_machine (rep_set_processed r (s.processed + 1)
        (by change s.forced ≤ s.processed + 1; omega)
        (by change s.processed + 1 ≤ s.assigned; omega)) after rfl
    have mode := next_mode_pending r before.1 pending
    have post : RunningPost formula a after := by
      refine ⟨a, w, represented, certificate.variables, .refl a, ?_, certificate.progress⟩
      refine ⟨certificate.control.history, certificate.control.saved, certificate.control.units,
        certificate.control.cursor, certificate.control.oldCount, certificate.control.tags,
        certificate.control.rootTags, certificate.control.rootPrefix, ?_⟩
      refine ⟨⟨mode.1, mode.2⟩, by simp [after], ?_, ?_⟩
      · simp [after]
      · refine ⟨w.heads s.trail[s.processed]!, Or.inl ⟨rfl, rfl⟩, ?_, ?_⟩
        · intro ref member absent
          exact False.elim (absent member)
        · simpa only [after, Nat.add_sub_cancel] using before.2.2.2
    simpa only [CDCL.step, Id.run, pure, pending, ↓reduceIte] using post
  · have complete : s.processed = s.assigned := by omega
    cases root with
    | false =>
      let after : CDCL.Machine := ⟨s, decision, .choose, old, false, 0, 0⟩
      have covered : LevelCover a := by
        rcases before.1.2 rfl with empty | active
        · intro i lower upper
          omega
        · exact active.2.1
      have six : SixBefore s := by
        rcases before.1.2 rfl with empty | active
        · rw [assignedLength, rootForced] at empty
          intro i active _
          change i < s.assigned at active
          change i < s.forced
          omega
        · exact active.2.2
      have post : RunningPost formula a after := by
        refine ⟨a, w, rep_change_machine r after rfl, certificate.variables, .refl a,
          ?_, certificate.progress⟩
        refine ⟨certificate.control.history, certificate.control.saved, certificate.control.units,
          certificate.control.cursor, certificate.control.oldCount, certificate.control.tags,
          certificate.control.rootTags, certificate.control.rootPrefix, ?_⟩
        exact ⟨complete, rfl, rfl, covered, six, before.2.2.2⟩
      simpa only [CDCL.step, Id.run, pure, pending, ↓reduceIte, Bool.false_eq_true] using post
    | true =>
      let next : LogicalState := { a with rootSize := s.processed }
      let after : CDCL.Machine := ⟨{ s with forced := s.processed }, decision, .choose, old, true, 0, 0⟩
      have length : a.trail.length = s.processed := r.trailLength.trans complete.symm
      have sound := root_commit_sound certificate before.1 rfl complete
      have represented : Rep after next w := rep_change_machine
        (rep_set_forced r s.processed (Nat.le_refl _)) after rfl
      have post : RunningPost formula a after := by
        refine ⟨next, w, represented, certificate.variables,
          .advance (.refl a) (.commitRoots a s.processed
            (by rw [rootForced]; exact bounds.1) (by omega) sound), ?_,
            ⟨certificate.progress.normalized, certificate.progress.distinctLearned⟩⟩
        refine ⟨?_, ?_, certificate.control.units, certificate.control.cursor,
          certificate.control.oldCount, certificate.control.tags, certificate.control.rootTags, ?_, ?_⟩
        · intro i lower upper
          change s.processed ≤ i at lower
          change i < a.trail.length at upper
          omega
        · intro i lower upper
          change s.processed ≤ i at lower
          change i < a.trail.length at upper
          omega
        · intro i bound
          exact before.1.1 rfl i (by
            change i < s.assigned
            change i < s.processed at bound
            omega)
        · refine ⟨complete, rfl, rfl, ?_, ?_, before.2.2.2⟩
          · intro i lower upper
            change s.processed ≤ i at lower
            change i < a.trail.length at upper
            omega
          · intro i active _
            change i < s.assigned at active
            change i < s.processed
            omega
      simpa only [CDCL.step, Id.run, pure, pending, ↓reduceIte] using post

end MicrosatLean.Verification.Implementation.Search
