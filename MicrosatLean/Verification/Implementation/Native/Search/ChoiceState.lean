import MicrosatLean.Verification.Implementation.Native.Search.ControlRank
import MicrosatLean.Verification.Implementation.Native.Search.RestartState

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation Propagation Analysis Reduction Std.Sat

/-- Saved decision closure also covers the root prefix. If a nonroot entry
exists, level cover forces an actual decision exactly at `forced`. -/
theorem DecisionHistory.rootClosed {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (levels : LevelCover s) (bounds : TrailBounds s)
    (closed : PropagationClosed s entries) :
    ∀ entry ∈ entries, PrefixUnitClosed s s.forced entry.lits := by
  by_cases nonroot : s.forced < s.assigned
  · obtain ⟨decision, lower, upper, reason⟩ := levels s.forced (Nat.le_refl _) nonroot
    have equal : decision = s.forced := by omega
    subst decision
    exact (history s.forced (Nat.le_refl _) nonroot reason).closed
  · have equal : s.forced = s.assigned := by
      have := bounds.forcedProcessed
      have := bounds.processedAssigned
      omega
    intro entry member
    rw [equal]
    exact closed entry member

theorem PropagationClosed.restart {s : State} {entries : List StoredClause}
    (closed : PropagationClosed s entries) (history : DecisionHistory s entries)
    (levels : LevelCover s) (bounds : TrailBounds s) :
    PropagationClosed s.restart entries := by
  intro entry member
  rw [restart_assigned bounds]
  exact ((DecisionHistory.rootClosed history levels bounds closed) entry member).transfer
    (fun i _ => by rw [restart_trail])

theorem PropagationClosed.reduceDB {s : State} {original learned kept : List StoredClause} {k : Nat}
    (closed : PropagationClosed s (original ++ learned))
    (matching : RelocationMatches (compactionResult s k).2.1
      (retainedEntries s (lockedReasons s) k learned) kept) :
    PropagationClosed (s.reduceDB k) (original ++ kept) := by
  intro entry member
  have source : ∃ prior ∈ original ++ learned, entry.lits = prior.lits := by
    rcases List.mem_append.mp member with old | retained
    · exact ⟨entry, List.mem_append_left _ old, rfl⟩
    · have wordMember : entry.lits ∈ kept.map StoredClause.lits := List.mem_map.mpr ⟨entry, retained, rfl⟩
      rw [← matching.literals] at wordMember
      obtain ⟨prior, priorMember, equal⟩ := List.mem_map.mp wordMember
      exact ⟨prior, List.mem_append_right original (List.mem_filter.mp priorMember).1, equal.symm⟩
  obtain ⟨prior, member, same⟩ := source
  rw [same, reduceDB_assigned]
  exact (closed prior member).transfer (fun i _ => by rw [reduceDB_trail])

end MicrosatLean.Verification.Implementation.Native.Analysis

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Reduction Std.Sat

theorem StateCertificate.setRestartCounters {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank) (res fast : Nat) :
    StateCertificate formula { s with res := res, fast := fast } original learned heads rank := by
  refine ⟨?_, ?_, certificate.active, certificate.distinct, certificate.phases, certificate.marked,
    certificate.order, certificate.database.frame rfl rfl rfl rfl, certificate.meaning,
    certificate.reasons, certificate.graph.frame rfl rfl rfl rfl,
    certificate.watches.frameArrays rfl rfl, certificate.nonempty, certificate.nodup,
    certificate.noClash, certificate.learnedDistinct, certificate.tags, certificate.roots,
    certificate.rootPrefix⟩
  · exact ⟨certificate.arrays.firstSize, certificate.arrays.marksSize, certificate.arrays.reasonsSize,
      certificate.arrays.phasesSize, certificate.arrays.trailSize, certificate.arrays.previousSize,
      certificate.arrays.nextSize⟩
  · exact ⟨certificate.bounds.forcedProcessed, certificate.bounds.processedAssigned,
      certificate.bounds.assignedVars⟩

private theorem restart_count (s : State) : s.restart.nLemmas = s.nLemmas := by
  simpa only using congrArg State.nLemmas (restart_frame s).restore

private theorem restart_limit (s : State) : s.restart.maxLemmas = s.maxLemmas := by
  simpa only using congrArg State.maxLemmas (restart_frame s).restore

private theorem restart_config (s : State) : s.restart.config = s.config := by
  simpa only using congrArg State.config (restart_frame s).restore

/-- Actual choice preparation preserves the base certificate, decision
history, level cover, root-tag placement, and unit closure. Restart closure
comes from the real saved root decision prefix; reduction uses exact retained
literal arrays. No propagation rerun or output closure is assumed. -/
theorem StateCertificate.prepareChoice {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned)) (levels : LevelCover s) (six : SixBefore s)
    (closed : PropagationClosed s (original ++ learned)) (cursor old : Nat) :
    ∃ nextLearned nextHeads,
      StateCertificate formula (prepareChoice s cursor old).1 original nextLearned nextHeads rank ∧
      DecisionHistory (prepareChoice s cursor old).1 (original ++ nextLearned) ∧
      LevelCover (prepareChoice s cursor old).1 ∧ SixBefore (prepareChoice s cursor old).1 ∧
      PropagationClosed (prepareChoice s cursor old).1 (original ++ nextLearned) := by
  by_cases learning : s.nLemmas > old
  · by_cases restart : s.fast > s.slow / 100 * 125
    · let reset := { s with res := 0, fast := s.slow / 100 * 125 }
      have resetCertificate : StateCertificate formula reset original learned heads rank :=
        certificate.setRestartCounters 0 _
      have resetClosed : PropagationClosed reset (original ++ learned) := closed
      have resetHistory : DecisionHistory reset (original ++ learned) := history
      have resetLevels : LevelCover reset := levels
      have rootClosed := PropagationClosed.restart resetClosed resetHistory resetLevels resetCertificate.bounds
      by_cases pressure : s.nLemmas > s.maxLemmas
      · obtain ⟨kept, nextHeads, next, matching, _⟩ := resetCertificate.restart.reduceDB_with_relocation
          (restart_root resetCertificate.bounds) s.config.reductionK
        refine ⟨kept, nextHeads, ?_⟩
        simp only [Search.prepareChoice, learning, restart, Id.run, pure, restart_count, restart_limit, restart_config,
          pressure, ↓reduceIte]
        exact ⟨next, reduceDB_decisionHistory (restart_root resetCertificate.bounds) _ _,
          reduceDB_levelCover (restart_root resetCertificate.bounds) _,
          reduceDB_sixBefore (restart_root resetCertificate.bounds) _, PropagationClosed.reduceDB rootClosed matching⟩
      · refine ⟨learned, heads, ?_⟩
        simp only [Search.prepareChoice, learning, restart, Id.run, pure, restart_count, restart_limit,
          pressure, ↓reduceIte]
        exact ⟨resetCertificate.restart, restart_decisionHistory resetCertificate.bounds _,
          restart_levelCover resetCertificate.bounds, restart_sixBefore resetCertificate.bounds, rootClosed⟩
    · simp only [Search.prepareChoice, learning, restart, Id.run, pure, ↓reduceIte]
      exact ⟨learned, heads, certificate, history, levels, six, closed⟩
  · rw [prepareChoice_no_learning s cursor old learning]
    exact ⟨learned, heads, certificate, history, levels, six, closed⟩

end MicrosatLean.Verification.Implementation.Native.Search
