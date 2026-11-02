import MicrosatLean.Verification.Implementation.Search.ChooseState
import MicrosatLean.Verification.Transitions

namespace MicrosatLean.Verification.Implementation.Search

open Bridge
open Native.Representation Native.Reduction
private abbrev NEntry := Native.Representation.StoredClause

private theorem nativeReason_member {s : CDCL.State} {entries : List NEntry}
    {i : Nat} {clause : Clause} (reason : nativeReason s entries i = some clause) :
    clause ∈ entries.map Native.Representation.StoredClause.view := by
  unfold nativeReason at reason
  split at reason
  · cases reason
  · obtain ⟨entry, selected, equal⟩ := Option.map_eq_some_iff.mp reason
    exact List.mem_map.mpr ⟨entry, List.mem_of_find?_eq_some selected, equal⟩

theorem reduction_move {input : CNF} {s : CDCL.State}
    {original learned kept : List NEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    (k : Nat) (stored : Database (s.reduceDB k) original kept)
    (proper : ReasonDatabase (s.reduceDB k) (original ++ kept))
    (matching : RelocationMatches (compactionResult s k).2.1
      (retainedEntries s (lockedReasons s) k learned) kept)
    (relocated : ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept)) :
    LogicalMove input (nativeState s original learned) (nativeState (s.reduceDB k) original kept) := by
  rw [nativeState_reduction base k stored proper relocated]
  apply LogicalMove.forget
  · intro clause member
    change clause ∈ learned.map Native.Representation.StoredClause.view
    change clause ∈ kept.map Native.Representation.StoredClause.view at member
    rw [← matching.views] at member
    obtain ⟨entry, retainedMember, equal⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨entry, (List.mem_filter.mp retainedMember).1, equal⟩
  · intro entry member clause reason
    obtain ⟨i, bound, equal⟩ := List.mem_iff_getElem.mp member
    have active : i < s.assigned := by simpa only [nativeState, nativeTrail_length] using bound
    have get : (nativeState s original learned).trail[i]! = entry := by
      rw [getElem!_pos _ i bound]
      exact equal
    have oldReason : nativeReason s (original ++ learned) i = some clause := by
      rw [nativeState, nativeTrail_get _ _ active] at get
      simpa only [← get] using reason
    have afterReason : nativeReason (s.reduceDB k) (original ++ kept) i = some clause :=
      (nativeReason_reduction base k stored proper relocated active).trans oldReason
    simpa only [nativeState, List.map_append] using nativeReason_member afterReason

private theorem restart_count (s : CDCL.State) : s.restart.nLemmas = s.nLemmas := by
  simpa only using congrArg CDCL.State.nLemmas (restart_frame s).restore

private theorem restart_limit (s : CDCL.State) : s.restart.maxLemmas = s.maxLemmas := by
  simpa only using congrArg CDCL.State.maxLemmas (restart_frame s).restore

private theorem restart_config (s : CDCL.State) : s.restart.config = s.config := by
  simpa only using congrArg CDCL.State.config (restart_frame s).restore

/-- Choice preparation has precisely the restart and forgetting moves visible
in its executable branches; counter changes are logical stuttering. -/
theorem prepare_execution {input : CNF} {s : CDCL.State}
    {original learned : List NEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate input s original learned heads rank) (cursor old : Nat) :
    ∃ nextLearned nextHeads,
      Native.Search.StateCertificate input (Native.Search.prepareChoice s cursor old).1
        original nextLearned nextHeads rank ∧
      LogicalExecution input (nativeState s original learned)
        (nativeState (Native.Search.prepareChoice s cursor old).1 original nextLearned) := by
  by_cases learning : s.nLemmas > old
  · by_cases restart : s.fast > s.slow / 100 * 125
    · let reset := { s with res := 0, fast := s.slow / 100 * 125 }
      have resetCertificate : Native.Search.StateCertificate input reset original learned heads rank :=
        base.setRestartCounters 0 _
      have restarted : LogicalExecution input (nativeState s original learned)
          (nativeState reset.restart original learned) := by
        rw [nativeState_restart reset original learned resetCertificate.bounds]
        exact LogicalExecution.advance (.refl _) (LogicalMove.restart _)
      by_cases pressure : s.nLemmas > s.maxLemmas
      · obtain ⟨kept, nextHeads, next, matching, relocated⟩ :=
          resetCertificate.restart.reduceDB_with_relocation
            (Native.Search.restart_root resetCertificate.bounds) s.config.reductionK
        refine ⟨kept, nextHeads, ?_⟩
        simp only [Native.Search.prepareChoice, learning, restart, Id.run, pure,
          restart_count, restart_limit, restart_config, pressure, ↓reduceIte]
        exact ⟨next, LogicalExecution.advance restarted
          (reduction_move resetCertificate.restart s.config.reductionK next.database next.reasons matching relocated)⟩
      · refine ⟨learned, heads, ?_⟩
        simp only [Native.Search.prepareChoice, learning, restart, Id.run, pure,
          restart_count, restart_limit, pressure, ↓reduceIte]
        exact ⟨resetCertificate.restart, restarted⟩
    · simp only [Native.Search.prepareChoice, learning, restart, Id.run, pure, ↓reduceIte]
      exact ⟨learned, heads, base, .refl _⟩
  · rw [Native.Search.prepareChoice_no_learning s cursor old learning]
    exact ⟨learned, heads, base, .refl _⟩

end MicrosatLean.Verification.Implementation.Search
