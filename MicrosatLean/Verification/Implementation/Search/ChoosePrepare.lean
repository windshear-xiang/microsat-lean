import MicrosatLean.Verification.Implementation.Search.ChooseState
import MicrosatLean.Verification.Transitions

namespace MicrosatLean.Verification.Implementation.Search

open Bridge
open Representation Reduction

private theorem reasonView_member {s : CDCL.State} {entries : List StoredClause}
    {i : Nat} {clause : Clause} (reason : reasonView s entries i = some clause) :
    clause ∈ entries.map Representation.StoredClause.view := by
  unfold reasonView at reason
  split at reason
  · cases reason
  · obtain ⟨entry, selected, equal⟩ := Option.map_eq_some_iff.mp reason
    exact List.mem_map.mpr ⟨entry, List.mem_of_find?_eq_some selected, equal⟩

theorem reduction_move {input : CNF} {s : CDCL.State}
    {original learned kept : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate input s original learned heads rank)
    (k : Nat) (stored : Database (s.reduceDB k) original kept)
    (proper : ReasonDatabase (s.reduceDB k) (original ++ kept))
    (matching : RelocationMatches (compactionResult s k).2.1
      (retainedEntries s (lockedReasons s) k learned) kept)
    (relocated : ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept)) :
    LogicalMove input (logicalView s original learned) (logicalView (s.reduceDB k) original kept) := by
  rw [logicalView_reduction base k stored proper relocated]
  apply LogicalMove.forget
  · intro clause member
    change clause ∈ learned.map Representation.StoredClause.view
    change clause ∈ kept.map Representation.StoredClause.view at member
    rw [← matching.views] at member
    obtain ⟨entry, retainedMember, equal⟩ := List.mem_map.mp member
    exact List.mem_map.mpr ⟨entry, (List.mem_filter.mp retainedMember).1, equal⟩
  · intro entry member clause reason
    obtain ⟨i, bound, equal⟩ := List.mem_iff_getElem.mp member
    have active : i < s.assigned := by simpa only [logicalView, trailView_length] using bound
    have get : (logicalView s original learned).trail[i]! = entry := by
      rw [getElem!_pos _ i bound]
      exact equal
    have oldReason : reasonView s (original ++ learned) i = some clause := by
      rw [logicalView, trailView_get _ _ active] at get
      simpa only [← get] using reason
    have afterReason : reasonView (s.reduceDB k) (original ++ kept) i = some clause :=
      (reasonView_reduction base k stored proper relocated active).trans oldReason
    simpa only [logicalView, List.map_append] using reasonView_member afterReason

private theorem restart_count (s : CDCL.State) : s.restart.nLemmas = s.nLemmas := by
  simpa only using congrArg CDCL.State.nLemmas (restart_frame s).restore

private theorem restart_limit (s : CDCL.State) : s.restart.maxLemmas = s.maxLemmas := by
  simpa only using congrArg CDCL.State.maxLemmas (restart_frame s).restore

private theorem restart_config (s : CDCL.State) : s.restart.config = s.config := by
  simpa only using congrArg CDCL.State.config (restart_frame s).restore

/-- Choice preparation has precisely the restart and forgetting moves visible
in its executable branches; counter changes are logical stuttering. -/
theorem prepare_execution {input : CNF} {s : CDCL.State}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate input s original learned heads rank) (cursor old : Nat) :
    ∃ nextLearned nextHeads,
      Search.Concrete.StateCertificate input (Search.Concrete.prepareChoice s cursor old).1
        original nextLearned nextHeads rank ∧
      LogicalExecution input (logicalView s original learned)
        (logicalView (Search.Concrete.prepareChoice s cursor old).1 original nextLearned) := by
  by_cases learning : s.nLemmas > old
  · by_cases restart : s.fast > s.slow / 100 * 125
    · let reset := { s with res := 0, fast := s.slow / 100 * 125 }
      have resetCertificate : Search.Concrete.StateCertificate input reset original learned heads rank :=
        base.setRestartCounters 0 _
      have restarted : LogicalExecution input (logicalView s original learned)
          (logicalView reset.restart original learned) := by
        rw [logicalView_restart reset original learned resetCertificate.bounds]
        exact LogicalExecution.advance (.refl _) (LogicalMove.restart _)
      by_cases pressure : s.nLemmas > s.maxLemmas
      · obtain ⟨kept, nextHeads, next, matching, relocated⟩ :=
          resetCertificate.restart.reduceDB_with_relocation
            (Search.Concrete.restart_root resetCertificate.bounds) s.config.reductionK
        refine ⟨kept, nextHeads, ?_⟩
        simp only [Search.Concrete.prepareChoice, learning, restart, Id.run, pure,
          restart_count, restart_limit, restart_config, pressure, ↓reduceIte]
        exact ⟨next, LogicalExecution.advance restarted
          (reduction_move resetCertificate.restart s.config.reductionK next.database next.reasons matching relocated)⟩
      · refine ⟨learned, heads, ?_⟩
        simp only [Search.Concrete.prepareChoice, learning, restart, Id.run, pure,
          restart_count, restart_limit, pressure, ↓reduceIte]
        exact ⟨resetCertificate.restart, restarted⟩
    · simp only [Search.Concrete.prepareChoice, learning, restart, Id.run, pure, ↓reduceIte]
      exact ⟨learned, heads, base, .refl _⟩
  · rw [Search.Concrete.prepareChoice_no_learning s cursor old learning]
    exact ⟨learned, heads, base, .refl _⟩

end MicrosatLean.Verification.Implementation.Search
