import MicrosatLean.Verification.Implementation.Search.Concrete.ReductionState

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Analysis Reduction Std.Sat

/-- Restart keeps exactly the forced trail prefix. Its concrete clearing
loop preserves every root mark and clears every discarded active mark. -/
theorem StateCertificate.restart {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank) :
    StateCertificate formula s.restart original learned heads rank := by
  have forced := Nat.le_trans certificate.bounds.forcedProcessed certificate.bounds.processedAssigned
  have order : MTFCoverage s.restart := by
    obtain ⟨order, valid⟩ := certificate.order
    exact ⟨order, valid.frame restart_nVars restart_head restart_previous restart_next⟩
  refine ⟨certificate.arrays.restart, certificate.bounds.restart,
    certificate.active.restart certificate.bounds certificate.distinct,
    certificate.distinct.restart certificate.bounds, certificate.phases.restart certificate.bounds,
    certificate.marked.restart certificate.arrays certificate.bounds certificate.active,
    order, certificate.database.restart, certificate.meaning,
    certificate.reasons.restart certificate.bounds, certificate.graph.restart certificate.bounds,
    certificate.watches.frameArrays restart_arena restart_first,
    certificate.nonempty, certificate.nodup, certificate.noClash, ?_, ?_, ?_, ?_⟩
  · simpa only [restart_nVars] using certificate.learnedDistinct
  · rintro lit ⟨i, before, rfl⟩
    rw [restart_assigned certificate.bounds] at before
    rw [restart_trail, restart_mark_root certificate.bounds certificate.distinct i before]
    exact certificate.tags _ ⟨i, Nat.lt_of_lt_of_le before forced, rfl⟩
  · rintro lit ⟨i, before, rfl⟩ six
    rw [restart_assigned certificate.bounds] at before
    rw [restart_trail, restart_mark_root certificate.bounds certificate.distinct i before] at six
    rw [restart_trail]
    exact certificate.roots _ ⟨i, Nat.lt_of_lt_of_le before forced, rfl⟩ six
  · intro i before
    rw [restart_forced] at before
    rw [restart_trail, restart_mark_root certificate.bounds certificate.distinct i before]
    exact certificate.rootPrefix i before

theorem HasStateCertificate.restart {formula : Std.Sat.CNF Nat} {s : State}
    (certificate : HasStateCertificate formula s) : HasStateCertificate formula s.restart := by
  obtain ⟨original, learned, heads, rank, certificate⟩ := certificate
  exact ⟨original, learned, heads, rank, certificate.restart⟩

theorem restart_root {s : State} (bounds : TrailBounds s) :
    s.restart.assigned = s.restart.forced := by
  rw [restart_assigned bounds, restart_forced]

theorem restart_decisionHistory {s : State} (bounds : TrailBounds s) (entries : List StoredClause) :
    DecisionHistory s.restart entries := DecisionHistory.no_decisions (Nat.le_of_eq (restart_root bounds))

theorem restart_levelCover {s : State} (bounds : TrailBounds s) : LevelCover s.restart :=
  LevelCover.root (Nat.le_of_eq (restart_root bounds))

theorem restart_sixBefore {s : State} (bounds : TrailBounds s) : SixBefore s.restart := by
  intro i before _
  simpa only [restart_root bounds] using before

end MicrosatLean.Verification.Implementation.Search.Concrete
