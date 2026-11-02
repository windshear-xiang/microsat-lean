import MicrosatLean.Verification.Implementation.Native.Propagation.WatchTraversal

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation Analysis Std.Sat

/-- Completing the current literal's list extends the processed prefix by
that actual trail entry, while retaining concrete active-trail truth witnesses. -/
theorem SettledPrefix.extend {s : State} {entries : List StoredClause}
    {heads : Nat → List Nat} {count : Nat} {lit : Lit}
    (settled : SettledPrefix s entries heads count)
    (current : ∀ ref ∈ heads lit, SettledWatch s entries s.assigned lit ref)
    (value : s.trail[count]! = lit) : SettledPrefix s entries heads (count + 1) := by
  intro query falseLit ref member
  obtain ⟨i, before, literal⟩ := falseLit
  by_cases old : i < count
  · exact settled query ⟨i, old, literal⟩ ref member
  · have equal : i = count := by omega
    subst i
    have same : lit = query := value.symm.trans literal
    exact (same ▸ current) ref member

theorem SettledWatchReturn.finish_prefix {after : Machine} {entries : List StoredClause}
    {heads : Nat → List Nat} {count : Nat} {lit : Lit}
    (result : SettledWatchReturn after entries heads count lit)
    (phase : after.phase = .nextLiteral) (value : after.solver.trail[count]! = lit) :
    SettledPrefix after.solver entries heads (count + 1) := by
  rcases result with ⟨prefixSettled, finished | unit⟩
  · exact prefixSettled.extend finished.2 value
  · obtain ⟨_, watch, _⟩ := unit
    cases watch.symm.trans phase

/-- The executable public watch phase restores its detached arrays before
returning. The arena-length budget is sufficient for its real cursor. -/
theorem step_watch_settled {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {count : Nat}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    (nodup : ∀ entry ∈ original ++ learned, entry.lits.toList.Nodup) (arrays : ArrayBounds s)
    (active : ActiveTrail s) (bounds : TrailBounds s) (marked : MarkedOnTrail s)
    (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0) (bound : count ≤ s.assigned)
    (prefixSettled : SettledPrefix s (original ++ learned) heads count)
    (remaining : List Nat) (visited : SettledCursor s (original ++ learned) heads lit remaining)
    (cursor : WatchCursor heads lit previous remaining) {after : Machine}
    (running : step ⟨s, decision, .watch, oldLemmas, root, lit, previous⟩ = .running after)
    (noAnalysis : after.solver.nLemmas = s.nLemmas) :
    ∃ nextOriginal nextLearned nextHeads,
      Database after.solver nextOriginal nextLearned ∧ DatabaseMeaning formula nextOriginal nextLearned ∧
      WatchCertificate after.solver (nextOriginal ++ nextLearned) nextHeads ∧
      (∀ entry ∈ nextOriginal ++ nextLearned, entry.lits.toList.Nodup) ∧
      SettledWatchReturn after (nextOriginal ++ nextLearned) nextHeads count lit := by
  change propagateWatches s.arena.size { s with arena := #[], first := #[] } s.arena s.first
    decision oldLemmas root lit previous = .running after at running
  have detachedBounds : TrailBounds { s with arena := #[], first := #[] } :=
    ⟨bounds.forcedProcessed, bounds.processedAssigned, bounds.assignedVars⟩
  exact propagateWatches_settled { s with arena := #[], first := #[] } decision oldLemmas root lit
    remaining s.arena.size s.arena s.first previous database meaning certificate nodup arrays
    active detachedBounds marked literal falseLit bound prefixSettled visited cursor
    (watchCursor_length_lt_arena database certificate cursor) running noAnalysis

end MicrosatLean.Verification.Implementation.Native.Propagation
