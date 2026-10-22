import MicrosatLean.Verification.Search.StateCertificate
import MicrosatLean.Verification.Reduction.Watches
import MicrosatLean.Verification.Analysis.LevelHistory
import MicrosatLean.Verification.Analysis.MarkCleanup

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Reduction Std.Sat

private theorem retained_source {s : State} {original learned kept : List StoredClause} {k : Nat}
    (matching : RelocationMatches (compactionResult s k).2.1
      (retainedEntries s (lockedReasons s) k learned) kept) {entry : StoredClause}
    (member : entry ∈ original ++ kept) :
    ∃ prior ∈ original ++ learned, entry.lits = prior.lits := by
  rcases List.mem_append.mp member with old | retained
  · exact ⟨entry, List.mem_append_left learned old, rfl⟩
  · have literalMember : entry.lits ∈ kept.map StoredClause.lits := List.mem_map.mpr ⟨entry, retained, rfl⟩
    rw [← matching.literals] at literalMember
    obtain ⟨prior, priorMember, equal⟩ := List.mem_map.mp literalMember
    exact ⟨prior, List.mem_append_right original (List.mem_filter.mp priorMember).1, equal.symm⟩

/-- Every normalization property is transferred through exact literal
equality, while canonical learned keys form a subsequence of the old keys. -/
theorem StateCertificate.reduceDB_with_relocation {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (root : s.assigned = s.forced) (k : Nat) :
    ∃ kept newHeads, StateCertificate formula (s.reduceDB k) original kept newHeads rank ∧
      RelocationMatches (compactionResult s k).2.1
        (retainedEntries s (lockedReasons s) k learned) kept ∧
      ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept) := by
  obtain ⟨kept, newHeads, database, meaning, matching, relocations, reasons, graph, arrays, watches⟩ :=
    reduceDB_reasons_and_watches certificate.database certificate.meaning certificate.watches
      certificate.reasons certificate.arrays certificate.active certificate.graph root k
  have unchanged : StateCertificate formula
      { s.reduceDB k with
        arena := s.arena, first := s.first, reasons := s.reasons,
        nLemmas := s.nLemmas, maxLemmas := s.maxLemmas, stats := s.stats }
      original learned heads rank := by
    rw [reduceDB_restore]
    exact certificate
  refine ⟨kept, newHeads, ?_, matching, relocations⟩
  refine ⟨arrays, reduceDB_trailBounds certificate.bounds k, unchanged.active, unchanged.distinct,
    unchanged.phases, unchanged.marked, unchanged.order, database, meaning, reasons, graph,
    watches, ?_, ?_, ?_, ?_, unchanged.tags, unchanged.roots, unchanged.rootPrefix⟩
  · intro entry member
    obtain ⟨prior, oldMember, same⟩ := retained_source matching member
    rw [same]
    exact certificate.nonempty prior oldMember
  · intro entry member
    obtain ⟨prior, oldMember, same⟩ := retained_source matching member
    rw [same]
    exact certificate.nodup prior oldMember
  · intro entry member
    obtain ⟨prior, oldMember, same⟩ := retained_source matching member
    rw [same]
    exact certificate.noClash prior oldMember
  · have keys : kept.map (fun entry => canonicalKey s.nVars entry.lits) =
        (retainedEntries s (lockedReasons s) k learned).map (fun entry => canonicalKey s.nVars entry.lits) := by
      have equal := congrArg (List.map (canonicalKey s.nVars)) matching.literals
      simpa only [List.map_map, Function.comp_def] using equal.symm
    rw [reduceDB_nVars, keys]
    have sublist : (retainedEntries s (lockedReasons s) k learned).Sublist learned := List.filter_sublist
    exact (sublist.map (fun entry => canonicalKey s.nVars entry.lits)).nodup certificate.learnedDistinct

/-- The full base certificate survives actual root database reduction. -/
theorem StateCertificate.reduceDB {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (root : s.assigned = s.forced) (k : Nat) :
    ∃ kept newHeads, StateCertificate formula (s.reduceDB k) original kept newHeads rank := by
  obtain ⟨kept, newHeads, result, _, _⟩ := certificate.reduceDB_with_relocation root k
  exact ⟨kept, newHeads, result⟩

theorem HasStateCertificate.reduceDB {formula : CNF Nat} {s : State}
    (certificate : HasStateCertificate formula s) (root : s.assigned = s.forced) (k : Nat) :
    HasStateCertificate formula (s.reduceDB k) := by
  obtain ⟨original, learned, heads, rank, certificate⟩ := certificate
  obtain ⟨kept, newHeads, result⟩ := certificate.reduceDB root k
  exact ⟨original, kept, newHeads, rank, result⟩

theorem reduceDB_root {s : State} (root : s.assigned = s.forced) (k : Nat) :
    (s.reduceDB k).assigned = (s.reduceDB k).forced := by
  simpa only [reduceDB_assigned, reduceDB_forced] using root

theorem reduceDB_decisionHistory {s : State} (root : s.assigned = s.forced) (k : Nat)
    (entries : List StoredClause) : DecisionHistory (s.reduceDB k) entries :=
  DecisionHistory.no_decisions (Nat.le_of_eq (reduceDB_root root k))

theorem reduceDB_levelCover {s : State} (root : s.assigned = s.forced) (k : Nat) :
    LevelCover (s.reduceDB k) := LevelCover.root (Nat.le_of_eq (reduceDB_root root k))

theorem reduceDB_sixBefore {s : State} (root : s.assigned = s.forced) (k : Nat) :
    SixBefore (s.reduceDB k) := by
  intro i before _
  simpa only [reduceDB_root root k] using before

/-- Unit truth in the retained root prefix transfers through the exact
retained literal arrays; no output unit normalization is postulated. -/
theorem reduceDB_unit_truth {s : State} {original learned kept : List StoredClause} {k : Nat}
    (matching : RelocationMatches (compactionResult s k).2.1
      (retainedEntries s (lockedReasons s) k learned) kept)
    (units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore s s.forced entry.lits[0]!) :
    ∀ entry ∈ original ++ kept, entry.lits.size = 1 →
      TrueBefore (s.reduceDB k) (s.reduceDB k).forced entry.lits[0]! := by
  intro entry member unit
  obtain ⟨prior, oldMember, same⟩ := retained_source matching member
  obtain ⟨i, before, value⟩ := units prior oldMember (by simpa only [same] using unit)
  exact ⟨i, by simpa only [reduceDB_forced] using before,
    by simpa only [reduceDB_trail, same] using value⟩

end MicrosatLean.Verification.Search
