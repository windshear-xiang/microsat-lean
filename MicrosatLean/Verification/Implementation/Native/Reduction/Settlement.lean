import MicrosatLean.Verification.Implementation.Native.Reduction.Watches
import MicrosatLean.Verification.Implementation.Native.Analysis.WatchHistory

namespace MicrosatLean.Verification.Implementation.Native.Reduction

open CDCL Representation Propagation Analysis

/-- Relocation may rebuild both numeric refs, but genuine pair coverage
recovers the old reference at the same watched literal. Thus exact literal
array preservation transfers settlement without assuming new ref ownership. -/
theorem settledWatches_of_sameClauses {before after : State}
    {oldEntries original learned : List StoredClause} {oldHeads newHeads : Nat → List Nat}
    {count : Nat} (oldCertificate : WatchCertificate before oldEntries oldHeads)
    (database : Database after original learned)
    (newCertificate : WatchCertificate after (original ++ learned) newHeads)
    (source : ∀ entry ∈ original ++ learned, ∃ prior ∈ oldEntries, entry.lits = prior.lits)
    (equal : PrefixLiterals before after count)
    (settled : SettledWatches before oldEntries oldHeads count) :
    SettledWatches after (original ++ learned) newHeads count := by
  intro lit falseLit ref watched entry member id
  obtain ⟨proper, properMember, properId, wide⟩ := newCertificate.references lit ref watched
  have same := database.layout.entry_eq_of_id properMember member (properId.symm.trans id)
  subst proper
  obtain ⟨prior, oldMember, literals⟩ := source entry member
  have oldWide : 2 ≤ prior.lits.size := by simpa only [literals] using wide
  have covered := oldCertificate.covered prior oldMember oldWide
  have atWatch := watch_ref_literals database newCertificate member watched id wide
  rw [literals] at atWatch
  have oldFalse := FalseBefore.transfer (fun i bound => (equal i bound).symm) falseLit
  have truth : TrueBefore before count (otherWatch prior.lits lit) := by
    rcases atWatch with first | second
    · obtain ⟨oldRef, oldWatched, oldId⟩ := clauseWatches_first_ref covered
      exact settled lit oldFalse oldRef (first ▸ oldWatched) prior oldMember oldId
    · obtain ⟨oldRef, oldWatched, oldId⟩ := clauseWatches_second_ref covered
      exact settled lit oldFalse oldRef (second ▸ oldWatched) prior oldMember oldId
  rw [literals]
  exact FalseBefore.transfer equal truth

theorem relocation_source {s : State} {original learned kept : List StoredClause} {k : Nat}
    (matching : RelocationMatches (compactionResult s k).2.1
      (retainedEntries s (lockedReasons s) k learned) kept) {entry : StoredClause}
    (member : entry ∈ original ++ kept) : ∃ prior ∈ original ++ learned, entry.lits = prior.lits := by
  rcases List.mem_append.mp member with originalMember | retained
  · exact ⟨entry, List.mem_append_left learned originalMember, rfl⟩
  · have wordMember : entry.lits ∈ kept.map StoredClause.lits := List.mem_map.mpr ⟨entry, retained, rfl⟩
    rw [← matching.literals] at wordMember
    obtain ⟨prior, oldMember, same⟩ := List.mem_map.mp wordMember
    exact ⟨prior, List.mem_append_right original (List.mem_filter.mp oldMember).1, same.symm⟩

/-- The actual reducer's exact retained literal arrays suffice to transfer
completed watch truth to its actual rebuilt heads and genuine output IDs. -/
theorem settledWatches_reduceDB {s : State} {original learned kept : List StoredClause}
    {heads newHeads : Nat → List Nat} {k : Nat}
    (certificate : WatchCertificate s (original ++ learned) heads)
    (database : Database (s.reduceDB k) original kept)
    (output : WatchCertificate (s.reduceDB k) (original ++ kept) newHeads)
    (matching : RelocationMatches (compactionResult s k).2.1
      (retainedEntries s (lockedReasons s) k learned) kept)
    (settled : SettledWatches s (original ++ learned) heads s.assigned) :
    SettledWatches (s.reduceDB k) (original ++ kept) newHeads (s.reduceDB k).assigned := by
  rw [reduceDB_assigned]
  exact settledWatches_of_sameClauses certificate database output
    (fun _ member => relocation_source matching member) (fun _ _ => by rw [reduceDB_trail]) settled

theorem activeUnits_reduceDB {s : State} {original learned kept : List StoredClause} {k : Nat}
    (matching : RelocationMatches (compactionResult s k).2.1
      (retainedEntries s (lockedReasons s) k learned) kept)
    (units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]!) :
    ∀ entry ∈ original ++ kept, entry.lits.size = 1 →
      TrueBefore (s.reduceDB k) (s.reduceDB k).assigned entry.lits[0]! := by
  intro entry member unit
  obtain ⟨prior, priorMember, literals⟩ := relocation_source matching member
  obtain ⟨i, before, value⟩ := units prior priorMember (by simpa only [literals] using unit)
  exact ⟨i, by simpa only [reduceDB_assigned] using before,
    by simpa only [reduceDB_trail, literals] using value⟩

end MicrosatLean.Verification.Implementation.Native.Reduction
