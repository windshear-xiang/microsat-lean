import MicrosatLean.Verification.Implementation.Native.Search.WatchPermutation
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchReasonRetention
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchSettlementBranches

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- Actual successful replacement preserves every base certificate field.
The false current watch excludes active reason movement; literal permutations
preserve normalization, canonical learned keys, and saved decision history. -/
theorem StateCertificate.moveWatch {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    {lit : Lit} {previous ref pos : Nat} {rest : List Nat}
    (cursor : WatchCursor heads lit previous (ref :: rest))
    (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (found : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = some pos) :
    let arrays := movedWatchArrays s.arena s.first lit ref previous pos
    let after := restoreWatchArrays s arrays.1 arrays.2
    let newLit := (orientWatch s.arena (watchClause ref) lit)[pos]!
    ∃ nextOriginal nextLearned,
      StateCertificate formula after nextOriginal nextLearned (moveHeads heads newLit ref) rank ∧
      WatchCursor (moveHeads heads newLit ref) lit previous rest ∧
      (DecisionHistory s (original ++ learned) → DecisionHistory after (nextOriginal ++ nextLearned)) := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := certificate.watches.references lit ref cursor.member
  have prior : previous = 0 ∨ StoredWatchRef (original ++ learned) previous := by
    by_cases head : previous = 0
    · exact Or.inl head
    · exact Or.inr (certificate.watches.references lit previous (cursor.previous_member head))
  obtain ⟨offset, _, _, _, exactDatabase, _⟩ :=
    replacement_branch_database certificate.database certificate.meaning lit ref previous member id wide
      (certificate.watches.entry certificate.database cursor.member) prior found
  obtain ⟨nextOriginal, nextLearned, nextDatabase, nextMeaning, nextWatches, _, nextCursor⟩ :=
    replacement_branch_certificate certificate.database certificate.meaning certificate.watches
      certificate.nodup certificate.arrays cursor literal falseLit found
  obtain ⟨sameOriginal, sameLearned⟩ := nextDatabase.unique exactDatabase
  subst nextOriginal nextLearned
  have graph := replacement_branch_reasonGraph certificate.database certificate.meaning certificate.graph
    certificate.active (Nat.le_refl _) certificate.reasons lit ref previous member id wide
    (certificate.watches.entry certificate.database cursor.member) prior found
  refine ⟨_, _, certificate.watchArrays _ _ (movedWatchArrays_first_size _ _ _ _ _ _)
    (moveWatchEntry entry.id offset (s.db entry.id == lit))
    (moveWatchEntry_id _ _ _) (moveWatchEntry_size _ _ _) (moveWatchEntry_perm _ _ _)
    _ nextDatabase nextMeaning nextWatches graph, nextCursor, ?_⟩
  intro history
  simpa only [List.map_append] using decisionHistory_watchArrays_map history
    (movedWatchArrays s.arena s.first lit ref previous pos).1
    (movedWatchArrays s.arena s.first lit ref previous pos).2
    (moveWatchEntry entry.id offset (s.db entry.id == lit)) (moveWatchEntry_perm _ _ _)

/-- Keeping a false watch after an unsuccessful replacement scan preserves
the full base certificate. An active reason keeps its true head first because
that head is unmarked and cannot equal the false current literal. -/
theorem StateCertificate.retainWatch {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (falseLit : s.mark lit ≠ 0) :
    let after := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    ∃ nextOriginal nextLearned,
      StateCertificate formula after nextOriginal nextLearned heads rank ∧
      (DecisionHistory s (original ++ learned) → DecisionHistory after (nextOriginal ++ nextLearned)) := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := certificate.watches.references lit ref current
  have watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.watches.entry certificate.database current).2.2.2
  have exactDatabase := retainWatch_database certificate.database member lit wide watched
  rw [← id] at exactDatabase
  obtain ⟨nextOriginal, nextLearned, nextDatabase, nextMeaning, nextWatches, _⟩ :=
    retainWatch_certificate certificate.database certificate.meaning certificate.watches certificate.nodup lit ref current
  obtain ⟨sameOriginal, sameLearned⟩ := nextDatabase.unique exactDatabase
  subst nextOriginal nextLearned
  have graph := retainWatch_reasonGraph certificate.database certificate.graph certificate.active
    certificate.reasons member wide lit falseLit watched
  rw [← id] at graph
  refine ⟨_, _, certificate.watchArrays _ s.first rfl
    (retainWatchEntry (watchClause ref) (s.db (watchClause ref) == lit))
    (retainWatchEntry_id _ _) (retainWatchEntry_size _ _) (retainWatchEntry_perm _ _)
    heads nextDatabase nextMeaning nextWatches graph, ?_⟩
  intro history
  simpa only [List.map_append, restoreWatchArrays] using decisionHistory_watchArrays_map history
    (Propagation.retainWatch s.arena (watchClause ref) lit) s.first
    (retainWatchEntry (watchClause ref) (s.db (watchClause ref) == lit)) (retainWatchEntry_perm _ _)

end MicrosatLean.Verification.Implementation.Native.Search
