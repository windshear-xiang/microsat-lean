import MicrosatLean.Verification.Implementation.Propagation.WatchSettlementVisit
import MicrosatLean.Verification.Implementation.Propagation.DatabaseIdentity
import MicrosatLean.Verification.Implementation.Propagation.WatchBounds

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL Representation Analysis Std.Sat

theorem WatchCertificate.assign {s : State} {entries : List StoredClause} {heads : Nat → List Nat}
    (certificate : WatchCertificate s entries heads) (id : Nat) (root : Bool) :
    WatchCertificate (s.assign id root) entries heads :=
  ⟨certificate.links, certificate.references, certificate.covered, certificate.unique⟩

/-- Skipping the current satisfied clause preserves the old witnesses and
settles this visit using the actual mark test before advancing its cursor. -/
theorem skip_branch_settlement {s : State} {formula : Std.Sat.CNF Nat}
    {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    (nodup : ∀ entry ∈ original ++ learned, entry.lits.toList.Nodup) (marked : MarkedOnTrail s)
    {count : Nat} {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (cursor : WatchCursor heads lit previous (ref :: rest))
    (prefixSettled : SettledPrefix s (original ++ learned) heads count)
    (visited : SettledCursor s (original ++ learned) heads lit (ref :: rest))
    (truth : s.mark (Lit.negate ((retainWatch s.arena (watchClause ref) lit)[watchClause ref]!)) ≠ 0) :
    let after := { s with arena := retainWatch s.arena (watchClause ref) lit }
    ∃ nextOriginal nextLearned,
      Database after nextOriginal nextLearned ∧ DatabaseMeaning formula nextOriginal nextLearned ∧
      WatchCertificate after (nextOriginal ++ nextLearned) heads ∧
      (∀ entry ∈ nextOriginal ++ nextLearned, entry.lits.toList.Nodup) ∧
      WatchCursor heads lit ref rest ∧
      SettledPrefix after (nextOriginal ++ nextLearned) heads count ∧
      SettledCursor after (nextOriginal ++ nextLearned) heads lit rest := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := certificate.references lit ref cursor.member
  have watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.entry database cursor.member).2.2.2
  obtain ⟨nextOriginal, nextLearned, nextDatabase, nextMeaning, nextCertificate, nextNodup⟩ :=
    retainWatch_certificate database meaning certificate nodup lit ref cursor.member
  have exactDatabase := retainWatch_database database member lit wide watched
  rw [← id] at exactDatabase
  obtain ⟨sameOriginal, sameLearned⟩ := nextDatabase.unique exactDatabase
  subst nextOriginal nextLearned
  have retainedPrefix := prefixSettled.retain database certificate member (s.db entry.id == lit)
    (retainWatch s.arena (watchClause ref) lit)
  have retainedVisited := visited.retain database certificate member (s.db entry.id == lit)
    (retainWatch s.arena (watchClause ref) lit)
  have settled := retainWatch_settled_of_marked database certificate marked member cursor.member id wide
    (by simpa only [id] using truth)
  have nonzero := storedWatchRef_nonzero database (certificate.references lit ref cursor.member)
  refine ⟨_, _, nextDatabase, nextMeaning, nextCertificate, nextNodup, cursor.advance nonzero, ?_, ?_⟩
  · simpa only [List.map_append, id] using retainedPrefix
  · apply SettledCursor.advance
    · simpa only [List.map_append, id] using retainedVisited
    · simpa only [List.map_append, id] using settled

/-- A genuine unit return settles its current watch with the newly appended
true literal, and preserves all earlier processed/visited witnesses. -/
theorem unit_branch_settlement {s : State} {formula : Std.Sat.CNF Nat}
    {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    (nodup : ∀ entry ∈ original ++ learned, entry.lits.toList.Nodup)
    {count : Nat} (bound : count ≤ s.assigned)
    {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (cursor : WatchCursor heads lit previous (ref :: rest))
    (prefixSettled : SettledPrefix s (original ++ learned) heads count)
    (visited : SettledCursor s (original ++ learned) heads lit (ref :: rest))
    (root : Bool) (space : s.assigned < s.trail.size) :
    let retained := { s with arena := retainWatch s.arena (watchClause ref) lit }
    let after := retained.assign (watchClause ref) root
    ∃ nextOriginal nextLearned,
      Database after nextOriginal nextLearned ∧ DatabaseMeaning formula nextOriginal nextLearned ∧
      WatchCertificate after (nextOriginal ++ nextLearned) heads ∧
      (∀ entry ∈ nextOriginal ++ nextLearned, entry.lits.toList.Nodup) ∧
      WatchCursor heads lit ref rest ∧
      SettledPrefix after (nextOriginal ++ nextLearned) heads count ∧
      SettledCursor after (nextOriginal ++ nextLearned) heads lit rest := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := certificate.references lit ref cursor.member
  have watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.entry database cursor.member).2.2.2
  obtain ⟨nextOriginal, nextLearned, nextDatabase, nextMeaning, nextCertificate, nextNodup⟩ :=
    retainWatch_certificate database meaning certificate nodup lit ref cursor.member
  have exactDatabase := retainWatch_database database member lit wide watched
  rw [← id] at exactDatabase
  obtain ⟨sameOriginal, sameLearned⟩ := nextDatabase.unique exactDatabase
  subst nextOriginal nextLearned
  have retainedPrefix := prefixSettled.retain database certificate member (s.db entry.id == lit)
    (retainWatch s.arena (watchClause ref) lit)
  have retainedVisited := visited.retain database certificate member (s.db entry.id == lit)
    (retainWatch s.arena (watchClause ref) lit)
  have settled := retainWatch_settled_of_assign database certificate member cursor.member id wide root space
  have nonzero := storedWatchRef_nonzero database (certificate.references lit ref cursor.member)
  refine ⟨_, _, nextDatabase.assign _ _, nextMeaning, nextCertificate.assign _ _, nextNodup,
    cursor.advance nonzero, ?_, ?_⟩
  · simpa only [List.map_append, id] using retainedPrefix.assign bound
  · apply SettledCursor.advance
    · simpa only [List.map_append, id] using (retainedVisited.assign (id := watchClause ref) (root := root))
    · simpa only [List.map_append, id] using settled

end MicrosatLean.Verification.Implementation.Propagation
