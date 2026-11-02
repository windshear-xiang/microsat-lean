import MicrosatLean.Verification.Implementation.Native.Search.WatchUnitState
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchSaved

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Std.Sat

theorem decisionWatchHistory_retain {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    {target : StoredClause} (member : target ∈ original ++ learned)
    (history : DecisionWatchHistory s (original ++ learned) heads) (first : Bool) (arena : Array Nat) :
    DecisionWatchHistory { s with arena := arena }
      ((original ++ learned).map (retainWatchEntry target.id first)) heads := by
  intro decision lower before reason
  exact settledWatches_retain database certificate member (history decision lower before reason) first arena

theorem decisionWatchHistory_move {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (active : ActiveTrail s)
    {target : StoredClause} (member : target ∈ original ++ learned)
    {lit newLit : Lit} {moved : Nat} (current : moved ∈ heads lit)
    (id : watchClause moved = target.id) (wide : 2 ≤ target.lits.size)
    (falseLit : s.mark lit ≠ 0) (unmarked : s.mark newLit = 0)
    (history : DecisionWatchHistory s (original ++ learned) heads)
    (offset : Nat) (first : Bool) (arena firstHeads : Array Nat) :
    DecisionWatchHistory (restoreWatchArrays s arena firstHeads)
      ((original ++ learned).map (moveWatchEntry target.id offset first)) (moveHeads heads newLit moved) := by
  intro decision lower before reason
  exact settledWatches_move database certificate active member current id wide falseLit unmarked
    (Nat.le_of_lt before) (history decision lower before reason) offset first arena firstHeads

theorem StateCertificate.moveWatch_saved {formula : CNF Nat} {s : State}
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
      (DecisionWatchHistory s (original ++ learned) heads →
        DecisionWatchHistory after (nextOriginal ++ nextLearned) (moveHeads heads newLit ref)) := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := certificate.watches.references lit ref cursor.member
  have prior : previous = 0 ∨ StoredWatchRef (original ++ learned) previous := by
    by_cases head : previous = 0
    · exact Or.inl head
    · exact Or.inr (certificate.watches.references lit previous (cursor.previous_member head))
  obtain ⟨offset, _, within, position, exactDatabase, _⟩ :=
    replacement_branch_database certificate.database certificate.meaning lit ref previous member id wide
      (certificate.watches.entry certificate.database cursor.member) prior found
  obtain ⟨nextOriginal, nextLearned, nextCertificate, nextCursor, _⟩ := certificate.moveWatch cursor literal falseLit found
  obtain ⟨sameOriginal, sameLearned⟩ := nextCertificate.database.unique exactDatabase
  subst nextOriginal nextLearned
  have selected : (orientWatch s.arena (watchClause ref) lit)[pos]! = entry.lits[offset]! := by
    rw [id, orientWatch_read_other _ _ _ _ (by omega), position]
    exact (certificate.database.layout.packed member).literals offset within
  have unmarked : s.mark ((orientWatch s.arena (watchClause ref) lit)[pos]!) = 0 := by
    have scan := found
    rw [id, replacement_orientWatch] at scan
    have result := (replacementScan_some scan).2.2.2.1
    rw [selected, ← (certificate.database.layout.packed member).literals offset within, ← position]
    exact result
  refine ⟨_, _, nextCertificate, nextCursor, ?_⟩
  intro history
  simpa only [List.map_append] using decisionWatchHistory_move certificate.database certificate.watches
    certificate.active member cursor.member id wide falseLit unmarked history offset (s.db entry.id == lit)
    (movedWatchArrays s.arena s.first lit ref previous pos).1 (movedWatchArrays s.arena s.first lit ref previous pos).2

theorem StateCertificate.retainWatch_saved {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (falseLit : s.mark lit ≠ 0) :
    let after := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    ∃ nextOriginal nextLearned,
      StateCertificate formula after nextOriginal nextLearned heads rank ∧
      (DecisionWatchHistory s (original ++ learned) heads →
        DecisionWatchHistory after (nextOriginal ++ nextLearned) heads) := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := certificate.watches.references lit ref current
  have watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.watches.entry certificate.database current).2.2.2
  have exactDatabase := retainWatch_database certificate.database member lit wide watched
  rw [← id] at exactDatabase
  obtain ⟨nextOriginal, nextLearned, nextCertificate, _⟩ := certificate.retainWatch current falseLit
  obtain ⟨sameOriginal, sameLearned⟩ := nextCertificate.database.unique exactDatabase
  subst nextOriginal nextLearned
  refine ⟨_, _, nextCertificate, ?_⟩
  intro history
  simpa only [List.map_append, id] using decisionWatchHistory_retain certificate.database certificate.watches
    member history (s.db entry.id == lit) (Propagation.retainWatch s.arena (watchClause ref) lit)

theorem StateCertificate.assign_watchSaved {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionWatchHistory s (original ++ learned) heads)
    {entry : StoredClause} (member : entry ∈ original ++ learned)
    (head : s.mark (s.db entry.id) = 0) (opposite : s.mark (Lit.negate (s.db entry.id)) = 0) (root : Bool) :
    DecisionWatchHistory (s.assign entry.id root) (original ++ learned) heads := by
  have packed := certificate.database.layout.packed member
  have nonempty := certificate.nonempty entry member
  have first : s.db entry.id = entry.lits[0]! := by simpa using packed.literals 0 nonempty
  have literal : LiteralBound s.nVars (s.db entry.id) := by
    rw [first]
    apply packed.wellFormed
    simpa only [getElem!_pos entry.lits 0 nonempty] using Array.getElem_mem nonempty
  apply DecisionWatchHistory.assign history entry.id root (by have := packed.startLower; omega)
  · rw [certificate.arrays.trailSize]
    have assigned := certificate.bounds.assignedVars
    omega
  · exact (certificate.arrays.variable_index literal.2).1
  · exact freshVariable_of_unmarked_literal certificate.active head opposite

theorem StateCertificate.watchUnit_saved {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (falseLit : s.mark lit ≠ 0)
    (root : Bool) (rootTrail : RootWatchTrail s root)
    (missing : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = none)
    (head : s.mark ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!) = 0)
    (opposite : s.mark (Lit.negate ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!)) = 0) :
    let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    let after := retained.assign (watchClause ref) root
    ∃ nextOriginal nextLearned nextRank,
      StateCertificate formula after nextOriginal nextLearned heads nextRank ∧
      (DecisionWatchHistory s (original ++ learned) heads → DecisionWatchHistory after (nextOriginal ++ nextLearned) heads) := by
  dsimp only
  obtain ⟨retainedOriginal, retainedLearned, retainedCertificate, savedRetained⟩ := certificate.retainWatch_saved current falseLit
  obtain ⟨nextOriginal, nextLearned, nextRank, nextCertificate, _⟩ := certificate.watchUnit current falseLit root rootTrail missing head opposite
  have assignedDatabase := retainedCertificate.database.assign (watchClause ref) root
  obtain ⟨sameOriginal, sameLearned⟩ := nextCertificate.database.unique assignedDatabase
  subst nextOriginal nextLearned
  refine ⟨retainedOriginal, retainedLearned, nextRank, nextCertificate, ?_⟩
  intro history
  obtain ⟨entry, member, id, _⟩ := retainedCertificate.watches.references lit ref current
  have headZero :
      ({ s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }).mark
        (({ s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }).db entry.id) = 0 := by
    simpa only [← id, State.mark, State.db] using head
  have oppositeZero :
      ({ s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }).mark
        (Lit.negate (({ s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }).db entry.id)) = 0 := by
    simpa only [← id, State.mark, State.db] using opposite
  have next := retainedCertificate.assign_watchSaved (savedRetained history) member headZero oppositeZero root
  simpa only [← id] using next

end MicrosatLean.Verification.Implementation.Native.Search
