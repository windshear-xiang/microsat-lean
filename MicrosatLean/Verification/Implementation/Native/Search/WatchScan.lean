import MicrosatLean.Verification.Implementation.Native.Search.WatchSavedState
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchUnits

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- The concrete facts carried within one false literal's finite list scan. -/
structure WatchScanFacts (formula : Std.Sat.CNF Nat) (s : State)
    (original learned : List StoredClause) (heads : Nat → List Nat) (rank : Lit → Nat)
    (count : Nat) (lit : Lit) (previous : Nat) (remaining : List Nat) : Prop where
  base : StateCertificate formula s original learned heads rank
  history : DecisionHistory s (original ++ learned)
  saved : DecisionWatchHistory s (original ++ learned) heads
  units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]!
  bound : count ≤ s.assigned
  prefixSettled : SettledPrefix s (original ++ learned) heads count
  visited : SettledCursor s (original ++ learned) heads lit remaining
  cursor : WatchCursor heads lit previous remaining

/-- The exact keep-orientation preserves all already established scan facts.
The current reference is deliberately left unvisited until its branch settles. -/
theorem WatchScanFacts.orient {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {count : Nat} {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (facts : WatchScanFacts formula s original learned heads rank count lit previous (ref :: rest))
    (falseLit : s.mark lit ≠ 0) :
    let after := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    ∃ nextOriginal nextLearned,
      WatchScanFacts formula after nextOriginal nextLearned heads rank count lit previous (ref :: rest) := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := facts.base.watches.references lit ref facts.cursor.member
  have watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (facts.base.watches.entry facts.base.database facts.cursor.member).2.2.2
  have exactDatabase := retainWatch_database facts.base.database member lit wide watched
  rw [← id] at exactDatabase
  obtain ⟨nextOriginal, nextLearned, nextBase, nextHistory⟩ := facts.base.retainWatch facts.cursor.member falseLit
  obtain ⟨sameOriginal, sameLearned⟩ := nextBase.database.unique exactDatabase
  subst nextOriginal nextLearned
  let arena := Propagation.retainWatch s.arena (watchClause ref) lit
  let f := retainWatchEntry (watchClause ref) (s.db (watchClause ref) == lit)
  have units := units_map_long facts.base.database member wide facts.units f (retainWatchEntry_size _ _)
    (fun old different => retainWatchEntry_of_ne _ _ _ (by simpa only [id] using different)) arena s.first
  have saved := decisionWatchHistory_retain facts.base.database facts.base.watches member facts.saved
    (s.db entry.id == lit) arena
  have prefixSettled := facts.prefixSettled.retain facts.base.database facts.base.watches member (s.db entry.id == lit) arena
  have visited := facts.visited.retain facts.base.database facts.base.watches member (s.db entry.id == lit) arena
  refine ⟨_, _, nextBase, nextHistory facts.history, ?_, ?_, facts.bound, ?_, ?_, facts.cursor⟩
  · simpa only [id, arena, List.map_append] using saved
  · simpa only [f, arena, List.map_append, restoreWatchArrays] using units
  · simpa only [id, arena, List.map_append] using prefixSettled
  · simpa only [id, arena, List.map_append] using visited

/-- Actual replacement preserves the simultaneous base, both histories,
singleton truth and active settlement, while removing exactly the visited ref. -/
theorem WatchScanFacts.move {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {count : Nat} {lit : Lit} {previous ref pos : Nat} {rest : List Nat}
    (facts : WatchScanFacts formula s original learned heads rank count lit previous (ref :: rest))
    (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (found : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = some pos) :
    let arrays := movedWatchArrays s.arena s.first lit ref previous pos
    let after := restoreWatchArrays s arrays.1 arrays.2
    let newLit := (orientWatch s.arena (watchClause ref) lit)[pos]!
    ∃ nextOriginal nextLearned,
      WatchScanFacts formula after nextOriginal nextLearned (moveHeads heads newLit ref) rank count lit previous rest := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := facts.base.watches.references lit ref facts.cursor.member
  have prior : previous = 0 ∨ StoredWatchRef (original ++ learned) previous := by
    by_cases head : previous = 0
    · exact Or.inl head
    · exact Or.inr (facts.base.watches.references lit previous (facts.cursor.previous_member head))
  obtain ⟨offset, _, within, position, exactDatabase, _⟩ :=
    replacement_branch_database facts.base.database facts.base.meaning lit ref previous member id wide
      (facts.base.watches.entry facts.base.database facts.cursor.member) prior found
  obtain ⟨nextOriginal, nextLearned, nextBase, nextCursor, nextHistory⟩ := facts.base.moveWatch facts.cursor literal falseLit found
  obtain ⟨sameOriginal, sameLearned⟩ := nextBase.database.unique exactDatabase
  subst nextOriginal nextLearned
  have selected : (orientWatch s.arena (watchClause ref) lit)[pos]! = entry.lits[offset]! := by
    rw [id, orientWatch_read_other _ _ _ _ (by omega), position]
    exact (facts.base.database.layout.packed member).literals offset within
  have unmarked : s.mark ((orientWatch s.arena (watchClause ref) lit)[pos]!) = 0 := by
    have scan := found
    rw [id, replacement_orientWatch] at scan
    have result := (replacementScan_some scan).2.2.2.1
    rw [selected, ← (facts.base.database.layout.packed member).literals offset within, ← position]
    exact result
  let f := moveWatchEntry entry.id offset (s.db entry.id == lit)
  let arrays := movedWatchArrays s.arena s.first lit ref previous pos
  have saved := decisionWatchHistory_move facts.base.database facts.base.watches facts.base.active member
    facts.cursor.member id wide falseLit unmarked facts.saved offset (s.db entry.id == lit) arrays.1 arrays.2
  have units := units_map_long facts.base.database member wide facts.units f (moveWatchEntry_size _ _ _)
    (moveWatchEntry_of_ne _ _ _) arrays.1 arrays.2
  have prefixSettled := facts.prefixSettled.move facts.base.database facts.base.watches facts.base.active member
    facts.cursor.member id wide falseLit unmarked facts.bound offset (s.db entry.id == lit) arrays.1 arrays.2
  have visited := facts.visited.move facts.base.database facts.base.watches facts.base.active member
    facts.cursor.member id wide falseLit unmarked offset (s.db entry.id == lit) arrays.1 arrays.2
  refine ⟨_, _, nextBase, nextHistory facts.history, ?_, ?_, facts.bound, ?_, ?_, nextCursor⟩
  · simpa only [List.map_append, arrays] using saved
  · simpa only [List.map_append, f, arrays] using units
  · simpa only [List.map_append, arrays] using prefixSettled
  · simpa only [List.map_append, arrays] using visited

end MicrosatLean.Verification.Implementation.Native.Search
