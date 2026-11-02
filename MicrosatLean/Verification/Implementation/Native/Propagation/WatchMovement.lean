import MicrosatLean.Verification.Implementation.Native.Propagation.WatchCoverage
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchRewire

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation Std.Sat

/-- Compose the real literal permutation and header rewiring into a complete
watch certificate. The next cursor retains exactly the unvisited tail.
Duplicate freedom supplies distinct new/retained watched literals. -/
theorem replacement_branch_certificate {s : State} {formula : Std.Sat.CNF Nat}
    {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    (nodup : ∀ entry ∈ original ++ learned, entry.lits.toList.Nodup) (arrays : ArrayBounds s)
    {lit : Lit} {previous ref pos : Nat} {rest : List Nat}
    (cursor : WatchCursor heads lit previous (ref :: rest)) (literal : LiteralBound s.nVars lit)
    (falseLit : s.mark lit ≠ 0)
    (found : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = some pos) :
    let nextArrays := movedWatchArrays s.arena s.first lit ref previous pos
    let after := restoreWatchArrays s nextArrays.1 nextArrays.2
    let newLit := (orientWatch s.arena (watchClause ref) lit)[pos]!
    ∃ nextOriginal nextLearned,
      Database after nextOriginal nextLearned ∧ DatabaseMeaning formula nextOriginal nextLearned ∧
      WatchCertificate after (nextOriginal ++ nextLearned) (moveHeads heads newLit ref) ∧
      (∀ entry ∈ nextOriginal ++ nextLearned, entry.lits.toList.Nodup) ∧
      WatchCursor (moveHeads heads newLit ref) lit previous rest := by
  dsimp only
  have current := cursor.member
  have currentProper := certificate.references lit ref current
  obtain ⟨entry, member, id, wide⟩ := currentProper
  have prior : previous = 0 ∨ StoredWatchRef (original ++ learned) previous := by
    by_cases head : previous = 0
    · exact Or.inl head
    · exact Or.inr (certificate.references lit previous (cursor.previous_member head))
  obtain ⟨offset, afterWatches, within, position, nextDatabase, nextMeaning⟩ :=
    replacement_branch_database database meaning lit ref previous member id wide
      (certificate.entry database current) prior found
  let f := moveWatchEntry entry.id offset (s.db entry.id == lit)
  let newLit := (orientWatch s.arena (watchClause ref) lit)[pos]!
  let moved := { s with arena := moveWatch s.arena entry.id lit (entry.id + offset) }
  have packed := database.layout.packed member
  have selected : newLit = entry.lits[offset]! := by
    dsimp only [newLit]
    rw [id, orientWatch_read_other _ _ _ _ (by omega), position]
    exact packed.literals offset within
  have scan : replacement s.arena s.marks entry.id = some pos := by
    simpa only [id, replacement_orientWatch] using found
  have selectedUnmarked : s.mark newLit = 0 := by
    have unmarked := (replacementScan_some scan).2.2.2.1
    dsimp only [newLit]
    rw [id, orientWatch_read_other _ _ _ _ (by omega)]
    exact unmarked
  have different : lit ≠ newLit := fun same => falseLit ((congrArg s.mark same).trans selectedUnmarked)
  have selectedMember : entry.lits[offset]! ∈ entry.lits := by
    simpa only [getElem!_pos entry.lits offset within] using Array.getElem_mem within
  have selectedBound : LiteralBound s.nVars newLit := by
    rw [selected]
    exact packed.wellFormed _ selectedMember
  have watchedLiteral : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.entry database current).2.2.2
  have movedDatabase : Database moved (original.map f) (learned.map f) :=
    moveWatch_database database member lit offset afterWatches within watchedLiteral
  have movedLinks : ∀ other, WatchLinks moved other (heads other) := by
    intro other
    exact (certificate.links other).moveWatch database member lit offset afterWatches within watchedLiteral
      (certificate.references other)
  have movedProper : ∀ other old, old ∈ heads other →
      StoredWatchRef ((original.map f) ++ (learned.map f)) old := by
    intro other old oldMember
    rw [← List.map_append]
    exact (certificate.references other old oldMember).mapEntries f
      (moveWatchEntry_id _ _ _) (moveWatchEntry_size _ _ _)
  have rewiredLinks := rewireWatch_all_links movedDatabase movedLinks movedProper certificate.unique cursor different
    (arrays.literal_index literal).2 (arrays.literal_index selectedBound).2
  refine ⟨original.map f, learned.map f, nextDatabase, nextMeaning, ?_, ?_, ?_⟩
  · constructor
    · simpa only [moved, movedWatchArrays, newLit, id, position, restoreWatchArrays] using rewiredLinks
    · intro other old oldMember
      rw [← List.map_append]
      exact moveHeads_references (fun lit => (certificate.links lit).1) certificate.references newLit ref
        ⟨entry, member, id, wide⟩ f (moveWatchEntry_id _ _ _) (moveWatchEntry_size _ _ _) other old oldMember
    · have covered := moveWatch_covered database certificate member (nodup entry member) lit ref offset id current
        afterWatches within
      simpa only [List.map_append, ← selected] using covered
    · exact moveHeads_unique (fun lit => (certificate.links lit).1) certificate.unique newLit ref
  · intro changed changedMember
    rw [← List.map_append] at changedMember
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp changedMember
    exact moveWatchEntry_nodup _ _ _ old (nodup old oldMember)
  · exact cursor.move (certificate.links lit).1 different

end MicrosatLean.Verification.Implementation.Native.Propagation
