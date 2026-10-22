import MicrosatLean.Verification.Propagation.WatchUnit
import MicrosatLean.Verification.Propagation.WatchMovement

namespace MicrosatLean.Verification.Propagation

open CDCL Representation Std.Sat

theorem clauseWatches_symm {heads : Nat → List Nat} {id first second : Nat}
    (covered : ClauseWatches heads id first second) : ClauseWatches heads id second first := by
  refine ⟨Ne.symm covered.1, ?_⟩
  rcases covered.2 with forward | backward
  · exact Or.inr forward
  · exact Or.inl backward

/-- Completing the temporary orientation without moving a watch preserves
every list and its ownership certificate, including when the two literals swap. -/
theorem retainWatch_certificate {s : State} {formula : CNF Nat}
    {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    (nodup : ∀ entry ∈ original ++ learned, entry.lits.toList.Nodup)
    (lit : Lit) (ref : Nat) (current : ref ∈ heads lit) :
    let after := { s with arena := retainWatch s.arena (watchClause ref) lit }
    ∃ nextOriginal nextLearned, Database after nextOriginal nextLearned ∧
      DatabaseMeaning formula nextOriginal nextLearned ∧ WatchCertificate after (nextOriginal ++ nextLearned) heads ∧
      (∀ entry ∈ nextOriginal ++ nextLearned, entry.lits.toList.Nodup) := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := certificate.references lit ref current
  let f := retainWatchEntry entry.id (s.db entry.id == lit)
  have packed := database.layout.packed member
  have watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.entry database current).2.2.2
  have nextDatabase := retainWatch_database database member lit wide watched
  have nextMeaning := retainWatch_databaseMeaning meaning entry.id (s.db entry.id == lit)
  refine ⟨original.map f, learned.map f, ?_, nextMeaning, ?_, ?_⟩
  · simpa only [id] using nextDatabase
  · constructor
    · intro other
      have bound : entry.id + 1 < s.arena.size := by have := packed.endBound; omega
      rw [id, retainWatch_eq_swap _ _ _ bound watched]
      by_cases first : s.arena[entry.id]! = lit
      · have moved := (certificate.links other).swapLiterals database member 0 1 (by omega) (by omega)
          (certificate.references other)
        simpa only [first, beq_self_eq_true, ite_true, Nat.add_zero] using moved
      · simpa only [beq_iff_eq, first, ite_false] using certificate.links other
    · intro other old oldMember
      rw [← List.map_append]
      exact (certificate.references other old oldMember).mapEntries f (retainWatchEntry_id _ _)
        (retainWatchEntry_size _ _)
    · intro changed changedMember changedWide
      rw [← List.map_append] at changedMember
      obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp changedMember
      by_cases same : old.id = entry.id
      · have equal := database.layout.entry_eq_of_id oldMember member same
        subst old
        have covered := certificate.covered entry member wide
        have pair := retainWatchEntry_heads entry (s.db entry.id == lit) wide
        change ClauseWatches heads (f entry).id (f entry).lits[0]! (f entry).lits[1]!
        dsimp only [f]
        rw [retainWatchEntry_id, pair.1, pair.2]
        split
        · exact clauseWatches_symm covered
        · exact covered
      · have unchanged : f old = old := retainWatchEntry_of_ne _ _ _ same
        simpa only [unchanged] using certificate.covered old oldMember (by
          simpa only [f, retainWatchEntry_size] using changedWide)
    · exact certificate.unique
  · intro changed changedMember
    rw [← List.map_append] at changedMember
    obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp changedMember
    exact (Array.perm_iff_toList_perm.mp (retainWatchEntry_perm entry.id (s.db entry.id == lit) old)).symm.nodup
      (nodup old oldMember)

theorem propagateWatches_skip (fuel : Nat) (s : State) (arena first : Array Nat)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat)
    (nonzero : currentWatchRef arena first lit previous ≠ 0)
    (missing : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
      s.marks (watchClause (currentWatchRef arena first lit previous)) = none)
    (satisfied : s.mark (Lit.negate ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) ≠ 0) :
    propagateWatches (fuel + 1) s arena first decision oldLemmas root lit previous =
      propagateWatches fuel s (retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
        first decision oldLemmas root lit (currentWatchRef arena first lit previous) := by
  simp only [currentWatchRef, beq_iff_eq] at nonzero
  simp only [currentWatchRef, orientWatch, beq_iff_eq] at missing
  simp only [currentWatchRef, retainWatch, orientWatch, beq_iff_eq, ne_eq] at satisfied
  simp only [propagateWatches, currentWatchRef, retainWatch, orientWatch, Id.run, pure,
    beq_iff_eq, nonzero, ite_false, missing, bne_iff_ne, ne_eq, satisfied, not_false_eq_true, ite_true]

end MicrosatLean.Verification.Propagation
