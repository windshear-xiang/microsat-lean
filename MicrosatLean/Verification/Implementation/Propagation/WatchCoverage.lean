import MicrosatLean.Verification.Implementation.Propagation.WatchHeads

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL Representation

theorem clauseWatches_moveHeads_other {heads : Nat → List Nat} (nodup : ∀ lit, (heads lit).Nodup)
    {id first second target ref newLit : Nat} (covered : ClauseWatches heads id first second)
    (refId : watchClause ref = target) (different : id ≠ target) :
    ClauseWatches (moveHeads heads newLit ref) id first second := by
  have even : 2 * id ≠ ref := by simp only [watchClause] at refId; omega
  have odd : 2 * id + 1 ≠ ref := by simp only [watchClause] at refId; omega
  refine ⟨covered.1, ?_⟩
  rcases covered.2 with forward | backward
  · exact Or.inl ⟨(moveHeads_other_mem_iff nodup _ _ _ _ even).mpr forward.1,
      (moveHeads_other_mem_iff nodup _ _ _ _ odd).mpr forward.2⟩
  · exact Or.inr ⟨(moveHeads_other_mem_iff nodup _ _ _ _ even).mpr backward.1,
      (moveHeads_other_mem_iff nodup _ _ _ _ odd).mpr backward.2⟩

/-- The moved slot belongs at the new literal; unique ownership identifies
the retained slot's old head regardless of the two slots' current order. -/
theorem clauseWatches_moveHeads_target {heads : Nat → List Nat} (nodup : ∀ lit, (heads lit).Nodup)
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    {id first second lit ref newLit : Nat} (covered : ClauseWatches heads id first second)
    (refId : watchClause ref = id) (current : ref ∈ heads lit)
    (different : (if first == lit then second else first) ≠ newLit) :
    ClauseWatches (moveHeads heads newLit ref) id (if first == lit then second else first) newLit := by
  have encoding : ref = 2 * id ∨ ref = 2 * id + 1 := by simp only [watchClause] at refId; omega
  have moved : ref ∈ moveHeads heads newLit ref newLit :=
    (moveHeads_moved_mem_iff nodup _ _ _).mpr rfl
  refine ⟨different, ?_⟩
  rcases encoding with even | odd
  · subst ref
    right
    refine ⟨moved, ?_⟩
    rcases covered.2 with forward | backward
    · have same := unique lit first _ current forward.1
      simpa only [same, beq_self_eq_true, ite_true] using
        (moveHeads_other_mem_iff nodup _ _ _ _ (by omega : 2 * id + 1 ≠ 2 * id)).mpr forward.2
    · have same := unique lit second _ current backward.1
      have ne : (first == second) = false := by simp [covered.1]
      simpa only [same, ne, Bool.false_eq_true, ite_false] using
        (moveHeads_other_mem_iff nodup _ _ _ _ (by omega : 2 * id + 1 ≠ 2 * id)).mpr backward.2
  · subst ref
    left
    refine ⟨?_, moved⟩
    rcases covered.2 with forward | backward
    · have same := unique lit second _ current forward.2
      have ne : (first == second) = false := by simp [covered.1]
      simpa only [same, ne, Bool.false_eq_true, ite_false] using
        (moveHeads_other_mem_iff nodup _ _ _ _ (by omega : 2 * id ≠ 2 * id + 1)).mpr forward.1
    · have same := unique lit first _ current backward.2
      simpa only [same, beq_self_eq_true, ite_true] using
        (moveHeads_other_mem_iff nodup _ _ _ _ (by omega : 2 * id ≠ 2 * id + 1)).mpr backward.1

theorem moveWatch_covered {s : State} {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (certificate : WatchCertificate s (original ++ learned) heads)
    {entry : StoredClause} (member : entry ∈ original ++ learned) (nodup : entry.lits.toList.Nodup)
    (lit : Lit) (ref offset : Nat) (refId : watchClause ref = entry.id) (current : ref ∈ heads lit)
    (afterWatches : 2 ≤ offset) (within : offset < entry.lits.size) :
    let f := moveWatchEntry entry.id offset (s.db entry.id == lit)
    let updated := moveHeads heads entry.lits[offset]! ref
    ∀ changed ∈ (original ++ learned).map f, 2 ≤ changed.lits.size →
      ClauseWatches updated changed.id changed.lits[0]! changed.lits[1]! := by
  dsimp only
  let f := moveWatchEntry entry.id offset (s.db entry.id == lit)
  have packed := database.layout.packed member
  have head : s.db entry.id = entry.lits[0]! := by simpa using packed.literals 0 (by omega)
  have distinct : (if entry.lits[0]! == lit then entry.lits[1]! else entry.lits[0]!) ≠ entry.lits[offset]! := by
    split
    · exact literal_at_ne_of_nodup nodup (by omega) within (by omega)
    · exact literal_at_ne_of_nodup nodup (by omega) within (by omega)
  have targetCovered := clauseWatches_moveHeads_target (fun lit => (certificate.links lit).1)
    certificate.unique (certificate.covered entry member (by omega)) refId current distinct
  have targetHeads := moveWatchEntry_heads entry offset (s.db entry.id == lit) afterWatches within
  intro changed changedMember wide
  obtain ⟨old, oldMember, rfl⟩ := List.mem_map.mp changedMember
  by_cases same : old.id = entry.id
  · have equal := database.layout.entry_eq_of_id oldMember member same
    subst old
    rw [moveWatchEntry_id, targetHeads.1, targetHeads.2]
    simpa only [head] using targetCovered
  · have unchanged : moveWatchEntry entry.id offset (s.db entry.id == lit) old = old :=
      moveWatchEntry_of_ne _ _ _ _ same
    have oldWide : 2 ≤ old.lits.size := by simpa only [moveWatchEntry_size] using wide
    simpa only [unchanged] using clauseWatches_moveHeads_other (fun lit => (certificate.links lit).1)
      (newLit := entry.lits[offset]!) (certificate.covered old oldMember oldWide) refId same

end MicrosatLean.Verification.Implementation.Propagation
