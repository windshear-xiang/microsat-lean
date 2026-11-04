import MicrosatLean.Verification.Implementation.Search.Concrete.WatchUnitState
import MicrosatLean.Verification.Implementation.Search.Concrete.AnalysisState

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Analysis Std.Sat

/-- The real failed scan and false remaining watch establish an all-false
genuine stored clause after the exact orientation writes. -/
theorem StateCertificate.retainedConflict {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (falseLit : s.mark lit ≠ 0)
    (missing : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = none)
    (head : s.mark ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!) ≠ 0) :
    let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    ∃ nextOriginal nextLearned conflict,
      StateCertificate formula retained nextOriginal nextLearned heads rank ∧
      (DecisionHistory s (original ++ learned) → DecisionHistory retained (nextOriginal ++ nextLearned)) ∧
      conflict ∈ nextOriginal ++ nextLearned ∧ conflict.id = watchClause ref ∧
      ∀ lit ∈ conflict.lits, retained.mark lit ≠ 0 := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := certificate.watches.references lit ref current
  have watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.watches.entry certificate.database current).2.2.2
  have exactDatabase := retainWatch_database certificate.database member lit wide watched
  rw [← id] at exactDatabase
  obtain ⟨nextOriginal, nextLearned, retainedCertificate, retainedHistory⟩ := certificate.retainWatch current falseLit
  obtain ⟨sameOriginal, sameLearned⟩ := retainedCertificate.database.unique exactDatabase
  subst nextOriginal nextLearned
  let f := retainWatchEntry (watchClause ref) (s.db (watchClause ref) == lit)
  let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
  have mapped : f entry ∈ original.map f ++ learned.map f := by
    rw [← List.map_append]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have packed := retainedCertificate.database.layout.packed mapped
  have packedId : (f entry).id = watchClause ref := (retainWatchEntry_id _ _ _).trans id.symm
  have missingRetained : replacement retained.arena retained.marks (f entry).id = none := by
    rw [packedId]
    exact (replacement_retainWatch _ _ _ _).trans missing
  have second : (f entry).lits[1]! = lit := by
    have oldPacked := certificate.database.layout.packed member
    have oldHead : s.db entry.id = entry.lits[0]! := by simpa using oldPacked.literals 0 (by omega)
    have pair := retainedEntry_watches entry lit wide (certificate.watches.covered entry member wide).1
      (watch_ref_literals certificate.database certificate.watches member current id wide)
    simpa only [f, id, oldHead] using pair.2
  have secondFalse : retained.mark (f entry).lits[1]! ≠ 0 := by
    change s.mark (f entry).lits[1]! ≠ 0
    rw [second]
    exact falseLit
  have unit := unit_of_replacement_none packed missingRetained secondFalse
  refine ⟨_, _, f entry, retainedCertificate, retainedHistory, mapped, packedId, ?_⟩
  intro query queryMember
  by_cases first : query = retained.db (f entry).id
  · simpa only [first, packedId, retained, State.mark, State.db] using head
  · exact unit query queryMember first

theorem StateCertificate.root_conflict_unsat {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (rootTags : ∀ i, i < s.assigned → s.mark s.trail[i]! = 6)
    {conflict : StoredClause} (member : conflict ∈ original ++ learned)
    (falseClause : ∀ lit ∈ conflict.lits, s.mark lit ≠ 0) : CNF.Unsat formula := by
  apply Logic.unsat_of_root_conflict (certificate.meaning.entails_entry member)
  intro a model viewed contains
  obtain ⟨lit, litMember, equal⟩ := clauseView_mem.mp contains
  obtain ⟨i, before, value⟩ := certificate.marked lit (falseClause lit litMember)
  have six : s.mark lit = 6 := by rw [← value]; exact rootTags i before
  have falsified := certificate.roots lit ⟨i, before, value⟩ six a model
  simpa only [Falsifies, equal] using falsified

end MicrosatLean.Verification.Implementation.Search.Concrete
