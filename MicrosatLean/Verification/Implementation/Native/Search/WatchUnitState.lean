import MicrosatLean.Verification.Implementation.Native.Search.WatchState
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchSettlementVisit

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- In a root propagation invocation every active false literal is an input
consequence, as witnessed by its genuine tag-six trail entry. -/
def RootWatchTrail (s : State) (root : Bool) : Prop :=
  root = true → ∀ i, i < s.assigned → s.mark s.trail[i]! = 6

theorem StateCertificate.root_unit_consequence {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    {entry : StoredClause} (member : entry ∈ original ++ learned)
    (unit : ∀ lit ∈ entry.lits, lit ≠ s.db entry.id → s.mark lit ≠ 0)
    (rootTags : ∀ i, i < s.assigned → s.mark s.trail[i]! = 6) :
    ∀ a, CNF.Sat a formula → Falsifies a (Lit.negate (s.db entry.id)) := by
  intro a model
  apply (falsifies_negate_iff a _).mpr
  apply head_true_of_unit (certificate.meaning.entails_entry member) certificate.marked unit model
  intro i before
  exact certificate.roots _ ⟨i, before, rfl⟩ (rootTags i before) a model

/-- A failed actual replacement and the two unmarked-other tests supply all
semantic and structural premises of the real unit assignment. -/
theorem StateCertificate.watchUnit {formula : CNF Nat} {s : State}
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
      (DecisionHistory s (original ++ learned) → DecisionHistory after (nextOriginal ++ nextLearned)) := by
  dsimp only
  obtain ⟨entry, member, id, wide⟩ := certificate.watches.references lit ref current
  have watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.watches.entry certificate.database current).2.2.2
  have exactDatabase := retainWatch_database certificate.database member lit wide watched
  rw [← id] at exactDatabase
  obtain ⟨nextOriginal, nextLearned, retainedCertificate, retainedHistory⟩ :=
    certificate.retainWatch current falseLit
  obtain ⟨sameOriginal, sameLearned⟩ := retainedCertificate.database.unique exactDatabase
  subst nextOriginal nextLearned
  let f := retainWatchEntry (watchClause ref) (s.db (watchClause ref) == lit)
  let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
  have mapped : f entry ∈ original.map f ++ learned.map f := by
    rw [← List.map_append]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have packed := retainedCertificate.database.layout.packed mapped
  have packedId : (f entry).id = watchClause ref := (retainWatchEntry_id _ _ _).trans id.symm
  have packedWide : 2 ≤ (f entry).lits.size := by simpa only [f, retainWatchEntry_size] using wide
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
  have tails : ∀ j, 0 < j → j < (f entry).lits.size →
      TrailMember retained retained.assigned (f entry).lits[j]! := by
    intro j positive before
    apply retainedCertificate.marked
    by_cases one : j = 1
    · simpa only [one] using secondFalse
    · exact replacement_none_of_packed packed missingRetained (by omega) before
  have nonempty : 0 < (f entry).lits.size := by omega
  have rootSound : root = true → ∀ a, CNF.Sat a formula →
      Falsifies a (Lit.negate (retained.db (f entry).id)) := by
    intro rootTrue
    exact retainedCertificate.root_unit_consequence mapped unit (rootTrail rootTrue)
  have headZero : retained.mark (retained.db (f entry).id) = 0 := by
    simpa only [packedId, retained, State.mark, State.db] using head
  have oppositeZero : retained.mark (Lit.negate (retained.db (f entry).id)) = 0 := by
    simpa only [packedId, retained, State.mark, State.db] using opposite
  have afterCertificate := retainedCertificate.assign (f entry) mapped nonempty tails headZero oppositeZero root rootSound
  refine ⟨original.map f, learned.map f,
    extendTrailRank rank (Lit.var (retained.db (watchClause ref))) s.assigned, ?_, ?_⟩
  · simpa only [packedId, retained] using afterCertificate
  · intro history
    have nextHistory := retainedHistory history
    have space : retained.assigned < retained.trail.size := by
      change s.assigned < s.trail.size
      rw [certificate.arrays.trailSize]
      have assigned := certificate.bounds.assignedVars
      omega
    have first := packed.literals 0 nonempty
    simp only [Nat.add_zero] at first
    have literal : LiteralBound retained.nVars (retained.db (f entry).id) := by
      rw [first]
      apply packed.wellFormed
      simpa only [getElem!_pos (f entry).lits 0 nonempty] using Array.getElem_mem nonempty
    have next := DecisionHistory.assign nextHistory (f entry).id root (by have := packed.startLower; omega)
      space (retainedCertificate.arrays.variable_index literal.2).1
      (freshVariable_of_unmarked_literal retainedCertificate.active headZero oppositeZero)
    simpa only [packedId, retained] using next

end MicrosatLean.Verification.Implementation.Native.Search
