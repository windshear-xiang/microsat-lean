import MicrosatLean.Verification.Implementation.Native.Propagation.WatchSettlementMove

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation Analysis

theorem retainedEntry_watches (entry : StoredClause) (lit : Lit)
    (wide : 2 ≤ entry.lits.size) (distinct : entry.lits[0]! ≠ entry.lits[1]!)
    (watched : lit = entry.lits[0]! ∨ lit = entry.lits[1]!) :
    let after := retainWatchEntry entry.id (entry.lits[0]! == lit) entry
    after.lits[0]! ≠ lit ∧ after.lits[1]! = lit := by
  dsimp only
  have pair := retainWatchEntry_heads entry (entry.lits[0]! == lit) wide
  rw [pair.1, pair.2]
  by_cases first : entry.lits[0]! = lit
  · have different : entry.lits[1]! ≠ lit := fun equal => distinct (first.trans equal.symm)
    simpa only [first, beq_self_eq_true, ite_true, and_true] using different
  · have second : lit = entry.lits[1]! := watched.resolve_left (Ne.symm first)
    simpa only [beq_iff_eq, first, ite_false] using ⟨first, second.symm⟩

theorem settledWatch_of_second {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {entry : StoredClause}
    (member : entry ∈ original ++ learned) {lit : Lit} {ref : Nat}
    (id : watchClause ref = entry.id) (head : entry.lits[0]! ≠ lit)
    (truth : TrueBefore s s.assigned entry.lits[0]!) :
    SettledWatch s (original ++ learned) s.assigned lit ref := by
  intro other otherMember otherId
  have equal := database.layout.entry_eq_of_id otherMember member (otherId.symm.trans id)
  subst other
  simpa only [otherWatch, beq_iff_eq, head, ite_false] using truth

/-- The actual satisfied-other-watch mark test supplies the new visit's
concrete trail truth witness after the exact orientation writes. -/
theorem retainWatch_settled_of_marked {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (marked : MarkedOnTrail s)
    {entry : StoredClause} (member : entry ∈ original ++ learned)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (id : watchClause ref = entry.id)
    (wide : 2 ≤ entry.lits.size)
    (truth : s.mark (Lit.negate ((retainWatch s.arena entry.id lit)[entry.id]!)) ≠ 0) :
    let f := retainWatchEntry entry.id (s.db entry.id == lit)
    let after := { s with arena := retainWatch s.arena entry.id lit }
    SettledWatch after ((original ++ learned).map f) after.assigned lit ref := by
  dsimp only
  let f := retainWatchEntry entry.id (s.db entry.id == lit)
  let after := { s with arena := retainWatch s.arena entry.id lit }
  have packed := database.layout.packed member
  have headRead : s.db entry.id = entry.lits[0]! := by simpa using packed.literals 0 (by omega)
  have watched := watch_ref_literals database certificate member current id wide
  have watchedRaw : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.entry database current).2.2.2
  have nextDatabase : Database after (original.map f) (learned.map f) :=
    retainWatch_database database member lit wide watchedRaw
  have nextMember : f entry ∈ original.map f ++ learned.map f := by
    rw [← List.map_append]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have pair : (f entry).lits[0]! ≠ lit ∧ (f entry).lits[1]! = lit := by
    simpa only [f, headRead] using retainedEntry_watches entry lit wide
      (certificate.covered entry member wide).1 watched
  have nextPacked := nextDatabase.layout.packed nextMember
  have nextRead : after.db entry.id = (f entry).lits[0]! := by
    simpa only [f, retainWatchEntry_id, Nat.add_zero] using nextPacked.literals 0 (by simpa [f] using (show 0 < entry.lits.size by omega))
  have nextTruth : TrueBefore after after.assigned (f entry).lits[0]! := by
    rw [← nextRead]
    exact trueBefore_of_marked (s := after) marked truth
  have settled := settledWatch_of_second nextDatabase nextMember (by simpa [f] using id) pair.1 nextTruth
  simpa only [List.map_append] using settled

/-- The real unit assignment appends precisely the true opposite watch, so
the just-visited reference is settled in its returned state. -/
theorem retainWatch_settled_of_assign {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    {entry : StoredClause} (member : entry ∈ original ++ learned)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (id : watchClause ref = entry.id)
    (wide : 2 ≤ entry.lits.size) (root : Bool) (space : s.assigned < s.trail.size) :
    let f := retainWatchEntry entry.id (s.db entry.id == lit)
    let retained := { s with arena := retainWatch s.arena entry.id lit }
    let after := retained.assign entry.id root
    SettledWatch after ((original ++ learned).map f) after.assigned lit ref := by
  dsimp only
  let f := retainWatchEntry entry.id (s.db entry.id == lit)
  let retained := { s with arena := retainWatch s.arena entry.id lit }
  let after := retained.assign entry.id root
  have packed := database.layout.packed member
  have headRead : s.db entry.id = entry.lits[0]! := by simpa using packed.literals 0 (by omega)
  have watched := watch_ref_literals database certificate member current id wide
  have watchedRaw : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using (certificate.entry database current).2.2.2
  have retainedDatabase : Database retained (original.map f) (learned.map f) :=
    retainWatch_database database member lit wide watchedRaw
  have nextDatabase : Database after (original.map f) (learned.map f) :=
    retainedDatabase.assign entry.id root
  have nextMember : f entry ∈ original.map f ++ learned.map f := by
    rw [← List.map_append]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have pair : (f entry).lits[0]! ≠ lit ∧ (f entry).lits[1]! = lit := by
    simpa only [f, headRead] using retainedEntry_watches entry lit wide
      (certificate.covered entry member wide).1 watched
  have nextPacked := retainedDatabase.layout.packed nextMember
  have nextRead : retained.db entry.id = (f entry).lits[0]! := by
    simpa only [f, retainWatchEntry_id, Nat.add_zero] using nextPacked.literals 0 (by simpa [f] using (show 0 < entry.lits.size by omega))
  have nextTruth : TrueBefore after after.assigned (f entry).lits[0]! := by
    refine ⟨s.assigned, by simp [after, retained, State.assign], ?_⟩
    have last : after.trail[s.assigned]! = Lit.negate (retained.db entry.id) :=
      assign_trail_last (s := retained) (root := root) space
    exact last.trans (congrArg Lit.negate nextRead)
  have settled := settledWatch_of_second nextDatabase nextMember (by simpa [f] using id) pair.1 nextTruth
  simpa only [List.map_append] using settled

end MicrosatLean.Verification.Implementation.Native.Propagation
