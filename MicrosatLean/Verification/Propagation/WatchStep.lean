import MicrosatLean.Verification.Propagation.WatchMove

namespace MicrosatLean.Verification.Propagation

open CDCL Representation Std.Sat

@[simp] theorem restoreWatchArrays_mark (s : State) (arena first : Array Nat) (lit : Lit) :
    (restoreWatchArrays s arena first).mark lit = s.mark lit := rfl

/-- A proper watch reference belongs to a genuine long stored clause, rather
than to an arbitrary zero-terminated suffix in the arena. -/
def StoredWatchRef (entries : List StoredClause) (ref : Nat) : Prop :=
  ∃ entry ∈ entries, watchClause ref = entry.id ∧ 2 ≤ entry.lits.size

theorem StoredWatchRef.mapEntries {entries : List StoredClause} {ref : Nat}
    (proper : StoredWatchRef entries ref) (f : StoredClause → StoredClause)
    (ids : ∀ entry, (f entry).id = entry.id) (sizes : ∀ entry, (f entry).lits.size = entry.lits.size) :
    StoredWatchRef (entries.map f) ref := by
  obtain ⟨entry, member, id, wide⟩ := proper
  exact ⟨f entry, List.mem_map.mpr ⟨entry, member, rfl⟩,
    id.trans (ids entry).symm, by simpa only [sizes] using wide⟩

/-- The exact link-cell and head writes performed after moving a literal. -/
def rewireWatch (arena first : Array Nat) (lit newLit : Lit) (ref previous : Nat) : Array Nat × Array Nat :=
  let nextRef := arena[watchLinkPos ref]!
  let (arena, first) := if previous == 0 then (arena, first.set! lit nextRef)
    else (arena.set! (watchLinkPos previous) nextRef, first)
  (arena.set! (watchLinkPos ref) first[newLit]!, first.set! newLit ref)

private theorem proper_link {ref : Nat} {entry : StoredClause} (id : watchClause ref = entry.id) :
    watchLinkPos ref = entry.id - 2 + ref % 2 := by
  simpa only [watchLinkPos, watchClause] using congrArg (fun id => id - 2 + ref % 2) id

theorem rewireWatch_database {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (lit newLit : Lit) (ref previous : Nat)
    (proper : StoredWatchRef (original ++ learned) ref)
    (prior : previous = 0 ∨ StoredWatchRef (original ++ learned) previous) :
    Database (restoreWatchArrays s (rewireWatch s.arena s.first lit newLit ref previous).1
      (rewireWatch s.arena s.first lit newLit ref previous).2) original learned := by
  obtain ⟨entry, member, id, _⟩ := proper
  have link := proper_link id
  have slot : ref % 2 ≤ 1 := by omega
  by_cases head : previous = 0
  · have updated := database.setHeader member (ref % 2)
      (s.first.set! lit s.arena[watchLinkPos ref]!)[newLit]! slot
    apply updated.frame
    · simp only [restoreWatchArrays, rewireWatch, head, beq_self_eq_true, ite_true, link]
    · rfl
    · rfl
    · rfl
  · obtain ⟨before, beforeMember, beforeId, _⟩ := prior.resolve_left head
    have beforeLink := proper_link beforeId
    have previousSlot : previous % 2 ≤ 1 := by omega
    have detached := database.setHeader beforeMember (previous % 2) s.arena[watchLinkPos ref]! previousSlot
    have updated := detached.setHeader member (ref % 2) s.first[newLit]! slot
    apply updated.frame
    · simp only [restoreWatchArrays, rewireWatch, beq_iff_eq, head, ite_false, link, beforeLink]
    · rfl
    · rfl
    · rfl

def currentWatchRef (arena first : Array Nat) (lit : Lit) (previous : Nat) : Nat :=
  if previous == 0 then first[lit]! else arena[watchLinkPos previous]!

def movedWatchArrays (arena first : Array Nat) (lit : Lit) (ref previous pos : Nat) : Array Nat × Array Nat :=
  rewireWatch (moveWatch arena (watchClause ref) lit pos) first lit
    (orientWatch arena (watchClause ref) lit)[pos]! ref previous

/-- This is an equation for the actual executable transition, not an abstract
replacement operation. It exposes exactly the recursive call's new arrays. -/
theorem propagateWatches_replacement (fuel : Nat) (s : State) (arena first : Array Nat)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous pos : Nat)
    (nonzero : currentWatchRef arena first lit previous ≠ 0)
    (found : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
      s.marks (watchClause (currentWatchRef arena first lit previous)) = some pos) :
    propagateWatches (fuel + 1) s arena first decision oldLemmas root lit previous =
      let arrays := movedWatchArrays arena first lit (currentWatchRef arena first lit previous) previous pos
      propagateWatches fuel s arrays.1 arrays.2 decision oldLemmas root lit previous := by
  simp only [currentWatchRef, beq_iff_eq] at nonzero
  simp only [currentWatchRef, orientWatch, beq_iff_eq] at found
  simp only [propagateWatches, currentWatchRef, orientWatch, moveWatch, movedWatchArrays,
    rewireWatch, Id.run, pure, beq_iff_eq, nonzero, ite_false, found]

/-- A successful actual replacement branch preserves a proper packed database
up to the exact source-order literal permutation and preserves input models.
Both current and previous refs name genuine stored clauses; no poststate
database, propagation closure, or semantic reason premise is assumed. -/
theorem replacement_branch_database {s : State} {formula : CNF Nat}
    {original learned : List StoredClause} (database : Database s original learned)
    (meaning : DatabaseMeaning formula original learned) (lit : Lit) (ref previous : Nat)
    {entry : StoredClause} (member : entry ∈ original ++ learned) (id : watchClause ref = entry.id)
    (wide : 2 ≤ entry.lits.size) (watched : WatchEntry s lit ref)
    (prior : previous = 0 ∨ StoredWatchRef (original ++ learned) previous) {pos : Nat}
    (found : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = some pos) :
    ∃ offset, 2 ≤ offset ∧ offset < entry.lits.size ∧ pos = entry.id + offset ∧
      let f := moveWatchEntry entry.id offset (s.db entry.id == lit)
      let arrays := movedWatchArrays s.arena s.first lit ref previous pos
      Database (restoreWatchArrays s arrays.1 arrays.2) (original.map f) (learned.map f) ∧
        DatabaseMeaning formula (original.map f) (learned.map f) := by
  have scan : replacement (orientWatch s.arena entry.id lit) s.marks entry.id = some pos := by
    simpa only [id] using found
  obtain ⟨offset, afterWatches, within, position, _⟩ :=
    replacement_orientWatch_some (database.layout.packed member) wide lit scan
  refine ⟨offset, afterWatches, within, position, ?_⟩
  let f := moveWatchEntry entry.id offset (s.db entry.id == lit)
  have watchedLiteral : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit := by
    simpa only [id] using watched.2.2.2
  have moved := moveWatch_database database member lit offset afterWatches within watchedLiteral
  have updatedRef : StoredWatchRef ((original.map f) ++ (learned.map f)) ref := by
    rw [← List.map_append]
    exact StoredWatchRef.mapEntries ⟨entry, member, id, wide⟩ f
      (moveWatchEntry_id _ _ _) (moveWatchEntry_size _ _ _)
  have updatedPrior : previous = 0 ∨ StoredWatchRef ((original.map f) ++ (learned.map f)) previous := by
    rcases prior with head | before
    · exact Or.inl head
    · right
      rw [← List.map_append]
      exact before.mapEntries f (moveWatchEntry_id _ _ _) (moveWatchEntry_size _ _ _)
  have rewired := rewireWatch_database moved lit
    (orientWatch s.arena entry.id lit)[pos]! ref previous updatedRef updatedPrior
  constructor
  · simpa only [movedWatchArrays, id, position, restoreWatchArrays] using rewired
  · exact moveWatch_databaseMeaning meaning entry.id offset (s.db entry.id == lit)

end MicrosatLean.Verification.Propagation
