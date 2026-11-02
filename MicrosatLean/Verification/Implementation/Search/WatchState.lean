import MicrosatLean.Verification.Implementation.Bridge.FromNative
import MicrosatLean.Verification.Implementation.Logic.Execution
import MicrosatLean.Verification.Implementation.Native.Search.WatchRich

namespace MicrosatLean.Verification.Implementation.Search

open Bridge
open CDCL
private abbrev NEntry := Native.Representation.StoredClause

/-! Watch maintenance permutes database literals while keeping every active
reason in exactly its previous order. These lemmas record that distinction. -/

theorem nativeReason_map_frame (s : State) (entries : List NEntry)
    (arena first : Array Nat) (f : NEntry → NEntry)
    (ids : ∀ entry, (f entry).id = entry.id)
    (fixed : ∀ i, i < s.assigned → ∀ entry ∈ entries,
      entry.id = s.reason s.trail[i]! → f entry = entry)
    {i : Nat} (before : i < s.assigned) :
    nativeReason (restoreWatchArrays s arena first) (entries.map f) i =
      nativeReason s entries i := by
  simp only [nativeReason, restoreWatchArrays, State.reason]
  by_cases zero : s.reasons[s.trail[i]!.var]! = 0
  · simp only [zero, ↓reduceIte]
  · simp only [zero, ↓reduceIte]
    rw [List.find?_map]
    have predicate : (fun entry => (f entry).id == s.reasons[s.trail[i]!.var]!) =
        (fun entry => entry.id == s.reasons[s.trail[i]!.var]!) := by
      funext entry
      rw [ids]
    simp only [Function.comp_def] at *
    rw [predicate]
    cases selected : entries.find? (fun entry => entry.id == s.reasons[s.trail[i]!.var]!) with
    | none => rfl
    | some entry =>
      have same := fixed i before entry (List.mem_of_find?_eq_some selected)
        (by simpa only [State.reason, beq_iff_eq] using List.find?_some selected)
      simp only [Option.map_some, same]

theorem nativeState_watch_frame (s : State) (original learned : List NEntry)
    (arena first : Array Nat) (f : NEntry → NEntry)
    (ids : ∀ entry, (f entry).id = entry.id)
    (fixed : ∀ i, i < s.assigned → ∀ entry ∈ original ++ learned,
      entry.id = s.reason s.trail[i]! → f entry = entry) :
    nativeState (restoreWatchArrays s arena first) (original.map f) (learned.map f) =
      { nativeState s original learned with
        original := (original.map f).map Native.Representation.StoredClause.view,
        learned := (learned.map f).map Native.Representation.StoredClause.view } := by
  have trail : nativeTrail (restoreWatchArrays s arena first)
      (original.map f ++ learned.map f) = nativeTrail s (original ++ learned) := by
    apply List.ext_getElem (by simp only [nativeTrail_length, restoreWatchArrays])
    intro i leftBound rightBound
    have before : i < s.assigned := by simpa only [nativeTrail_length] using rightBound
    rw [← getElem!_pos _ i leftBound, ← getElem!_pos _ i rightBound,
      nativeTrail_get (restoreWatchArrays s arena first) _ before,
      nativeTrail_get s _ before, ← List.map_append,
      nativeReason_map_frame s _ arena first f ids fixed before]
    rfl
  change LogicalState.mk _ _ _ (nativeTrail (restoreWatchArrays s arena first) _ ) _ = _
  rw [trail]
  rfl

theorem clausePermutations_map (entries : List NEntry) (f : NEntry → NEntry)
    (perms : ∀ entry, (f entry).lits.Perm entry.lits) :
    ClausePermutations (entries.map Native.Representation.StoredClause.view) ((entries.map f).map Native.Representation.StoredClause.view) := by
  induction entries with
  | nil => trivial
  | cons entry rest ih =>
    refine ⟨?_, ih⟩
    simpa only [Native.Representation.StoredClause.view, MicrosatLean.Verification.clauseView_literals]
      using ((Array.perm_iff_toList_perm.mp (perms entry)).map literalView).symm

theorem watch_map_trace (input : CNF) (s : State) (original learned : List NEntry)
    (arena first : Array Nat) (f : NEntry → NEntry)
    (ids : ∀ entry, (f entry).id = entry.id)
    (perms : ∀ entry, (f entry).lits.Perm entry.lits)
    (fixed : ∀ i, i < s.assigned → ∀ entry ∈ original ++ learned,
      entry.id = s.reason s.trail[i]! → f entry = entry) :
    LogicalExecution input (nativeState s original learned)
      (nativeState (restoreWatchArrays s arena first) (original.map f) (learned.map f)) := by
  rw [nativeState_watch_frame s original learned arena first f ids fixed]
  exact Logic.single_move (.permute _ _ _
    (clausePermutations_map original f perms) (clausePermutations_map learned f perms))

theorem retained_trace {input : CNF} {s : State} {original learned : List NEntry}
    {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (falseLit : s.mark lit ≠ 0)
    {nextOriginal nextLearned : List NEntry}
    (database : Native.Representation.Database
      { s with arena := Native.Propagation.retainWatch s.arena (watchClause ref) lit }
      nextOriginal nextLearned) :
    LogicalExecution input (nativeState s original learned)
      (nativeState { s with arena := Native.Propagation.retainWatch s.arena (watchClause ref) lit }
        nextOriginal nextLearned) := by
  obtain ⟨target, member, id, wide⟩ := base.watches.references lit ref current
  have watched : s.db target.id = lit ∨ s.db (target.id + 1) = lit := by
    simpa only [id] using (base.watches.entry base.database current).2.2.2
  have exactDatabase := Native.Propagation.retainWatch_database base.database member lit wide watched
  rw [← id] at exactDatabase
  obtain ⟨rfl, rfl⟩ := database.unique exactDatabase
  apply watch_map_trace input s original learned _ s.first
    (Native.Propagation.retainWatchEntry (watchClause ref) (s.db (watchClause ref) == lit))
    (Native.Propagation.retainWatchEntry_id _ _) (Native.Propagation.retainWatchEntry_perm _ _)
  intro i before entry stored same
  by_cases different : entry.id ≠ watchClause ref
  · exact Native.Propagation.retainWatchEntry_of_ne _ _ _ different
  · have reason : s.reason s.trail[i]! = watchClause ref := same.symm.trans (by simpa using different)
    have nonzero : s.reason s.trail[i]! ≠ 0 := by
      have lower := (base.database.layout.packed member).startLower
      rw [reason, id]
      omega
    obtain ⟨lits, packed, nonempty, head, _, _⟩ := base.graph.clauses i before nonzero
    have first : s.db (watchClause ref) = s.trail[i]!.negate := by
      simpa only [reason, Nat.add_zero, head] using packed.literals 0 nonempty
    have unmarked : s.mark (s.db (watchClause ref)) = 0 := by
      rw [first]
      exact (base.active i before).2.2
    have notFirst : s.db (watchClause ref) ≠ lit :=
      fun equal => falseLit ((congrArg s.mark equal).symm.trans unmarked)
    have test : (s.db (watchClause ref) == lit) = false := by simp [notFirst]
    simp only [test, Native.Propagation.retainWatchEntry_false]

theorem moved_trace {input : CNF} {s : State} {original learned : List NEntry}
    {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    {lit : Lit} {previous ref pos : Nat} {rest : List Nat}
    (cursor : Native.Propagation.WatchCursor heads lit previous (ref :: rest))
    (found : replacement (Native.Propagation.orientWatch s.arena (watchClause ref) lit)
      s.marks (watchClause ref) = some pos)
    {nextOriginal nextLearned : List NEntry}
    (database : Native.Representation.Database
      (restoreWatchArrays s (Native.Propagation.movedWatchArrays s.arena s.first lit ref previous pos).1
        (Native.Propagation.movedWatchArrays s.arena s.first lit ref previous pos).2)
      nextOriginal nextLearned) :
    LogicalExecution input (nativeState s original learned)
      (nativeState
        (restoreWatchArrays s (Native.Propagation.movedWatchArrays s.arena s.first lit ref previous pos).1
          (Native.Propagation.movedWatchArrays s.arena s.first lit ref previous pos).2)
        nextOriginal nextLearned) := by
  obtain ⟨target, member, id, wide⟩ := base.watches.references lit ref cursor.member
  have prior : previous = 0 ∨ Native.Propagation.StoredWatchRef (original ++ learned) previous := by
    by_cases zero : previous = 0
    · exact Or.inl zero
    · exact Or.inr (base.watches.references lit previous (cursor.previous_member zero))
  obtain ⟨offset, _, _, _, exactDatabase, _⟩ :=
    Native.Propagation.replacement_branch_database base.database base.meaning lit ref previous member id wide
      (base.watches.entry base.database cursor.member) prior found
  obtain ⟨rfl, rfl⟩ := database.unique exactDatabase
  apply watch_map_trace input s original learned _ _
    (Native.Propagation.moveWatchEntry target.id offset (s.db target.id == lit))
    (Native.Propagation.moveWatchEntry_id _ _ _) (Native.Propagation.moveWatchEntry_perm _ _ _)
  intro i before entry stored same
  have scan : replacement (Native.Propagation.orientWatch s.arena target.id lit)
      s.marks target.id = some pos := by simpa only [id] using found
  have different : entry.id ≠ target.id := by
    rw [same]
    exact Native.Propagation.replacement_not_active_reason base.graph base.active (Nat.le_refl _)
      (base.database.layout.packed member) wide lit scan i before
  exact Native.Propagation.moveWatchEntry_of_ne _ _ _ _ different

end MicrosatLean.Verification.Implementation.Search
