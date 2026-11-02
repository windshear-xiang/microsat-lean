import MicrosatLean.Verification.Implementation.Native.Propagation.WatchStep
import MicrosatLean.Verification.Implementation.Native.Propagation.Unit

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation Std.Sat

/-- The exact watched-literal writes when no replacement is available. -/
def retainWatch (arena : Array Nat) (id : Nat) (lit : Lit) : Array Nat :=
  (orientWatch arena id lit).set! (id + 1) lit

theorem retainWatch_eq_swap (arena : Array Nat) (id : Nat) (lit : Lit)
    (bound : id + 1 < arena.size) (watched : arena[id]! = lit ∨ arena[id + 1]! = lit) :
    retainWatch arena id lit = if arena[id]! == lit then arena.swapIfInBounds id (id + 1) else arena := by
  have headBound : id < arena.size := by omega
  by_cases first : arena[id]! = lit
  · simp only [retainWatch, orientWatch, first, beq_self_eq_true, ite_true]
    apply Array.ext
    · simp
    · intro i before after
      have original : i < arena.size := by simpa using before
      rw [← getElem!_pos _ i before, ← getElem!_pos _ i after,
        set_read _ _ _ _ (by simpa using bound), set_read _ _ _ _ headBound,
        swap_read _ _ _ _ headBound bound original]
      by_cases atHead : i = id <;> by_cases atSecond : i = id + 1 <;> simp_all [eq_comm]
  · have second := watched.resolve_left first
    simp only [retainWatch, orientWatch, beq_iff_eq, first, ite_false]
    apply Array.ext
    · simp
    · intro i before after
      rw [← getElem!_pos _ i before, ← getElem!_pos _ i after, set_read _ _ _ _ bound]
      by_cases atSecond : i = id + 1 <;> simp_all [eq_comm]

def retainWatchEntry (id : Nat) (first : Bool) (entry : StoredClause) : StoredClause :=
  if first then swapEntry id 0 1 entry else entry

@[simp] theorem retainWatchEntry_true (id : Nat) : retainWatchEntry id true = swapEntry id 0 1 := rfl
@[simp] theorem retainWatchEntry_false (id : Nat) : retainWatchEntry id false = (fun entry => entry) := rfl

@[simp] theorem retainWatchEntry_id (id : Nat) (first : Bool) (entry : StoredClause) :
    (retainWatchEntry id first entry).id = entry.id := by cases first <;> simp [retainWatchEntry]

@[simp] theorem retainWatchEntry_size (id : Nat) (first : Bool) (entry : StoredClause) :
    (retainWatchEntry id first entry).lits.size = entry.lits.size := by cases first <;> simp [retainWatchEntry]

theorem retainWatchEntry_of_ne (id : Nat) (first : Bool) (entry : StoredClause) (different : entry.id ≠ id) :
    retainWatchEntry id first entry = entry := by cases first <;> simp [retainWatchEntry, swapEntry, different]

theorem retainWatchEntry_perm (id : Nat) (first : Bool) (entry : StoredClause) :
    (retainWatchEntry id first entry).lits.Perm entry.lits := by
  cases first
  · exact .refl _
  · exact swapEntry_perm _ _ _ _

theorem retainWatchEntry_heads (entry : StoredClause) (first : Bool) (wide : 2 ≤ entry.lits.size) :
    (retainWatchEntry entry.id first entry).lits[0]! = (if first then entry.lits[1]! else entry.lits[0]!) ∧
      (retainWatchEntry entry.id first entry).lits[1]! = (if first then entry.lits[0]! else entry.lits[1]!) := by
  cases first
  · simp only [retainWatchEntry, Bool.false_eq_true, ↓reduceIte, and_self]
  · simp only [retainWatchEntry, swapEntry, ↓reduceIte]
    rw [swap_read entry.lits 0 1 0 (by omega) (by omega) (by omega),
      swap_read entry.lits 0 1 1 (by omega) (by omega) (by omega)]
    simp

theorem retainWatch_database {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {entry : StoredClause}
    (member : entry ∈ original ++ learned) (lit : Lit) (wide : 2 ≤ entry.lits.size)
    (watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit) :
    Database { s with arena := retainWatch s.arena entry.id lit }
      (original.map (retainWatchEntry entry.id (s.db entry.id == lit)))
      (learned.map (retainWatchEntry entry.id (s.db entry.id == lit))) := by
  have packed := database.layout.packed member
  have bound : entry.id + 1 < s.arena.size := by have := packed.endBound; omega
  rw [retainWatch_eq_swap _ _ _ bound watched]
  by_cases first : s.db entry.id = lit
  · have test : (s.arena[entry.id]! == lit) = true := by simpa only [beq_iff_eq, State.db] using first
    simpa only [State.db, test, ite_true, Nat.add_zero, retainWatchEntry_true] using
      database.swapLiterals member 0 1 (by omega) (by omega)
  · have firstArray : ¬s.arena[entry.id]! = lit := first
    have test : (s.arena[entry.id]! == lit) = false := by simp [firstArray]
    simpa only [State.db, test, Bool.false_eq_true, ite_false, retainWatchEntry_false, List.map_id'] using database

theorem retainWatch_databaseMeaning {formula : CNF Nat} {original learned : List StoredClause}
    (meaning : DatabaseMeaning formula original learned) (id : Nat) (first : Bool) :
    DatabaseMeaning formula (original.map (retainWatchEntry id first))
      (learned.map (retainWatchEntry id first)) := by
  cases first
  · simpa only [retainWatchEntry_false, List.map_id'] using meaning
  · simpa only [retainWatchEntry_true] using meaning.swapLiterals id 0 1

theorem retainWatch_second (arena : Array Nat) (id : Nat) (lit : Lit) (bound : id + 1 < arena.size) :
    (retainWatch arena id lit)[id + 1]! = lit := by
  apply Array.getElem!_set!_self
  unfold orientWatch
  split <;> simpa using bound

theorem replacement_retainWatch (arena marks : Array Nat) (id : Nat) (lit : Lit) :
    replacement (retainWatch arena id lit) marks id = replacement (orientWatch arena id lit) marks id :=
  replacement_set_before _ _ _ _ _ (by omega)

private theorem fresh_of_unmarked_pair {s : State} {lit : Lit} (active : ActiveTrail s)
    (head : s.mark lit = 0) (opposite : s.mark lit.negate = 0) : FreshVariable s lit.var := by
  intro i before same
  have encoded := literal_encoding s.trail[i]!
  rw [same] at encoded
  have headEncoded := literal_encoding lit
  have oppositeEncoded := literal_encoding lit.negate
  rw [negate_var] at oppositeEncoded
  have different := negate_ne lit
  have polarity : s.trail[i]! = lit ∨ s.trail[i]! = lit.negate := by
    rcases encoded with positive | negative
    · rcases headEncoded with positive' | negative'
      · exact Or.inl (positive.trans positive'.symm)
      · right
        rcases oppositeEncoded with positive'' | negative''
        · exact positive.trans positive''.symm
        · exact False.elim (different (negative''.trans negative'.symm))
    · rcases headEncoded with positive' | negative'
      · right
        rcases oppositeEncoded with positive'' | negative''
        · exact False.elim (different (positive''.trans positive'.symm))
        · exact negative.trans negative''.symm
      · exact Or.inl (negative.trans negative'.symm)
  rcases polarity with equal | equal
  · exact (active i before).2.1 ((congrArg s.mark equal).trans head)
  · exact (active i before).2.1 ((congrArg s.mark equal).trans opposite)

/-- Retaining a watch changes only arena order. Thus it changes no previous
semantic dependency, and a concrete failed scan establishes the new unit
dependency rather than assuming that dependency of the poststate. -/
theorem watch_unit_preserves {s : State} {formula : CNF Nat} {original learned : List StoredClause}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (coverage : MarkedOnTrail s) (active : ActiveTrail s) (reasons : ReasonConsequences formula s)
    {entry : StoredClause} (member : entry ∈ original ++ learned) (lit : Lit) (root : Bool)
    (wide : 2 ≤ entry.lits.size) (watched : s.db entry.id = lit ∨ s.db (entry.id + 1) = lit)
    (falseLit : s.mark lit ≠ 0)
    (missing : replacement (orientWatch s.arena entry.id lit) s.marks entry.id = none)
    (head : s.mark (retainWatch s.arena entry.id lit)[entry.id]! = 0)
    (opposite : s.mark (Lit.negate (retainWatch s.arena entry.id lit)[entry.id]!) = 0)
    (space : s.assigned < s.trail.size) :
    let ready := { s with arena := retainWatch s.arena entry.id lit }
    let f := retainWatchEntry entry.id (s.db entry.id == lit)
    Database (ready.assign entry.id root) (original.map f) (learned.map f) ∧
      DatabaseMeaning formula (original.map f) (learned.map f) ∧
      ReasonConsequences formula (ready.assign entry.id root) ∧
      ∀ a, CNF.Sat a formula → TrailCompatible s a → TrailCompatible (ready.assign entry.id root) a := by
  let ready := { s with arena := retainWatch s.arena entry.id lit }
  let f := retainWatchEntry entry.id (s.db entry.id == lit)
  have nextDatabase := retainWatch_database database member lit wide watched
  have nextMeaning := retainWatch_databaseMeaning meaning entry.id (s.db entry.id == lit)
  have mappedMember : f entry ∈ original.map f ++ learned.map f := by
    rw [← List.map_append]
    exact List.mem_map.mpr ⟨entry, member, rfl⟩
  have packed : PackedClause ready entry.id (f entry).lits := by
    simpa only [f, retainWatchEntry_id] using nextDatabase.layout.packed mappedMember
  have bound : entry.id + 1 < s.arena.size := by have := (database.layout.packed member).endBound; omega
  have second : (f entry).lits[1]! = lit := by
    have read := packed.literals 1 (by simpa only [f, retainWatchEntry_size] using (show 1 < entry.lits.size by omega))
    exact read.symm.trans (retainWatch_second s.arena entry.id lit bound)
  have entailed : CNF.EntailsClause formula (clauseView (f entry).lits) :=
    nextMeaning.entails_entry mappedMember
  have nextCoverage : MarkedOnTrail ready := coverage
  have nextActive : ActiveTrail ready := active
  have nextReasons : ReasonConsequences formula ready := reasons
  have noReplacement : replacement ready.arena ready.marks entry.id = none :=
    (replacement_retainWatch _ _ _ _).trans missing
  have secondFalse : ready.mark (f entry).lits[1]! ≠ 0 := by simpa only [second, ready, State.mark] using falseLit
  have unit := unit_of_replacement_none packed noReplacement secondFalse
  have fresh : FreshVariable ready (Lit.var (ready.db entry.id)) := fresh_of_unmarked_pair nextActive head opposite
  refine ⟨nextDatabase.assign _ _, nextMeaning, ?_, ?_⟩
  · exact reasonConsequences_assign nextReasons entailed nextCoverage unit fresh space
  · intro a model compatible
    exact trailCompatible_assign_of_unit entailed nextCoverage unit space model compatible

theorem propagateWatches_unit (fuel : Nat) (s : State) (arena first : Array Nat)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat)
    (nonzero : currentWatchRef arena first lit previous ≠ 0)
    (missing : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
      s.marks (watchClause (currentWatchRef arena first lit previous)) = none)
    (head : s.mark ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) = 0)
    (opposite : s.mark (Lit.negate ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0) :
    propagateWatches (fuel + 1) s arena first decision oldLemmas root lit previous =
      .running ⟨(restoreWatchArrays s
        (retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit) first).assign
          (watchClause (currentWatchRef arena first lit previous)) root,
        decision, .watch, oldLemmas, root, lit, currentWatchRef arena first lit previous⟩ := by
  simp only [currentWatchRef, beq_iff_eq] at nonzero
  simp only [currentWatchRef, orientWatch, beq_iff_eq] at missing
  simp only [currentWatchRef, retainWatch, orientWatch, beq_iff_eq] at head opposite
  simp only [propagateWatches, currentWatchRef, retainWatch, orientWatch, Id.run, pure,
    beq_iff_eq, nonzero, ite_false, missing, restoreWatchArrays_mark, head, opposite, bne_iff_ne, ne_eq,
    not_true_eq_false, ite_true]

end MicrosatLean.Verification.Implementation.Native.Propagation
