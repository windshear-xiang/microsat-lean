import MicrosatLean.Verification.Implementation.Propagation.Closure
import MicrosatLean.Verification.Implementation.Propagation.Replacement
import MicrosatLean.Verification.Implementation.Propagation.WatchStep

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL Representation
open Std.Sat

/-- Trail coverage lets a mark-based unit test speak about every model that
agrees with the current decision assumptions, rather than only saved phases. -/
theorem marked_falsifies_of_trail {s : State} {a : Nat → Bool}
    (coverage : MarkedOnTrail s) (compatible : TrailCompatible s a)
    {lit : Lit} (marked : s.mark lit ≠ 0) : Falsifies a lit := by
  obtain ⟨i, before, equal⟩ := coverage lit marked
  simpa only [equal] using compatible i before

/-- A unit clause entailed by the input forces its head under the current
trail assumptions. The concrete watch scan must supply `unit`. -/
theorem head_true_of_unit {s : State} {formula : Std.Sat.CNF Nat} {lits : Array Lit} {head : Lit}
    (entailed : CNF.EntailsClause formula (clauseView lits))
    (coverage : MarkedOnTrail s)
    (unit : ∀ lit ∈ lits, lit ≠ head → s.mark lit ≠ 0)
    {a : Nat → Bool} (model : CNF.Sat a formula) (compatible : TrailCompatible s a) :
    a (literalView head).1 = (literalView head).2 := by
  apply Logic.forced_of_sat (entailed a model)
  intro viewed member different
  obtain ⟨lit, hlit, equal⟩ := clauseView_mem.mp member
  have ne : lit ≠ head := by
    intro same
    exact different (equal.symm.trans (congrArg literalView same))
  have falseLit := marked_falsifies_of_trail coverage compatible (unit lit hlit ne)
  simpa only [Falsifies, equal] using falseLit

/-- A failed concrete replacement scan and a false second watch establish the
unit premise used by propagation. The packed clause ties that premise to the
actual arena head read by `State.assign`. -/
theorem unit_of_replacement_none {s : State} {lits : Array Lit} {clauseId : Nat}
    (packed : PackedClause s clauseId lits)
    (missing : replacement s.arena s.marks clauseId = none)
    (secondFalse : s.mark lits[1]! ≠ 0) :
    ∀ lit ∈ lits, lit ≠ s.db clauseId → s.mark lit ≠ 0 := by
  intro lit member different
  obtain ⟨i, hi, value⟩ := Array.mem_iff_getElem.mp member
  have equal : lits[i]! = lit := by simpa only [getElem!_pos lits i hi] using value
  by_cases first : i = 0
  · subst i
    have head := packed.literals 0 (by omega)
    simp only [Nat.add_zero] at head
    exact False.elim (different (equal.symm.trans head.symm))
  · by_cases second : i = 1
    · subst i
      simpa only [equal] using secondFalse
    · simpa only [equal] using replacement_none_of_packed packed missing (by omega : 2 ≤ i) hi

end MicrosatLean.Verification.Implementation.Propagation

namespace MicrosatLean.Verification.Implementation.Propagation

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

theorem retainWatch_databaseMeaning {formula : Std.Sat.CNF Nat} {original learned : List StoredClause}
    (meaning : DatabaseMeaning formula original learned) (id : Nat) (first : Bool) :
    DatabaseMeaning formula (original.map (retainWatchEntry id first))
      (learned.map (retainWatchEntry id first)) := by
  cases first
  · simpa only [retainWatchEntry_false, List.map_id'] using meaning
  · simpa only [retainWatchEntry_true] using meaning.swapLiterals id 0 1

theorem replacement_retainWatch (arena marks : Array Nat) (id : Nat) (lit : Lit) :
    replacement (retainWatch arena id lit) marks id = replacement (orientWatch arena id lit) marks id :=
  replacement_set_before _ _ _ _ _ (by omega)

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

end MicrosatLean.Verification.Implementation.Propagation
