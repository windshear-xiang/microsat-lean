import MicrosatLean.Verification.Implementation.Reduction.Counters

namespace MicrosatLean.Verification.Implementation.Reduction

open CDCL Representation

abbrev ClauseReadAcc := Array Lit × Nat × Nat

/-- The exact anonymous inner body in the executable compactor. -/
def clauseReadBody (arena : Array Nat) (phases : Array Bool) (_ : Nat) (acc : ClauseReadAcc) :
    Id (ForInStep ClauseReadAcc) := Id.run do
  let lit : Lit := arena[acc.2.2]!
  if lit == 0 then return .done acc
  if lit.satisfiedBy phases then
    return .yield (acc.1.push lit, acc.2.1 + 1, acc.2.2 + 1)
  return .yield (acc.1.push lit, acc.2.1, acc.2.2 + 1)

def scanClause (arena : Array Nat) (phases : Array Bool) (id : Nat) : ClauseReadAcc :=
  forIn (m := Id) [:arena.size - id] (#[], 0, id) (clauseReadBody arena phases)

/-- Equality includes the real scan, branch test, allocator and remap write. -/
theorem compactionBody_eq_scan (oldArena : Array Nat) (locked : Array Bool) (k index : Nat)
    (s : State) (remap : Array Nat) (start : Nat) :
    compactionBody oldArena locked k index (s, remap, start) =
      let result := scanClause oldArena s.phases (start + 2)
      if result.2.1 < k || locked[start + 2]! then
        let added := s.addClause result.1 false
        .yield (added.1, remap.set! (start + 2) added.2, result.2.2 + 1)
      else .yield (s, remap, result.2.2 + 1) := by
  simp only [compactionBody, scanClause, Id.run, bind, pure]
  unfold clauseReadBody
  rfl

def clauseReadScan (arena : Array Nat) (phases : Array Bool) : Nat → ClauseReadAcc → ClauseReadAcc
  | 0, acc => acc
  | fuel + 1, acc =>
    match clauseReadBody arena phases 0 acc with
    | .done result => result
    | .yield next => clauseReadScan arena phases fuel next

theorem clauseRead_range_eq (arena : Array Nat) (phases : Array Bool) (fuel start : Nat)
    (acc : ClauseReadAcc) :
    forIn (m := Id) (List.range' start fuel) acc (clauseReadBody arena phases) =
      clauseReadScan arena phases fuel acc := by
  induction fuel generalizing start acc with
  | zero => rfl
  | succ fuel ih =>
    rw [List.range'_succ, List.forIn_cons]
    simp only [bind, pure]
    have ignore : clauseReadBody arena phases start acc = clauseReadBody arena phases 0 acc := rfl
    rw [ignore]
    cases execute : clauseReadBody arena phases 0 acc with
    | done result => simp only [clauseReadScan, execute]
    | yield next => simpa only [clauseReadScan, execute] using ih (start + 1) next

theorem scanClause_eq_scan (arena : Array Nat) (phases : Array Bool) (id : Nat) :
    scanClause arena phases id = clauseReadScan arena phases (arena.size - id) (#[], 0, id) := by
  unfold scanClause
  rw [Std.Legacy.Range.forIn_eq_forIn_range', clauseRead_range_eq]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]

private theorem clauseReadScan_words (words : List Lit) (arena : Array Nat) (phases : Array Bool)
    (fuel cursor : Nat) (accLits : Array Lit) (count : Nat)
    (budget : words.length < fuel)
    (reads : ∀ i, i < words.length → arena[cursor + i]! = words[i]!)
    (nonzero : ∀ lit ∈ words, lit ≠ 0) (terminator : arena[cursor + words.length]! = 0) :
    clauseReadScan arena phases fuel (accLits, count, cursor) =
      (accLits ++ words.toArray, count + (words.filter (fun lit => lit.satisfiedBy phases)).length,
        cursor + words.length) := by
  induction words generalizing fuel cursor accLits count with
  | nil =>
    cases fuel with
    | zero => simp at budget
    | succ fuel =>
      have zero : arena[cursor]! = 0 := by simpa using terminator
      simp [clauseReadScan, clauseReadBody, zero, Id.run, pure]
  | cons lit rest ih =>
    cases fuel with
    | zero => simp at budget
    | succ fuel =>
      have head : arena[cursor]! = lit := by simpa using reads 0 (by simp)
      have notZero : lit ≠ 0 := nonzero lit (by simp)
      have tailReads : ∀ i, i < rest.length → arena[(cursor + 1) + i]! = rest[i]! := by
        intro i before
        simpa only [List.getElem!_cons_succ, Nat.add_assoc, Nat.add_comm 1 i] using
          reads (i + 1) (by simp; omega)
      have tailZero : arena[(cursor + 1) + rest.length]! = 0 := by
        simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1 rest.length] using terminator
      cases satisfied : lit.satisfiedBy phases <;>
        simp only [clauseReadScan, clauseReadBody, head, notZero, satisfied, beq_iff_eq,
          Bool.false_eq_true, ↓reduceIte, Id.run, pure] <;>
        rw [ih fuel (cursor + 1) (accLits.push lit) _ (by simp at budget; omega) tailReads
          (by intro word member; exact nonzero word (List.mem_cons_of_mem lit member)) tailZero] <;>
        rw [List.toArray_cons, Array.push_eq_append, Array.append_assoc] <;>
        simp only [List.filter_cons, satisfied, Bool.false_eq_true, ↓reduceIte, List.length_cons,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- The reduction criterion counts literals true in the saved phase array. -/
def phaseTrueCount (phases : Array Bool) (lits : Array Lit) : Nat :=
  (lits.toList.filter (fun lit => lit.satisfiedBy phases)).length

/-- The actual finite scan reads every literal of a genuine packed clause,
stops at its real zero terminator, and computes the exact phase count. The
arena bound supplies enough iterations even when the clause is last. -/
theorem scanClause_packed {old : State} {id : Nat} {lits : Array Lit}
    (packed : PackedClause old id lits) (phases : Array Bool) :
    scanClause old.arena phases id = (lits, phaseTrueCount phases lits, id + lits.size) := by
  rw [scanClause_eq_scan]
  have budget : lits.toList.length < old.arena.size - id := by
    have bound := packed.endBound
    simp only [Array.length_toList]
    omega
  have reads : ∀ i, i < lits.toList.length → old.arena[id + i]! = lits.toList[i]! := by
    intro i before
    have within : i < lits.size := by simpa only [Array.length_toList] using before
    have same : lits.toList[i]! = lits[i]! := by
      rw [getElem!_pos lits.toList i before, getElem!_pos lits i within]
      exact Array.getElem_toList before
    rw [same]
    exact packed.literals i within
  have nonzero : ∀ lit ∈ lits.toList, lit ≠ 0 := by
    intro lit member
    exact (packed.wellFormed lit (by simpa using member)).nonzero
  have terminator : old.arena[id + lits.toList.length]! = 0 := by
    simpa only [Array.length_toList, State.db] using packed.terminator
  simpa [phaseTrueCount] using clauseReadScan_words lits.toList old.arena phases
    (old.arena.size - id) id #[] 0 budget reads nonzero terminator

/-- A real stored entry's compaction step is exactly its semantic keep test,
followed by the actual allocator/remap write or by an unchanged accumulator. -/
theorem compactionBody_packed {old : State} {start : Nat} {lits : Array Lit}
    (packed : PackedClause old (start + 2) lits) (locked : Array Bool) (k index : Nat)
    (s : State) (remap : Array Nat) :
    compactionBody old.arena locked k index (s, remap, start) =
      if phaseTrueCount s.phases lits < k || locked[start + 2]! then
        let added := s.addClause lits false
        .yield (added.1, remap.set! (start + 2) added.2, start + 2 + lits.size + 1)
      else .yield (s, remap, start + 2 + lits.size + 1) := by
  rw [compactionBody_eq_scan, scanClause_packed packed s.phases]

end MicrosatLean.Verification.Implementation.Reduction
