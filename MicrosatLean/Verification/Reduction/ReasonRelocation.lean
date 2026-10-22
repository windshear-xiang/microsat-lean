import MicrosatLean.Verification.Reduction.WatchFilter

namespace MicrosatLean.Verification.Reduction

open CDCL Representation

/-- Exact proof name for the lock-table update in the executable reducer. -/
def lockReasonBody (s : State) (index : Nat) (locked : Array Bool) : Id (ForInStep (Array Bool)) :=
  Id.run do
    let id := s.reason s.trail[index]!
    if id != 0 then return .yield (locked.set! id true)
    return .yield locked

theorem lockedReasons_eq_loop (s : State) : lockedReasons s =
    forIn (m := Id) [:s.forced] (Array.replicate s.arena.size false) (lockReasonBody s) := by
  rfl

private theorem lockReasonBody_eq (s : State) (index : Nat) (locked : Array Bool) :
    lockReasonBody s index locked = .yield
      (if s.reason s.trail[index]! = 0 then locked else locked.set! (s.reason s.trail[index]!) true) := by
  by_cases zero : s.reason s.trail[index]! = 0 <;> simp [lockReasonBody, zero]

private theorem lockReasonLoop (s : State) (indices : List Nat) (locked : Array Bool) :
    let result : Array Bool := forIn (m := Id) indices locked (lockReasonBody s)
    result.size = locked.size ∧ ∀ id, id < locked.size →
      (locked[id]! = true ∨ ∃ index ∈ indices, s.reason s.trail[index]! = id ∧ id ≠ 0) →
      result[id]! = true := by
  induction indices generalizing locked with
  | nil =>
    refine ⟨rfl, ?_⟩
    intro id bound witness
    rcases witness with old | ⟨index, member, _⟩
    · exact old
    · simp at member
  | cons index rest ih =>
    rw [List.forIn_cons, lockReasonBody_eq]
    simp only [bind]
    split
    · rename_i zero
      have tail := ih locked
      refine ⟨tail.1, ?_⟩
      intro id bound witness
      apply tail.2 id bound
      rcases witness with old | ⟨other, member, equal, nonzero⟩
      · exact Or.inl old
      · rcases List.mem_cons.mp member with rfl | member
        · exact False.elim (nonzero (equal.symm.trans zero))
        · exact Or.inr ⟨other, member, equal, nonzero⟩
    · rename_i nonzero
      let next := locked.set! (s.reason s.trail[index]!) true
      have tail := ih next
      refine ⟨tail.1.trans (Array.size_set! _ _ _), ?_⟩
      intro id bound witness
      apply tail.2 id (by simpa only [next, Array.size_set!] using bound)
      rcases witness with old | ⟨other, member, equal, idNonzero⟩
      · left
        by_cases same : s.reason s.trail[index]! = id
        · simpa only [next, same] using Array.getElem!_set!_self locked id true bound
        · exact (Array.getElem!_set!_ne _ _ _ _ same).trans old
      · rcases List.mem_cons.mp member with rfl | member
        · left
          simpa only [next, equal] using Array.getElem!_set!_self locked id true bound
        · exact Or.inr ⟨other, member, equal, idNonzero⟩

/-- Every genuine nonzero reason of a forced trail entry is locked by the
actual scan, independently of the phase-satisfaction reduction threshold. -/
theorem lockedReasons_of_index {s : State} {i : Nat} (before : i < s.forced)
    (nonzero : s.reason s.trail[i]! ≠ 0)
    (bounded : s.reason s.trail[i]! < s.arena.size) :
    (lockedReasons s)[s.reason s.trail[i]!]! = true := by
  rw [lockedReasons_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  have member : i ∈ List.range' 0 s.forced := List.mem_range'.mpr ⟨i, before, by simp⟩
  apply (lockReasonLoop s (List.range' 0 s.forced) (Array.replicate s.arena.size false)).2
    _ (by simpa using bounded)
  exact Or.inr ⟨i, member, rfl, nonzero⟩

def relocatedReason (fixed : Nat) (remap : Array Nat) (id : Nat) : Nat :=
  if fixed ≤ id then remap[id]! else id

/-- Exact proof name for the second executable array loop. -/
def relocateReasonBody (fixed : Nat) (remap : Array Nat) (var : Nat) (reasons : Array Nat) :
    Id (ForInStep (Array Nat)) := Id.run do
  let oldId := reasons[var]!
  if oldId >= fixed then return .yield (reasons.set! var remap[oldId]!)
  return .yield reasons

theorem relocatedReasons_eq_loop (s : State) (remap : Array Nat) : relocatedReasons s remap =
    forIn (m := Id) [1:s.nVars + 1] s.reasons (relocateReasonBody s.fixed remap) := by
  rfl

private theorem relocateReasonBody_eq (fixed : Nat) (remap : Array Nat) (var : Nat)
    (reasons : Array Nat) :
    relocateReasonBody fixed remap var reasons = .yield
      (if fixed ≤ reasons[var]! then reasons.set! var remap[reasons[var]!]! else reasons) := by
  by_cases changed : fixed ≤ reasons[var]! <;> simp [relocateReasonBody, changed]

private theorem relocateReasonLoop_size (fixed : Nat) (remap : Array Nat) (indices : List Nat)
    (reasons : Array Nat) :
    (forIn (m := Id) indices reasons (relocateReasonBody fixed remap)).size = reasons.size := by
  induction indices generalizing reasons with
  | nil => rfl
  | cons var rest ih =>
    rw [List.forIn_cons, relocateReasonBody_eq]
    simp only [bind]
    split <;> rw [ih] <;> simp

private theorem relocateReasonLoop_read (fixed : Nat) (remap : Array Nat) (indices : List Nat)
    (distinct : indices.Nodup) (reasons : Array Nat) (query : Nat) (bound : query < reasons.size) :
    let result : Array Nat := forIn (m := Id) indices reasons (relocateReasonBody fixed remap)
    result[query]! =
      if query ∈ indices then relocatedReason fixed remap reasons[query]! else reasons[query]! := by
  induction indices generalizing reasons with
  | nil => rfl
  | cons var rest ih =>
    rw [List.forIn_cons, relocateReasonBody_eq]
    simp only [bind]
    have restDistinct := (List.nodup_cons.mp distinct).2
    by_cases same : var = query
    · subst var
      have absent : query ∉ rest := (List.nodup_cons.mp distinct).1
      split
      · rename_i changed
        rw [ih restDistinct _ (by simpa using bound)]
        simp only [absent, ↓reduceIte, Array.getElem!_set!_self reasons query _ bound,
          List.mem_cons_self, relocatedReason, changed]
      · rename_i unchanged
        rw [ih restDistinct reasons bound]
        simp only [absent, ↓reduceIte, List.mem_cons_self, relocatedReason, unchanged]
    · split
      · rw [ih restDistinct _ (by simpa using bound)]
        rw [Array.getElem!_set!_ne _ _ _ _ same]
        simp only [List.mem_cons, Ne.symm same, false_or]
      · rw [ih restDistinct reasons bound]
        simp only [List.mem_cons, Ne.symm same, false_or]

theorem relocatedReasons_size (s : State) (remap : Array Nat) :
    (relocatedReasons s remap).size = s.reasons.size := by
  rw [relocatedReasons_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  exact relocateReasonLoop_size _ _ _ _

/-- Each variable is visited exactly once, so the mutable loop uses its
original reason ID and applies precisely the compaction relocation table. -/
theorem relocatedReasons_read {s : State} (remap : Array Nat) {var : Nat}
    (lower : 1 ≤ var) (upper : var ≤ s.nVars) (bound : var < s.reasons.size) :
    (relocatedReasons s remap)[var]! = relocatedReason s.fixed remap s.reasons[var]! := by
  rw [relocatedReasons_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  have member : var ∈ List.range' 1 s.nVars :=
    List.mem_range'.mpr ⟨var - 1, by omega, by omega⟩
  have read := relocateReasonLoop_read s.fixed remap (List.range' 1 s.nVars)
    (List.nodup_range' 1 (by decide)) s.reasons var bound
  simpa only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one, Nat.sub_zero,
    member, ↓reduceIte] using read

private theorem compactionBody_reasonFrame (oldArena : Array Nat) (locked : Array Bool)
    (k index : Nat) (acc : CompactionAcc) :
    (compactionBody oldArena locked k index acc).value.1.reasons = acc.1.reasons ∧
    (compactionBody oldArena locked k index acc).value.1.fixed = acc.1.fixed ∧
    (compactionBody oldArena locked k index acc).value.1.nVars = acc.1.nVars := by
  simp only [compactionBody, Id.run, pure, bind]
  split
  · simp only [ForInStep.value_yield, addClause_reasons, addClause_fixed, addClause_nVars,
      Bool.false_eq_true, ↓reduceIte, and_self]
  · exact ⟨rfl, rfl, rfl⟩

private theorem compactionLoop_reasonFrame (oldArena : Array Nat) (locked : Array Bool)
    (k : Nat) (indices : List Nat) (acc : CompactionAcc) :
    let result := forIn (m := Id) indices acc (compactionBody oldArena locked k)
    result.1.reasons = acc.1.reasons ∧ result.1.fixed = acc.1.fixed ∧ result.1.nVars = acc.1.nVars := by
  induction indices generalizing acc with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons index rest ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    have step := compactionBody_reasonFrame oldArena locked k index acc
    cases body : compactionBody oldArena locked k index acc with
    | done next => simpa only [body, ForInStep.value_done] using step
    | yield next =>
      simp only [body, ForInStep.value_yield] at step
      have tail := ih next
      exact ⟨tail.1.trans step.1, tail.2.1.trans step.2.1, tail.2.2.trans step.2.2⟩

theorem compactionResult_reasonFrame (s : State) (k : Nat) :
    (compactionResult s k).1.reasons = s.reasons ∧
    (compactionResult s k).1.fixed = s.fixed ∧ (compactionResult s k).1.nVars = s.nVars := by
  unfold compactionResult
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have loop := compactionLoop_reasonFrame s.arena (lockedReasons s) k
    (List.range' [:s.nLemmas].start [:s.nLemmas].size [:s.nLemmas].step) (compactionInitial s)
  have detached := (removeLearnedWatches_frame s).restore
  refine ⟨loop.1.trans ?_, loop.2.1.trans ?_, loop.2.2.trans ?_⟩
  · simpa only [compactionInitial] using congrArg State.reasons detached
  · simpa only [compactionInitial] using congrArg State.fixed detached
  · exact compactionInitial_vars s

theorem reduceDB_reason {s : State} (k : Nat) {lit : Lit}
    (lower : 1 ≤ lit.var) (upper : lit.var ≤ s.nVars) (bound : lit.var < s.reasons.size) :
    (s.reduceDB k).reason lit =
      relocatedReason s.fixed (compactionResult s k).2.1 (s.reason lit) := by
  have frame := compactionResult_reasonFrame s k
  rw [reduceDB_eq_compaction]
  change (relocatedReasons (compactionResult s k).1 (compactionResult s k).2.1)[lit.var]! = _
  rw [relocatedReasons_read _ lower (by simpa only [frame.2.2] using upper)
    (by simpa only [frame.1] using bound)]
  simp only [frame.1, frame.2.1, State.reason]

end MicrosatLean.Verification.Reduction
