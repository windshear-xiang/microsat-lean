import MicrosatLean.Verification.Implementation.Native.Representation.Database
import MicrosatLean.Verification.Implementation.Native.Search.Measure

namespace MicrosatLean.Verification.Implementation.Native.Reduction

open CDCL Representation Search

/-!
Exact loop names for the executable compactor. Counter projections do not
require a well-formed database; retained-clause and relocation correctness are
separate obligations.
-/

def lockedReasons (s : State) : Array Bool := Id.run do
  let mut locked := Array.replicate s.arena.size false
  for idx in [:s.forced] do
    let clauseId := s.reason s.trail[idx]!
    if clauseId != 0 then locked := locked.set! clauseId true
  return locked

abbrev CompactionAcc := State × Array Nat × Nat

/-- The actual bounded learned-clause iteration, including its arena scan. -/
def compactionBody (oldArena : Array Nat) (locked : Array Bool) (k : Nat)
    (_ : Nat) (acc : CompactionAcc) : Id (ForInStep CompactionAcc) := Id.run do
  let mut s := acc.1
  let mut remap := acc.2.1
  let start := acc.2.2
  let clauseId := start + 2
  let mut lits : Array Lit := #[]
  let mut count := 0
  let mut cursor := clauseId
  for _ in [:oldArena.size - clauseId] do
    let lit : Lit := oldArena[cursor]!
    if lit == 0 then break
    lits := lits.push lit
    if lit.satisfiedBy s.phases then count := count + 1
    cursor := cursor + 1
  let start := cursor + 1
  if count < k || locked[clauseId]! then
    let (next, newId) := s.addClause lits false
    s := next
    remap := remap.set! clauseId newId
  return .yield (s, remap, start)

def compactionInitial (s : State) : CompactionAcc :=
  let detached := s.removeLearnedWatches
  ({ detached with
      arena := detached.arena.extract 0 detached.fixed,
      nLemmas := 0, maxLemmas := scheduledLimit s.nLemmas s.maxLemmas },
    Array.replicate s.arena.size 0, detached.fixed)

def compactionResult (s : State) (k : Nat) : CompactionAcc :=
  forIn (m := Id) [:s.nLemmas] (compactionInitial s)
    (compactionBody s.arena (lockedReasons s) k)

def relocatedReasons (s : State) (remap : Array Nat) : Array Nat := Id.run do
  let mut reasons := s.reasons
  for var in [1:s.nVars + 1] do
    let oldId := reasons[var]!
    if oldId >= s.fixed then reasons := reasons.set! var remap[oldId]!
  return reasons

/-- Definitional agreement with all loops, branches, and array operations in
the executable function. No alternative compaction algorithm is introduced. -/
theorem reduceDB_eq_compaction (s : State) (k : Nat) :
    s.reduceDB k =
      let result := compactionResult s k
      { result.1 with
        reasons := relocatedReasons result.1 result.2.1
        stats := { result.1.stats with
          reductions := result.1.stats.reductions + 1
          removedLearned := result.1.stats.removedLearned + s.nLemmas - result.1.nLemmas } } := by
  by_cases pressure : s.nLemmas > s.maxLemmas
  all_goals
    simp only [State.reduceDB, compactionResult, compactionInitial, scheduledLimit,
      pressure, ↓reduceIte, Id.run, pure, bind]
    rfl

private theorem addClause_maxLemmas (s : State) (lits : Array Lit) :
    (s.addClause lits false).1.maxLemmas = s.maxLemmas := by
  by_cases watches : 1 < lits.size <;>
    simp [State.addClause, State.addWatch, watches]

private theorem compactionBody_counters (oldArena : Array Nat) (locked : Array Bool)
    (k index : Nat) (acc : CompactionAcc) :
    (compactionBody oldArena locked k index acc).value.1.maxLemmas = acc.1.maxLemmas ∧
      (compactionBody oldArena locked k index acc).value.1.nLemmas ≤ acc.1.nLemmas + 1 := by
  simp only [compactionBody, Id.run, pure, bind]
  split
  · simp only [ForInStep.value_yield, addClause_maxLemmas, addClause_learnedCount,
      Bool.false_eq_true, ↓reduceIte]
    exact ⟨True.intro, Nat.le_refl _⟩
  · exact ⟨rfl, Nat.le_add_right _ _⟩

private theorem compactionList_counters (oldArena : Array Nat) (locked : Array Bool)
    (k : Nat) (xs : List Nat) (acc : CompactionAcc) :
    let result := forIn (m := Id) xs acc (compactionBody oldArena locked k)
    result.1.maxLemmas = acc.1.maxLemmas ∧ result.1.nLemmas ≤ acc.1.nLemmas + xs.length := by
  induction xs generalizing acc with
  | nil => exact ⟨rfl, by simp only [List.length_nil, Nat.add_zero]; exact Nat.le_refl _⟩
  | cons head tail ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    have step := compactionBody_counters oldArena locked k head acc
    cases body : compactionBody oldArena locked k head acc with
    | done next =>
      simp only [body, ForInStep.value_done] at step
      exact ⟨step.1, by simp only [List.length_cons]; omega⟩
    | yield next =>
      simp only [body, ForInStep.value_yield] at step
      have rest := ih next
      exact ⟨rest.1.trans step.1, by simp only [List.length_cons]; omega⟩

/-- The complete actual compactor uses the scheduled limit exactly. -/
theorem reduceDB_maxLemmas (s : State) (k : Nat) :
    (s.reduceDB k).maxLemmas = scheduledLimit s.nLemmas s.maxLemmas := by
  rw [reduceDB_eq_compaction]
  dsimp only
  unfold compactionResult
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact (compactionList_counters _ _ _ _ _).1

/-- At most one clause is stored per original learned-clause iteration. -/
theorem reduceDB_nLemmas_le (s : State) (k : Nat) :
    (s.reduceDB k).nLemmas ≤ s.nLemmas := by
  rw [reduceDB_eq_compaction]
  dsimp only
  unfold compactionResult
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have bound := (compactionList_counters s.arena (lockedReasons s) k
    (List.range' [:s.nLemmas].start [:s.nLemmas].size [:s.nLemmas].step)
    (compactionInitial s)).2
  simpa only [compactionInitial, List.length_range', Nat.zero_add, Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] using bound

theorem reduceDB_nLemmas_le_limit (s : State) (k : Nat) :
    (s.reduceDB k).nLemmas ≤ (s.reduceDB k).maxLemmas := by
  rw [reduceDB_maxLemmas]
  exact Nat.le_trans (reduceDB_nLemmas_le s k) (count_le_scheduledLimit _ _)

/-- This decrease concerns the actual reduction transition, including arbitrary
forgetting. Global termination additionally needs a finite active-clause bound. -/
theorem reduceDB_clauseProgress {bound : Nat} (s : State) (k : Nat)
    (bounded : s.nLemmas ≤ bound) (pressure : s.maxLemmas < s.nLemmas) :
    clauseProgress bound (s.reduceDB k) < clauseProgress bound s := by
  apply clauseProgress_lt_of_reduce bounded pressure
  rw [reduceDB_maxLemmas]
  exact scheduledLimit_strict_of_pressure pressure

end MicrosatLean.Verification.Implementation.Native.Reduction
