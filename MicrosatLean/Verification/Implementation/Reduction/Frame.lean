import MicrosatLean.Verification.Implementation.Reduction.Counters
import MicrosatLean.Verification.Implementation.Reduction.WatchFilterFrame

namespace MicrosatLean.Verification.Implementation.Reduction

open CDCL Representation

/-- All fields unaffected by compaction, represented by clearing exactly its
six mutable components. In particular, the complete trail and MTF state stay. -/
def retainedState (s : State) : State :=
  { s with
    arena := #[], first := #[], reasons := #[], nLemmas := 0,
    maxLemmas := 0, stats := {} }

private theorem addClause_retained (s : State) (lits : Array Lit) :
    retainedState (s.addClause lits false).1 = retainedState s := by
  by_cases watches : 1 < lits.size <;>
    simp [retainedState, State.addClause, State.addWatch, watches]

private theorem compactionBody_retained (oldArena : Array Nat) (locked : Array Bool)
    (k index : Nat) (acc : CompactionAcc) :
    retainedState (compactionBody oldArena locked k index acc).value.1 = retainedState acc.1 := by
  simp only [compactionBody, Id.run, pure, bind]
  split
  · exact addClause_retained _ _
  · rfl

private theorem compactionList_retained (oldArena : Array Nat) (locked : Array Bool)
    (k : Nat) (xs : List Nat) (acc : CompactionAcc) :
    retainedState (forIn (m := Id) xs acc (compactionBody oldArena locked k)).1 =
      retainedState acc.1 := by
  induction xs generalizing acc with
  | nil => rfl
  | cons head tail ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    have step := compactionBody_retained oldArena locked k head acc
    cases body : compactionBody oldArena locked k head acc with
    | done next => simpa only [body, ForInStep.value_done] using step
    | yield next =>
      have frame : retainedState next.1 = retainedState acc.1 := by
        simpa only [body, ForInStep.value_yield] using step
      exact (ih next).trans frame

theorem reduceDB_retainedState (s : State) (k : Nat) :
    retainedState (s.reduceDB k) = retainedState s := by
  rw [reduceDB_eq_compaction]
  change retainedState (compactionResult s k).1 = retainedState s
  unfold compactionResult
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  rw [compactionList_retained]
  have frame := congrArg retainedState (removeLearnedWatches_frame s).restore
  simpa only [retainedState, compactionInitial] using frame

/-- A full record frame, rather than isolated equalities about selected fields. -/
theorem reduceDB_restore (s : State) (k : Nat) :
    { s.reduceDB k with
      arena := s.arena, first := s.first, reasons := s.reasons, nLemmas := s.nLemmas,
      maxLemmas := s.maxLemmas, stats := s.stats } = s := by
  have frame := congrArg (fun after : State =>
    { after with
      arena := s.arena, first := s.first, reasons := s.reasons,
      nLemmas := s.nLemmas, maxLemmas := s.maxLemmas, stats := s.stats }) (reduceDB_retainedState s k)
  simpa only [retainedState] using frame

@[simp] theorem reduceDB_nVars (s : State) (k : Nat) : (s.reduceDB k).nVars = s.nVars := by
  simpa only [retainedState] using congrArg State.nVars (reduceDB_retainedState s k)

@[simp] theorem reduceDB_assigned (s : State) (k : Nat) : (s.reduceDB k).assigned = s.assigned := by
  simpa only [retainedState] using congrArg State.assigned (reduceDB_retainedState s k)

@[simp] theorem reduceDB_processed (s : State) (k : Nat) : (s.reduceDB k).processed = s.processed := by
  simpa only [retainedState] using congrArg State.processed (reduceDB_retainedState s k)

@[simp] theorem reduceDB_forced (s : State) (k : Nat) : (s.reduceDB k).forced = s.forced := by
  simpa only [retainedState] using congrArg State.forced (reduceDB_retainedState s k)

theorem reduceDB_trailBounds {s : State} (bounds : TrailBounds s) (k : Nat) :
    TrailBounds (s.reduceDB k) := by
  constructor
  · simpa only [reduceDB_forced, reduceDB_processed] using bounds.forcedProcessed
  · simpa only [reduceDB_processed, reduceDB_assigned] using bounds.processedAssigned
  · simpa only [reduceDB_assigned, reduceDB_nVars] using bounds.assignedVars

end MicrosatLean.Verification.Implementation.Reduction
