import MicrosatLean.Verification.Implementation.Bridge.FromConcrete
import MicrosatLean.Verification.Implementation.Search.Concrete.ChoiceSettlement

namespace MicrosatLean.Verification.Implementation.Search

open Bridge

/-- Counters and heuristics do not occur in the logical state view. -/
theorem logicalView_counters (s : CDCL.State) (original learned : List StoredClause) (res fast : Nat) :
    logicalView { s with res := res, fast := fast } original learned = logicalView s original learned := rfl

theorem trailView_restart (s : CDCL.State) (entries : List StoredClause)
    (bounds : Representation.TrailBounds s) :
    trailView s.restart entries = (trailView s entries).take s.forced := by
  have forced : s.forced ≤ s.assigned := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  simp only [trailView, Representation.restart_assigned bounds,
    reasonView, CDCL.State.reason, Representation.restart_reasons,
    Representation.restart_trail, ← List.map_take, List.take_range, Nat.min_eq_left forced]
  rfl

theorem logicalView_restart (s : CDCL.State) (original learned : List StoredClause)
    (bounds : Representation.TrailBounds s) :
    logicalView s.restart original learned =
      { logicalView s original learned with trail := (logicalView s original learned).trail.take s.forced } := by
  simp only [logicalView, Representation.restart_nVars,
    Representation.restart_forced, trailView_restart s _ bounds]

private theorem reasonView_eq_entry {s : CDCL.State} {original learned : List StoredClause}
    (database : Representation.Database s original learned)
    (proper : Representation.ReasonDatabase s (original ++ learned))
    {i : Nat} (before : i < s.assigned) {entry : StoredClause}
    (member : entry ∈ original ++ learned) (id : s.reason s.trail[i]! = entry.id) :
    reasonView s (original ++ learned) i = some entry.view := by
  have nonzero : s.reason s.trail[i]! ≠ 0 := by
    have lower := (database.layout.packed member).startLower
    omega
  obtain ⟨selected, contained, selectedId, value⟩ := reasonView_some proper before nonzero
  have same := database.layout.entry_eq_of_id contained member (selectedId.symm.trans id)
  simpa only [same] using value

private theorem reduce_zero_reason {input : CNF} {s : CDCL.State} {original learned : List StoredClause}
    {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate input s original learned heads rank)
    (k : Nat) {i : Nat} (before : i < s.assigned) (zero : s.reason s.trail[i]! = 0) :
    (s.reduceDB k).reason (s.reduceDB k).trail[i]! = 0 := by
  have literal := (base.active i before).1
  have index : s.trail[i]!.var < s.reasons.size := by
    rw [base.arrays.reasonsSize]
    have := literal.2
    omega
  have fixed : ¬ s.fixed ≤ 0 := by have := base.database.fixed; omega
  rw [Reduction.reduceDB_trail, Reduction.reduceDB_reason k literal.1 literal.2 index, zero]
  simp only [Reduction.relocatedReason, fixed, ↓reduceIte]

theorem reasonView_reduction {input : CNF} {s : CDCL.State} {original learned kept : List StoredClause}
    {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate input s original learned heads rank)
    (k : Nat) (stored : Representation.Database (s.reduceDB k) original kept)
    (proper : Representation.ReasonDatabase (s.reduceDB k) (original ++ kept))
    (relocated : Reduction.ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept))
    {i : Nat} (before : i < s.assigned) :
    reasonView (s.reduceDB k) (original ++ kept) i = reasonView s (original ++ learned) i := by
  have active : i < (s.reduceDB k).assigned := by simpa only [Reduction.reduceDB_assigned] using before
  by_cases zero : s.reason s.trail[i]! = 0
  · have afterZero := reduce_zero_reason base k before zero
    simp only [reasonView, zero, afterZero, ↓reduceIte]
  · obtain ⟨old, oldMember, next, nextMember, oldId, nextId, literals⟩ := relocated i before zero
    rw [reasonView_eq_entry base.database base.reasons before oldMember oldId,
      reasonView_eq_entry stored proper active nextMember nextId]
    simp only [Representation.StoredClause.view, literals]

theorem logicalView_reduction {input : CNF} {s : CDCL.State} {original learned kept : List StoredClause}
    {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate input s original learned heads rank)
    (k : Nat) (stored : Representation.Database (s.reduceDB k) original kept)
    (proper : Representation.ReasonDatabase (s.reduceDB k) (original ++ kept))
    (relocated : Reduction.ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept)) :
    logicalView (s.reduceDB k) original kept =
      { logicalView s original learned with learned := kept.map Representation.StoredClause.view } := by
  have trail : trailView (s.reduceDB k) (original ++ kept) = trailView s (original ++ learned) := by
    apply List.ext_getElem (by simp only [trailView_length, Reduction.reduceDB_assigned])
    intro i leftBound rightBound
    have before : i < s.assigned := by simpa only [trailView_length] using rightBound
    have after : i < (s.reduceDB k).assigned := by simpa only [trailView_length] using leftBound
    rw [← getElem!_pos _ i leftBound, ← getElem!_pos _ i rightBound,
      trailView_get _ _ after, trailView_get _ _ before,
      Reduction.reduceDB_trail, reasonView_reduction base k stored proper relocated before]
  simp only [logicalView, Reduction.reduceDB_nVars, Reduction.reduceDB_forced, trail]

end MicrosatLean.Verification.Implementation.Search
