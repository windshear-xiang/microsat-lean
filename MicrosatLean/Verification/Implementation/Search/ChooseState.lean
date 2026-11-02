import MicrosatLean.Verification.Implementation.Bridge.FromNative
import MicrosatLean.Verification.Implementation.Native.Search.ChoiceSettlement

namespace MicrosatLean.Verification.Implementation.Search

open Bridge
private abbrev NEntry := Native.Representation.StoredClause

/-- Counters and heuristics do not occur in the logical state view. -/
theorem nativeState_counters (s : CDCL.State) (original learned : List NEntry) (res fast : Nat) :
    nativeState { s with res := res, fast := fast } original learned = nativeState s original learned := rfl

theorem nativeTrail_restart (s : CDCL.State) (entries : List NEntry)
    (bounds : Native.Representation.TrailBounds s) :
    nativeTrail s.restart entries = (nativeTrail s entries).take s.forced := by
  have forced : s.forced ≤ s.assigned := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  simp only [nativeTrail, Native.Representation.restart_assigned bounds,
    nativeReason, CDCL.State.reason, Native.Representation.restart_reasons,
    Native.Representation.restart_trail, ← List.map_take, List.take_range, Nat.min_eq_left forced]
  rfl

theorem nativeState_restart (s : CDCL.State) (original learned : List NEntry)
    (bounds : Native.Representation.TrailBounds s) :
    nativeState s.restart original learned =
      { nativeState s original learned with trail := (nativeState s original learned).trail.take s.forced } := by
  simp only [nativeState, Native.Representation.restart_nVars,
    Native.Representation.restart_forced, nativeTrail_restart s _ bounds]

private theorem nativeReason_eq_entry {s : CDCL.State} {original learned : List NEntry}
    (database : Native.Representation.Database s original learned)
    (proper : Native.Representation.ReasonDatabase s (original ++ learned))
    {i : Nat} (before : i < s.assigned) {entry : NEntry}
    (member : entry ∈ original ++ learned) (id : s.reason s.trail[i]! = entry.id) :
    nativeReason s (original ++ learned) i = some entry.view := by
  have nonzero : s.reason s.trail[i]! ≠ 0 := by
    have lower := (database.layout.packed member).startLower
    omega
  obtain ⟨selected, contained, selectedId, value⟩ := nativeReason_some proper before nonzero
  have same := database.layout.entry_eq_of_id contained member (selectedId.symm.trans id)
  simpa only [same] using value

private theorem reduce_zero_reason {input : CNF} {s : CDCL.State} {original learned : List NEntry}
    {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    (k : Nat) {i : Nat} (before : i < s.assigned) (zero : s.reason s.trail[i]! = 0) :
    (s.reduceDB k).reason (s.reduceDB k).trail[i]! = 0 := by
  have literal := (base.active i before).1
  have index : s.trail[i]!.var < s.reasons.size := by
    rw [base.arrays.reasonsSize]
    have := literal.2
    omega
  have fixed : ¬ s.fixed ≤ 0 := by have := base.database.fixed; omega
  rw [Native.Reduction.reduceDB_trail, Native.Reduction.reduceDB_reason k literal.1 literal.2 index, zero]
  simp only [Native.Reduction.relocatedReason, fixed, ↓reduceIte]

theorem nativeReason_reduction {input : CNF} {s : CDCL.State} {original learned kept : List NEntry}
    {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    (k : Nat) (stored : Native.Representation.Database (s.reduceDB k) original kept)
    (proper : Native.Representation.ReasonDatabase (s.reduceDB k) (original ++ kept))
    (relocated : Native.Reduction.ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept))
    {i : Nat} (before : i < s.assigned) :
    nativeReason (s.reduceDB k) (original ++ kept) i = nativeReason s (original ++ learned) i := by
  have active : i < (s.reduceDB k).assigned := by simpa only [Native.Reduction.reduceDB_assigned] using before
  by_cases zero : s.reason s.trail[i]! = 0
  · have afterZero := reduce_zero_reason base k before zero
    simp only [nativeReason, zero, afterZero, ↓reduceIte]
  · obtain ⟨old, oldMember, next, nextMember, oldId, nextId, literals⟩ := relocated i before zero
    rw [nativeReason_eq_entry base.database base.reasons before oldMember oldId,
      nativeReason_eq_entry stored proper active nextMember nextId]
    simp only [Native.Representation.StoredClause.view, literals]

theorem nativeState_reduction {input : CNF} {s : CDCL.State} {original learned kept : List NEntry}
    {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    (k : Nat) (stored : Native.Representation.Database (s.reduceDB k) original kept)
    (proper : Native.Representation.ReasonDatabase (s.reduceDB k) (original ++ kept))
    (relocated : Native.Reduction.ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept)) :
    nativeState (s.reduceDB k) original kept =
      { nativeState s original learned with learned := kept.map Native.Representation.StoredClause.view } := by
  have trail : nativeTrail (s.reduceDB k) (original ++ kept) = nativeTrail s (original ++ learned) := by
    apply List.ext_getElem (by simp only [nativeTrail_length, Native.Reduction.reduceDB_assigned])
    intro i leftBound rightBound
    have before : i < s.assigned := by simpa only [nativeTrail_length] using rightBound
    have after : i < (s.reduceDB k).assigned := by simpa only [nativeTrail_length] using leftBound
    rw [← getElem!_pos _ i leftBound, ← getElem!_pos _ i rightBound,
      nativeTrail_get _ _ after, nativeTrail_get _ _ before,
      Native.Reduction.reduceDB_trail, nativeReason_reduction base k stored proper relocated before]
  simp only [nativeState, Native.Reduction.reduceDB_nVars, Native.Reduction.reduceDB_forced, trail]

end MicrosatLean.Verification.Implementation.Search
