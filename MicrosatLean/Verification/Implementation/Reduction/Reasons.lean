import MicrosatLean.Verification.Implementation.Reduction.ReasonRelocation
import MicrosatLean.Verification.Implementation.Analysis.ReasonUpdates
import MicrosatLean.Verification.Implementation.Representation.ReasonDatabase

namespace MicrosatLean.Verification.Implementation.Reduction

open CDCL Representation Propagation Analysis Std.Sat

private theorem original_id_before_boundary {s : State} {start : Nat}
    {original learned : List StoredClause} (layout : DatabaseFrom s start (original ++ learned))
    {entry : StoredClause} (member : entry ∈ original) :
    entry.id < start + (original.map fun e => e.lits.size + 3).sum := by
  induction original generalizing start with
  | nil => simp at member
  | cons head rest ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp member with rfl | member
    · have id := layout.1
      omega
    · have tail := ih layout.2.2 member
      have id := layout.1
      omega

private theorem learned_id_after_boundary {s : State} {start : Nat}
    {original learned : List StoredClause} (layout : DatabaseFrom s start (original ++ learned))
    {entry : StoredClause} (member : entry ∈ learned) :
    start + (original.map fun e => e.lits.size + 3).sum + 2 ≤ entry.id := by
  induction original generalizing start with
  | nil => simpa only [List.nil_append, List.map_nil, List.sum_nil, Nat.add_zero] using layout.id_lower member
  | cons head rest ih =>
    have tail := ih layout.2.2
    have id := layout.1
    simp only [List.map_cons, List.sum_cons]
    omega

theorem original_id_lt_fixed {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {entry : StoredClause} (member : entry ∈ original) :
    entry.id < s.fixed := by
  rw [database.fixed]
  exact original_id_before_boundary database.layout member

theorem learned_id_ge_fixed {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {entry : StoredClause} (member : entry ∈ learned) :
    s.fixed ≤ entry.id := by
  have lower := learned_id_after_boundary database.layout member
  rw [database.fixed]
  omega

/-- Every active genuine reason is protected when reduction is invoked at
the root. The implementation locks exactly the forced prefix. -/
theorem activeReason_locked {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (proper : ReasonDatabase s (original ++ learned))
    (root : s.assigned = s.forced) {i : Nat} (before : i < s.assigned)
    (nonzero : s.reason s.trail[i]! ≠ 0) :
    (lockedReasons s)[s.reason s.trail[i]!]! = true := by
  obtain ⟨entry, member, id⟩ := proper i before nonzero
  have packed := database.layout.packed member
  apply lockedReasons_of_index (by simpa only [← root] using before) nonzero
  rw [id]
  exact packed.start_index

theorem activeReason_retained {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (proper : ReasonDatabase s (original ++ learned))
    (root : s.assigned = s.forced) {i : Nat} (before : i < s.assigned)
    {entry : StoredClause} (member : entry ∈ learned) (id : s.reason s.trail[i]! = entry.id)
    (k : Nat) : entry ∈ retainedEntries s (lockedReasons s) k learned := by
  have nonzero : s.reason s.trail[i]! ≠ 0 := by
    rw [id]
    have lower := (database.layout.packed (List.mem_append_right original member)).startLower
    omega
  have locked : (lockedReasons s)[entry.id]! = true := by
    simpa only [id] using activeReason_locked database proper root before nonzero
  apply List.mem_filter.mpr
  exact ⟨member, by simp only [keepEntry, locked, Bool.or_true]⟩

theorem reduceDB_trail (s : State) (k : Nat) : (s.reduceDB k).trail = s.trail := by
  simpa only using congrArg State.trail (reduceDB_restore s k)

/-- Each active nondecision names a genuine retained entry with exactly its
old literal array. Original IDs remain fixed; learned IDs use the real remap. -/
def ReasonRelocations (before after : State) (oldEntries newEntries : List StoredClause) : Prop :=
  ∀ i, i < before.assigned → before.reason before.trail[i]! ≠ 0 →
    ∃ old ∈ oldEntries, ∃ relocated ∈ newEntries,
      before.reason before.trail[i]! = old.id ∧
      after.reason after.trail[i]! = relocated.id ∧ old.lits = relocated.lits

private theorem reason_relocations {s : State} {original learned kept : List StoredClause}
    (database : Database s original learned) (proper : ReasonDatabase s (original ++ learned))
    (arrays : ArrayBounds s) (active : ActiveTrail s) (root : s.assigned = s.forced) (k : Nat)
    (matching : RelocationMatches (compactionResult s k).2.1
      (retainedEntries s (lockedReasons s) k learned) kept) :
    ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept) := by
  intro i before nonzero
  obtain ⟨entry, member, id⟩ := proper i before nonzero
  have literal := (active i before).1
  have index : s.trail[i]!.var < s.reasons.size := by
    rw [arrays.reasonsSize]
    have upper := literal.2
    omega
  have reason := reduceDB_reason k literal.1 literal.2 index
  rw [id] at reason
  rcases List.mem_append.mp member with originalMember | learnedMember
  · have unchanged : ¬s.fixed ≤ entry.id := by have := original_id_lt_fixed database originalMember; omega
    refine ⟨entry, List.mem_append_left learned originalMember, entry,
      List.mem_append_left kept originalMember, id, ?_, rfl⟩
    simpa only [relocatedReason, unchanged, ↓reduceIte, reduceDB_trail] using reason
  · have retained := activeReason_retained database proper root before learnedMember id k
    obtain ⟨relocated, stored, same, remap⟩ := matching.association retained
    refine ⟨entry, List.mem_append_right original learnedMember, relocated,
      List.mem_append_right original stored, id, ?_, same⟩
    have relocatedReasonId : (s.reduceDB k).reason (s.reduceDB k).trail[i]! =
        (compactionResult s k).2.1[entry.id]! := by
      simpa only [relocatedReason, learned_id_ge_fixed database learnedMember, ↓reduceIte,
        reduceDB_trail] using reason
    exact relocatedReasonId.trans remap

private theorem reason_zero_preserved {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (arrays : ArrayBounds s) (active : ActiveTrail s)
    (k : Nat) {i : Nat} (before : i < s.assigned) (zero : s.reason s.trail[i]! = 0) :
    (s.reduceDB k).reason (s.reduceDB k).trail[i]! = 0 := by
  have literal := (active i before).1
  have index : s.trail[i]!.var < s.reasons.size := by
    rw [arrays.reasonsSize]
    have upper := literal.2
    omega
  have fixed : ¬s.fixed ≤ 0 := by have := database.fixed; omega
  rw [reduceDB_trail, reduceDB_reason k literal.1 literal.2 index, zero]
  simp only [relocatedReason, fixed, ↓reduceIte]

private theorem reasonDatabase_of_relocations {s : State} {original learned kept : List StoredClause}
    (database : Database s original learned) (arrays : ArrayBounds s) (active : ActiveTrail s)
    (k : Nat) (relocations : ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept)) :
    ReasonDatabase (s.reduceDB k) (original ++ kept) := by
  intro i before nondecision
  have oldBefore : i < s.assigned := by simpa only [reduceDB_assigned] using before
  have oldNonzero : s.reason s.trail[i]! ≠ 0 :=
    fun zero => nondecision (reason_zero_preserved database arrays active k oldBefore zero)
  obtain ⟨_, _, relocated, member, _, id, _⟩ := relocations i oldBefore oldNonzero
  exact ⟨relocated, member, id⟩

private theorem reasonGraph_of_relocations {formula : Std.Sat.CNF Nat} {s : State}
    {original learned kept : List StoredClause} {rank : Lit → Nat}
    (database : Database s original learned) (arrays : ArrayBounds s) (active : ActiveTrail s)
    (graph : ReasonGraph formula s s.assigned rank) (k : Nat)
    (stored : Database (s.reduceDB k) original kept)
    (relocations : ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept)) :
    ReasonGraph formula (s.reduceDB k) (s.reduceDB k).assigned rank := by
  constructor
  · simpa only [reduceDB_assigned, reduceDB_trail] using graph.countBound
  · simpa only [reduceDB_assigned, reduceDB_trail] using graph.ranks
  · simpa only [reduceDB_assigned, reduceDB_trail] using graph.distinctVariables
  · intro i before nondecision
    have oldBefore : i < s.assigned := by simpa only [reduceDB_assigned] using before
    have oldNonzero : s.reason s.trail[i]! ≠ 0 :=
      fun zero => nondecision (reason_zero_preserved database arrays active k oldBefore zero)
    obtain ⟨lits, packed, nonempty, head, entailed, tails⟩ := graph.clauses i oldBefore oldNonzero
    obtain ⟨old, oldMember, relocated, newMember, oldId, newId, sameLits⟩ :=
      relocations i oldBefore oldNonzero
    have oldPacked : PackedClause s (s.reason s.trail[i]!) old.lits := by
      rw [oldId]
      exact database.layout.packed oldMember
    have exactLits : lits = old.lits := packed.unique oldPacked
    refine ⟨lits, ?_, nonempty, ?_, entailed, ?_⟩
    · rw [newId, exactLits, sameLits]
      exact stored.layout.packed newMember
    · simpa only [reduceDB_trail] using head
    · simpa only [reduceDB_trail] using tails

/-- Actual root reduction preserves all active reason nodes and their DAG.
Retention, ID relocation and literal equality are derived from the real
locking/compaction loops, rather than assumed as output reason clauses. -/
theorem reduceDB_reasons {formula : Std.Sat.CNF Nat} {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} {rank : Lit → Nat}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    (proper : ReasonDatabase s (original ++ learned)) (arrays : ArrayBounds s)
    (active : ActiveTrail s) (graph : ReasonGraph formula s s.assigned rank)
    (root : s.assigned = s.forced) (k : Nat) :
    ∃ kept, Database (s.reduceDB k) original kept ∧ DatabaseMeaning formula original kept ∧
      RelocationMatches (compactionResult s k).2.1
        (retainedEntries s (lockedReasons s) k learned) kept ∧
      ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept) ∧
      ReasonDatabase (s.reduceDB k) (original ++ kept) ∧
      ReasonGraph formula (s.reduceDB k) (s.reduceDB k).assigned rank := by
  obtain ⟨kept, stored, semantic, matching⟩ :=
    reduceDB_database_meaning_of_watchCertificate database meaning certificate k
  have relocations := reason_relocations database proper arrays active root k matching
  exact ⟨kept, stored, semantic, matching, relocations,
    reasonDatabase_of_relocations database arrays active k relocations,
    reasonGraph_of_relocations database arrays active graph k stored relocations⟩

end MicrosatLean.Verification.Implementation.Reduction
