import MicrosatLean.Verification.Implementation.Representation.DatabaseUpdates
import MicrosatLean.Verification.Implementation.Representation.Capacity

namespace MicrosatLean.Verification.Implementation.Representation

open CDCL

private theorem fresh_of_marks {s : State} {lit : Lit} (active : ActiveTrail s)
    (head : s.mark lit = 0) (opposite : s.mark lit.negate = 0) : FreshVariable s lit.var := by
  have encoded := literal_encoding lit
  have negated := literal_encoding lit.negate
  rw [negate_var] at negated
  have different := negate_ne lit
  rcases encoded with positive | negative <;> rcases negated with positive' | negative'
  · exact False.elim (different (positive'.trans positive.symm))
  · exact freshVariable_of_unmarked active ((congrArg s.mark positive).symm.trans head)
      ((congrArg s.mark negative').symm.trans opposite)
  · exact freshVariable_of_unmarked active ((congrArg s.mark positive').symm.trans opposite)
      ((congrArg s.mark negative).symm.trans head)
  · exact False.elim (different (negative'.trans negative.symm))

/-- Active nondecision reasons name genuine stored clause starts. A terminated
suffix that happens to satisfy `PackedClause` is insufficient for this fact. -/
def ReasonDatabase (s : State) (entries : List StoredClause) (count : Nat := s.assigned) : Prop :=
  ∀ i, i < count → s.reason s.trail[i]! ≠ 0 →
    ∃ entry ∈ entries, s.reason s.trail[i]! = entry.id

theorem ReasonDatabase.mono {s : State} {before after : List StoredClause} {count : Nat}
    (proper : ReasonDatabase s before count) (included : before ⊆ after) :
    ReasonDatabase s after count := by
  intro i bound nonzero
  obtain ⟨entry, member, same⟩ := proper i bound nonzero
  exact ⟨entry, included member, same⟩

theorem ReasonDatabase.prefix {s : State} {entries : List StoredClause} {count shorter : Nat}
    (proper : ReasonDatabase s entries count) (bound : shorter ≤ count) :
    ReasonDatabase s entries shorter := fun i before => proper i (Nat.lt_of_lt_of_le before bound)

theorem ReasonDatabase.frame {before after : State} {entries : List StoredClause} {count : Nat}
    (proper : ReasonDatabase before entries count) (trail : after.trail = before.trail)
    (reasons : after.reasons = before.reasons) : ReasonDatabase after entries count := by
  simpa only [ReasonDatabase, State.reason, trail, reasons] using proper

theorem ReasonDatabase.mapEntries {s : State} {entries : List StoredClause} {count : Nat}
    (proper : ReasonDatabase s entries count) (f : StoredClause → StoredClause)
    (ids : ∀ entry, (f entry).id = entry.id) : ReasonDatabase s (entries.map f) count := by
  intro i before nonzero
  obtain ⟨entry, member, same⟩ := proper i before nonzero
  exact ⟨f entry, List.mem_map.mpr ⟨entry, member, rfl⟩, same.trans (ids entry).symm⟩

theorem ReasonDatabase.addClause {s : State} {entries : List StoredClause} {count : Nat}
    (proper : ReasonDatabase s entries count) (lits : Array Lit) (original : Bool) :
    ReasonDatabase (s.addClause lits original).1
      (entries ++ [⟨(s.addClause lits original).2, lits⟩]) count :=
  (proper.frame addClause_trail addClause_reasons).mono (List.subset_append_left _ _)

theorem ReasonDatabase.assign_of_fresh {s : State} {entries : List StoredClause} {entry : StoredClause}
    (proper : ReasonDatabase s entries) (member : entry ∈ entries) (root : Bool)
    (fresh : FreshVariable s (Lit.var (s.db entry.id)))
    (space : s.assigned < s.trail.size) (index : Lit.var (s.db entry.id) < s.reasons.size) :
    ReasonDatabase (s.assign entry.id root) entries := by
  intro i before nonzero
  have upper : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [assign_trail_last space]
    have reason : (s.assign entry.id root).reason (Lit.negate (s.db entry.id)) = entry.id := by
      simpa only [State.reason, negate_var] using (assign_reason (root := root) index)
    exact ⟨entry, member, reason⟩
  · have earlier : i < s.assigned := by omega
    have reason : (s.assign entry.id root).reason s.trail[i]! = s.reason s.trail[i]! :=
      Array.getElem!_set!_ne s.reasons _ _ _ (Ne.symm (fresh i earlier))
    have old : s.reason s.trail[i]! ≠ 0 := by simpa only [assign_trail_prefix earlier, reason] using nonzero
    obtain ⟨prior, stored, id⟩ := proper i earlier old
    exact ⟨prior, stored, by simpa only [assign_trail_prefix earlier, reason] using id⟩

theorem ReasonDatabase.assign {s : State} {entries : List StoredClause} {entry : StoredClause}
    (proper : ReasonDatabase s entries) (member : entry ∈ entries) (root : Bool)
    (arrays : ArrayBounds s) (active : ActiveTrail s) (distinct : DistinctTrailVariables s)
    (head : LiteralBound s.nVars (s.db entry.id))
    (unmarked : s.mark (s.db entry.id) = 0) (opposite : s.mark (Lit.negate (s.db entry.id)) = 0) :
    ReasonDatabase (s.assign entry.id root) entries := by
  have fresh := fresh_of_marks active unmarked opposite
  have room := assigned_lt_of_fresh active distinct fresh head.1 head.2
  apply proper.assign_of_fresh member root fresh
  · rw [arrays.trailSize]
    omega
  · exact (arrays.variable_index head.2).1

theorem ReasonDatabase.restart {s : State} {entries : List StoredClause}
    (proper : ReasonDatabase s entries) (bounds : TrailBounds s) : ReasonDatabase s.restart entries := by
  intro i before nonzero
  have earlier : i < s.assigned := by
    have forced : i < s.forced := by simpa only [restart_assigned bounds] using before
    have := bounds.forcedProcessed
    have := bounds.processedAssigned
    omega
  obtain ⟨entry, member, same⟩ := proper i earlier (by
    simpa only [State.reason, restart_trail, restart_reasons] using nonzero)
  exact ⟨entry, member, by simpa only [State.reason, restart_trail, restart_reasons] using same⟩

theorem ReasonDatabase.decide_of_fresh {s : State} {entries : List StoredClause} {var : Nat}
    (proper : ReasonDatabase s entries) (fresh : FreshVariable s var)
    (space : s.assigned < s.trail.size) (index : var < s.reasons.size) :
    ReasonDatabase (s.decide var) entries := by
  intro i before nonzero
  have upper : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [decide_trail_last space] at nonzero
    have zero : (s.decide var).reason (decisionLiteral s var).negate = 0 := by
      simpa only [State.reason, negate_var, decisionLiteral_var] using decide_reason index
    exact False.elim (nonzero zero)
  · have earlier : i < s.assigned := by omega
    have reason : (s.decide var).reason s.trail[i]! = s.reason s.trail[i]! :=
      Array.getElem!_set!_ne s.reasons _ _ _ (Ne.symm (fresh i earlier))
    have old : s.reason s.trail[i]! ≠ 0 := by simpa only [decide_trail_prefix earlier, reason] using nonzero
    obtain ⟨entry, stored, id⟩ := proper i earlier old
    exact ⟨entry, stored, by simpa only [decide_trail_prefix earlier, reason] using id⟩

theorem ReasonDatabase.decide {s : State} {entries : List StoredClause} {var : Nat}
    (proper : ReasonDatabase s entries) (arrays : ArrayBounds s) (active : ActiveTrail s)
    (distinct : DistinctTrailVariables s) (lower : 1 ≤ var) (upper : var ≤ s.nVars)
    (positive : s.mark (2 * var) = 0) (negative : s.mark (2 * var + 1) = 0) :
    ReasonDatabase (s.decide var) entries :=
  proper.decide_of_fresh (freshVariable_of_unmarked active positive negative)
    (assignment_space_of_unmarked arrays active distinct lower upper positive negative)
    (arrays.variable_index upper).1

theorem ReasonDatabase.setMark {s : State} {entries : List StoredClause} {count : Nat}
    (proper : ReasonDatabase s entries count) (lit value : Nat) :
    ReasonDatabase (s.setMark lit value) entries count := proper.frame rfl rfl

theorem ReasonDatabase.bump {s : State} {entries : List StoredClause} {count : Nat}
    (proper : ReasonDatabase s entries count) (lit : Lit) : ReasonDatabase (s.bump lit) entries count :=
  proper.frame bump_trail bump_reasons

end MicrosatLean.Verification.Implementation.Representation
