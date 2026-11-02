import MicrosatLean.Verification.Implementation.Bridge.Trail
import MicrosatLean.Verification.Implementation.Bridge.Semantics
import MicrosatLean.Verification.Implementation.Logic.Execution

namespace MicrosatLean.Verification.Implementation.Bridge

theorem find_clause_view {s : CDCL.State} {original learned : List StoredClause}
    (database : Representation.Database s original learned)
    {entry : StoredClause} (member : entry ∈ original ++ learned) :
    ((original ++ learned).find? (fun item => item.id == entry.id)).map
      Representation.StoredClause.view = some entry.view := by
  cases found : (original ++ learned).find? (fun item => item.id == entry.id) with
  | none =>
    have absent := (List.find?_eq_none.mp found) entry member
    exact False.elim (absent (by simp))
  | some selected =>
    have selectedMember := List.mem_of_find?_eq_some found
    have sameId : selected.id = entry.id := by simpa only [beq_iff_eq] using List.find?_some found
    have same := database.layout.entry_eq_of_id selectedMember member sameId
    simp only [same, Option.map_some]

/-- Concrete assignment changes only the new trail slot and the fresh
variable's reason. Looking up reasons by genuine clause ID preserves every
old logical entry, and the new entry records exactly the propagated clause. -/
theorem trailView_assign {s : CDCL.State} {original learned : List StoredClause}
    (database : Representation.Database s original learned)
    (arrays : Representation.ArrayBounds s)
    (active : Representation.ActiveTrail s)
    (distinct : Representation.DistinctTrailVariables s)
    {entry : StoredClause} (member : entry ∈ original ++ learned)
    (nonempty : 0 < entry.lits.size)
    (head : s.mark (s.db entry.id) = 0) (opposite : s.mark (Lit.negate (s.db entry.id)) = 0)
    (root : Bool) :
    trailView (s.assign entry.id root) (original ++ learned) =
      trailView s (original ++ learned) ++ [⟨literalView (s.db entry.id), some entry.view⟩] := by
  have packed := database.layout.packed member
  have headValue : s.db entry.id = entry.lits[0]! := by simpa using packed.literals 0 nonempty
  have headMember : s.db entry.id ∈ entry.lits := by
    rw [headValue, getElem!_pos entry.lits 0 nonempty]
    exact Array.getElem_mem nonempty
  have declared := packed.wellFormed _ headMember
  have fresh := Analysis.freshVariable_of_unmarked_literal active head opposite
  have room := Representation.assigned_lt_of_fresh active distinct fresh declared.1 declared.2
  have space : s.assigned < s.trail.size := by rw [arrays.trailSize]; omega
  have reasonBound : Lit.var (s.db entry.id) < s.reasons.size := by
    rw [arrays.reasonsSize]
    exact Nat.lt_succ_of_le declared.2
  have lastCode : (s.assign entry.id root).reason (s.assign entry.id root).trail[s.assigned]! = entry.id := by
    rw [Representation.assign_trail_last space]
    change (s.reasons.set! (Lit.var (s.db entry.id)) entry.id)[Lit.var (Lit.negate (s.db entry.id))]! = entry.id
    rw [Representation.negate_var]
    exact Array.getElem!_set!_self _ _ _ reasonBound
  apply trailView_append_of_get _ rfl
  · intro i before
    constructor
    · rw [Representation.assign_trail_prefix before]
    · apply reasonView_eq_of_code
      rw [Representation.assign_trail_prefix before]
      exact Analysis.assign_reason_prefix fresh before
  · rw [Representation.assign_trail_last space, literalView_negate]
    simp only [Std.Sat.Literal.negate, Bool.not_not]
  · have nonzero : entry.id ≠ 0 := by have := packed.startLower; omega
    simp only [reasonView, lastCode, nonzero, ↓reduceIte]
    exact find_clause_view database member

theorem logicalView_assign {s : CDCL.State} {original learned : List StoredClause}
    (database : Representation.Database s original learned)
    (arrays : Representation.ArrayBounds s)
    (active : Representation.ActiveTrail s)
    (distinct : Representation.DistinctTrailVariables s)
    {entry : StoredClause} (member : entry ∈ original ++ learned)
    (nonempty : 0 < entry.lits.size)
    (head : s.mark (s.db entry.id) = 0) (opposite : s.mark (Lit.negate (s.db entry.id)) = 0)
    (root : Bool) :
    logicalView (s.assign entry.id root) original learned =
      appendEntry (logicalView s original learned) (literalView (s.db entry.id)) (some entry.view) := by
  have trail := trailView_assign database arrays active distinct member nonempty head opposite root
  change LogicalState.mk _ _ _ _ _ = LogicalState.mk _ _ _ _ _
  rw [trail]
  rfl

/-- The semantic unit premises come from the real failed replacement scan.
This lemma handles only the assignment writes and their logical interpretation. -/
theorem view_assign_trace {input : CNF} {s : CDCL.State}
    {original learned : List StoredClause}
    (database : Representation.Database s original learned)
    (arrays : Representation.ArrayBounds s)
    (active : Representation.ActiveTrail s)
    (distinct : Representation.DistinctTrailVariables s)
    {entry : StoredClause} (member : entry ∈ original ++ learned)
    (nonempty : 0 < entry.lits.size)
    (head : s.mark (s.db entry.id) = 0) (opposite : s.mark (Lit.negate (s.db entry.id)) = 0)
    (logicalHead : entry.view.literals.head? = some (literalView (s.db entry.id)))
    (fresh : Unassigned (logicalView s original learned).trueTrail (literalView (s.db entry.id)).1)
    (tails : ∀ lit ∈ entry.view.literals.tail, FalseIn (logicalView s original learned).trueTrail lit)
    (root : Bool) :
    LogicalExecution input (logicalView s original learned)
      (logicalView (s.assign entry.id root) original learned) := by
  rw [logicalView_assign database arrays active distinct member nonempty head opposite root]
  apply Logic.single_move
  exact .propagate _ entry.view _ (by rw [logicalView_database]; exact List.mem_map.mpr ⟨entry, member, rfl⟩)
    logicalHead fresh tails

/-- Convert the physical reason-tail premises once, for unit propagation and
the asserting assignment after analysis. No output invariant is assumed. -/
theorem view_unit_trace {input : CNF} {s : CDCL.State}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate input s original learned heads rank)
    {entry : StoredClause} (member : entry ∈ original ++ learned)
    (nonempty : 0 < entry.lits.size)
    (head : s.mark (s.db entry.id) = 0) (opposite : s.mark (Lit.negate (s.db entry.id)) = 0)
    (tails : ∀ j, 0 < j → j < entry.lits.size →
      Analysis.TrailMember s s.assigned entry.lits[j]!) (root : Bool) :
    LogicalExecution input (logicalView s original learned)
      (logicalView (s.assign entry.id root) original learned) := by
  obtain ⟨order, ordered⟩ := base.order
  let machine : CDCL.Machine := { solver := s, decision := s.head }
  have represented := view_rep (m := machine) base ordered
  have packed := base.database.layout.packed member
  apply view_assign_trace base.database base.arrays base.active base.distinct member nonempty head opposite
  · simp only [Representation.StoredClause.view, clauseView_literals,
      List.head?_eq_getElem?, List.getElem?_map, Array.getElem?_toList,
      Array.getElem?_eq_getElem nonempty, Option.map_some]
    rw [← getElem!_pos entry.lits 0 nonempty, ← packed.literals 0 nonempty]
    rfl
  · have fresh := Analysis.freshVariable_of_unmarked_literal base.active head opposite
    intro lit contains same
    obtain ⟨trailEntry, contained, rfl⟩ := List.mem_map.mp contains
    obtain ⟨i, active, value⟩ := List.mem_iff_getElem.mp contained
    have before : i < s.assigned := by simpa only [logicalView, trailView_length] using active
    have literal := represented.trail i before
    have variableEq : trailEntry.literal.1 = s.trail[i]!.var := by
      rw [← value]
      simpa only [machine, getElem!_pos (logicalView s original learned).trail i active,
        literalView, Std.Sat.Literal.negate] using congrArg (fun x : Literal => x.1) literal
    apply fresh i before
    exact variableEq.symm.trans same
  · intro lit contained
    have words : entry.view.literals = entry.lits.toList.map literalView := clauseView_literals _
    rw [words] at contained
    obtain ⟨j, beforeTail, value⟩ := List.mem_iff_getElem.mp contained
    have beforeWord : j + 1 < entry.lits.size := by
      have size : (entry.lits.toList.map literalView).length = entry.lits.size := by simp
      rw [List.length_tail, size] at beforeTail
      omega
    have viewed : literalView entry.lits[j + 1]! = lit := by
      simpa [List.getElem_tail, getElem!_pos entry.lits (j + 1) beforeWord] using value
    rw [← viewed]
    have old := tails (j + 1) (by omega) beforeWord
    have logical := (falseBefore_iff represented (Nat.le_refl s.assigned) _).mpr old
    have whole : (trailView s (original ++ learned)).take s.assigned =
        trailView s (original ++ learned) := List.take_of_length_le (by simp)
    simpa only [FalseBefore, prefixLiterals, machine, logicalView, whole,
      LogicalState.trueTrail] using logical

end MicrosatLean.Verification.Implementation.Bridge
