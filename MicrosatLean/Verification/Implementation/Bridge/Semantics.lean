import MicrosatLean.Verification.Implementation.Bridge.View

namespace MicrosatLean.Verification.Implementation.Bridge

@[simp] theorem logicalView_database (s : CDCL.State)
    (original learned : List Representation.StoredClause) :
    (logicalView s original learned).database =
      (original ++ learned).map Representation.StoredClause.view := by
  simp [logicalView, LogicalState.database]

theorem view_true_of_falsifies (valuation : Assignment) (lit : Lit)
    (falseValue : Representation.Falsifies valuation lit) :
    valuation (literalView lit).negate.1 = (literalView lit).negate.2 := by
  change valuation lit.var ≠ (lit % 2 == 0) at falseValue
  change valuation lit.var = !(lit % 2 == 0)
  cases left : valuation lit.var <;> cases right : (lit % 2 == 0) <;> simp_all

theorem view_semantic {formula : Formula} {m : CDCL.Machine}
    {original learned : List Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    {order : List Nat} (ordered : Representation.MTFOrder m.solver order) :
    SemanticInv (formulaView formula) (logicalView m.solver original learned) := by
  let a := logicalView m.solver original learned
  let w := representationWitness original learned heads order
  let s := m.solver
  have represented : Rep m a w := view_rep base ordered
  refine ⟨base.meaning.original, base.meaning.learned,
    by simpa [logicalView] using Nat.le_trans base.bounds.forcedProcessed base.bounds.processedAssigned,
    by simpa [a, logicalView] using base.bounds.assignedVars,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro lit member
    obtain ⟨entry, contains, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, before, equal⟩ := List.mem_iff_getElem.mp contains
    have active : i < s.assigned := by simpa [a, logicalView] using before
    have bound := (base.active i active).1
    have value := represented.trail i active
    rw [getElem!_pos a.trail i before, equal] at value
    rw [value]
    exact bound
  · apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j beforeI beforeJ same
    have activeI : i < s.assigned := by simpa [LogicalState.trueTrail, a, logicalView] using beforeI
    have activeJ : j < s.assigned := by simpa [LogicalState.trueTrail, a, logicalView] using beforeJ
    apply base.distinct i j activeI activeJ
    have logical : a.trail[i]!.literal.1 = a.trail[j]!.literal.1 := by
      simpa [LogicalState.trueTrail, getElem!_pos a.trail i (by simpa [a, logicalView] using activeI),
        getElem!_pos a.trail j (by simpa [a, logicalView] using activeJ)] using same
    simpa only [trail_var represented activeI, trail_var represented activeJ] using logical
  · intro clause member lit contains
    rw [logicalView_database] at member
    obtain ⟨entry, stored, rfl⟩ := List.mem_map.mp member
    obtain ⟨encoded, encodedMember, equal⟩ := clauseView_mem.mp contains
    rw [← equal]
    exact (base.database.layout.packed stored).wellFormed encoded encodedMember
  · intro clause member empty
    rw [logicalView_database] at member
    obtain ⟨entry, stored, rfl⟩ := List.mem_map.mp member
    have length := congrArg List.length empty
    simp only [Representation.StoredClause.view, clauseView_literals,
      List.length_map, Array.length_toList, List.length_nil] at length
    have positive := base.nonempty entry stored
    omega
  · intro i before clause reason
    have active : i < s.assigned := by simpa [a, logicalView] using before
    change (trailView s (original ++ learned))[i]!.reason = some clause at reason
    rw [trailView_get _ _ active] at reason
    by_cases zero : s.reason s.trail[i]! = 0
    · simp only [reasonView, zero, ↓reduceIte] at reason
      cases reason
    · obtain ⟨entry, stored, id, selected⟩ := reasonView_some base.reasons active zero
      have sameClause : entry.view = clause := Option.some.inj (selected.symm.trans reason)
      subst clause
      obtain ⟨lits, packed, positive, head, entailed, tails⟩ := base.graph.clauses i active zero
      have entryPacked : Representation.PackedClause s (s.reason s.trail[i]!) entry.lits := by
        rw [id]
        exact base.database.layout.packed stored
      have same := packed.unique entryPacked
      subst lits
      refine ⟨entailed, ?_, ?_⟩
      · change (clauseView entry.lits).literals.head? = (some (trailView s (original ++ learned))[i]!.literal)
        rw [trailView_get _ _ active]
        simp only [clauseView_literals, List.head?_eq_getElem?, List.getElem?_map, Array.getElem?_toList,
          Array.getElem?_eq_getElem positive, Option.map_some]
        rw [← getElem!_pos entry.lits 0 positive, head, literalView_negate]
      · intro lit member
        have words : (entry.view).literals = entry.lits.toList.map literalView := clauseView_literals _
        rw [words] at member
        obtain ⟨j, beforeTail, value⟩ := List.mem_iff_getElem.mp member
        have beforeWord : j + 1 < entry.lits.size := by
          have size : (entry.lits.toList.map literalView).length = entry.lits.size := by simp
          rw [List.length_tail, size] at beforeTail
          omega
        have viewed : literalView entry.lits[j + 1]! = lit := by
          simpa [List.getElem_tail, getElem!_pos entry.lits (j + 1) beforeWord] using value
        rw [← viewed]
        exact (falseBefore_iff represented (Nat.le_of_lt active) _).mpr
          (tails (j + 1) (by omega) beforeWord)
  · intro lit member valuation model
    obtain ⟨i, before, value⟩ := (prefix_mem_iff
      (by simpa [a, logicalView] using Nat.le_trans base.bounds.forcedProcessed base.bounds.processedAssigned) lit).mp member
    have active : i < s.assigned := Nat.lt_of_lt_of_le before
      (Nat.le_trans base.bounds.forcedProcessed base.bounds.processedAssigned)
    have root : s.mark s.trail[i]! = 6 := base.rootPrefix i before
    have falseValue := base.roots s.trail[i]! ⟨i, active, rfl⟩ root valuation model
    rw [← value, represented.trail i active]
    exact view_true_of_falsifies valuation _ falseValue

end MicrosatLean.Verification.Implementation.Bridge
