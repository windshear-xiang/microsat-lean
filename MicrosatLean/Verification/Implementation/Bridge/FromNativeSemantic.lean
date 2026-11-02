import MicrosatLean.Verification.Implementation.Bridge.FromNativeBase

namespace MicrosatLean.Verification.Implementation.Bridge

@[simp] theorem nativeState_database (s : CDCL.State)
    (original learned : List Native.Representation.StoredClause) :
    (nativeState s original learned).database =
      (original ++ learned).map Native.Representation.StoredClause.view := by
  simp [nativeState, LogicalState.database]

theorem native_true_of_falsifies (valuation : Assignment) (lit : Lit)
    (falseValue : Native.Representation.Falsifies valuation lit) :
    valuation (literalView lit).negate.1 = (literalView lit).negate.2 := by
  change valuation lit.var ≠ (lit % 2 == 0) at falseValue
  change valuation lit.var = !(lit % 2 == 0)
  cases left : valuation lit.var <;> cases right : (lit % 2 == 0) <;> simp_all

theorem native_semantic {formula : Formula} {m : CDCL.Machine}
    {original learned : List Native.Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Native.Search.StateCertificate (formulaView formula) m.solver original learned heads rank)
    {order : List Nat} (ordered : Native.Representation.MTFOrder m.solver order) :
    SemanticInv (formulaView formula) (nativeState m.solver original learned) := by
  let a := nativeState m.solver original learned
  let w := nativeWitness original learned heads order
  let s := m.solver
  have represented : Rep m a w := native_rep base ordered
  refine ⟨base.meaning.original, base.meaning.learned,
    by simpa [nativeState] using Nat.le_trans base.bounds.forcedProcessed base.bounds.processedAssigned,
    by simpa [a, nativeState] using base.bounds.assignedVars,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro lit member
    obtain ⟨entry, contains, rfl⟩ := List.mem_map.mp member
    obtain ⟨i, before, equal⟩ := List.mem_iff_getElem.mp contains
    have active : i < s.assigned := by simpa [a, nativeState] using before
    have bound := (base.active i active).1
    have value := represented.trail i active
    rw [getElem!_pos a.trail i before, equal] at value
    rw [value]
    exact bound
  · apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j beforeI beforeJ same
    have activeI : i < s.assigned := by simpa [LogicalState.trueTrail, a, nativeState] using beforeI
    have activeJ : j < s.assigned := by simpa [LogicalState.trueTrail, a, nativeState] using beforeJ
    apply base.distinct i j activeI activeJ
    have logical : a.trail[i]!.literal.1 = a.trail[j]!.literal.1 := by
      simpa [LogicalState.trueTrail, getElem!_pos a.trail i (by simpa [a, nativeState] using activeI),
        getElem!_pos a.trail j (by simpa [a, nativeState] using activeJ)] using same
    simpa only [trail_var represented activeI, trail_var represented activeJ] using logical
  · intro clause member lit contains
    rw [nativeState_database] at member
    obtain ⟨entry, stored, rfl⟩ := List.mem_map.mp member
    obtain ⟨encoded, encodedMember, equal⟩ := Native.clauseView_mem.mp contains
    rw [← equal]
    exact (base.database.layout.packed stored).wellFormed encoded encodedMember
  · intro clause member empty
    rw [nativeState_database] at member
    obtain ⟨entry, stored, rfl⟩ := List.mem_map.mp member
    have length := congrArg List.length empty
    simp only [Native.Representation.StoredClause.view, Native.clauseView_literals,
      List.length_map, Array.length_toList, List.length_nil] at length
    have positive := base.nonempty entry stored
    omega
  · intro i before clause reason
    have active : i < s.assigned := by simpa [a, nativeState] using before
    change (nativeTrail s (original ++ learned))[i]!.reason = some clause at reason
    rw [nativeTrail_get _ _ active] at reason
    by_cases zero : s.reason s.trail[i]! = 0
    · simp only [nativeReason, zero, ↓reduceIte] at reason
      cases reason
    · obtain ⟨entry, stored, id, selected⟩ := nativeReason_some base.reasons active zero
      have sameClause : entry.view = clause := Option.some.inj (selected.symm.trans reason)
      subst clause
      obtain ⟨lits, packed, positive, head, entailed, tails⟩ := base.graph.clauses i active zero
      have entryPacked : Native.Representation.PackedClause s (s.reason s.trail[i]!) entry.lits := by
        rw [id]
        exact base.database.layout.packed stored
      have same := packed.unique entryPacked
      subst lits
      refine ⟨entailed, ?_, ?_⟩
      · change (clauseView entry.lits).literals.head? = (some (nativeTrail s (original ++ learned))[i]!.literal)
        rw [nativeTrail_get _ _ active]
        simp only [clauseView_literals, List.head?_eq_getElem?, List.getElem?_map, Array.getElem?_toList,
          Array.getElem?_eq_getElem positive, Option.map_some]
        rw [← getElem!_pos entry.lits 0 positive, head, literalView_negate]
      · intro lit member
        have words : (entry.view).literals = entry.lits.toList.map literalView := Native.clauseView_literals _
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
      (by simpa [a, nativeState] using Nat.le_trans base.bounds.forcedProcessed base.bounds.processedAssigned) lit).mp member
    have active : i < s.assigned := Nat.lt_of_lt_of_le before
      (Nat.le_trans base.bounds.forcedProcessed base.bounds.processedAssigned)
    have root : s.mark s.trail[i]! = 6 := base.rootPrefix i before
    have falseValue := base.roots s.trail[i]! ⟨i, active, rfl⟩ root valuation model
    rw [← value, represented.trail i active]
    exact native_true_of_falsifies valuation _ falseValue

end MicrosatLean.Verification.Implementation.Bridge
