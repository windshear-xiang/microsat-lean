import MicrosatLean.Verification.Implementation.Bridge.AnalysisTraceBase

namespace MicrosatLean.Verification.Implementation.Bridge

private abbrev NativeEntry := Native.Representation.StoredClause

/-- Actual conflict analysis refines learning followed by backjumping. The
learned clause is justified by the native resolution/minimization proof; the
old reason lookups survive allocation and the retained trail is a prefix. -/
theorem native_analyze_trace {input : CNF} {s : CDCL.State}
    {original learned : List NativeEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    (entry : Native.Analysis.AnalysisTransitionEntry input s conflict lits rank decision) :
    let added : NativeEntry := ⟨(CDCL.analyze s conflict).2, Native.Analysis.analysisLearned s conflict⟩
    LogicalExecution input (nativeState s original learned)
      (nativeState (CDCL.analyze s conflict).1 original (learned ++ [added])) := by
  dsimp only
  let added : NativeEntry := ⟨(CDCL.analyze s conflict).2, Native.Analysis.analysisLearned s conflict⟩
  have ready := entry.ready
  have first : LogicalExecution input (nativeState s original learned)
      (nativeState s original (learned ++ [added])) := by
    rw [nativeState_learn base.reasons added]
    apply Logic.single_move
    apply LogicalMove.learn
    · exact ready.entailed
    · intro lit member
      obtain ⟨encoded, contains, same⟩ := Native.clauseView_mem.mp member
      rw [← same]
      have bound := ready.packed.wellFormed encoded contains
      change 0 < encoded.var ∧ encoded.var ≤ s.nVars
      rw [Native.Search.analyze_nVars] at bound
      exact ⟨by have := bound.1; omega, bound.2⟩
    · intro empty
      change (clauseView (Native.Analysis.analysisLearned s conflict)).literals = [] at empty
      have size := congrArg List.length empty
      simp only [clauseView_literals,
        List.length_map, Array.length_toList, List.length_nil] at size
      have := ready.nonempty
      omega
  have second : LogicalExecution input (nativeState s original (learned ++ [added]))
      (nativeState (CDCL.analyze s conflict).1 original (learned ++ [added])) := by
    rw [nativeState_analyze_prefix base entry]
    apply Logic.single_move
    apply LogicalMove.backjump
    · change s.forced ≤ (CDCL.analyze s conflict).1.assigned
      rw [← Native.Analysis.analyze_forced s conflict]
      exact Nat.le_trans ready.bounds.forcedProcessed ready.bounds.processedAssigned
    · simpa only [nativeState, nativeTrail_length] using
        Nat.le_of_lt (Native.Analysis.analyze_assigned_lt entry.decisionEntry)
  exact Logic.execution_trans first second

/-- The asserting head returned by the real analyzer is a unit of its newly
allocated learned clause. Assignment therefore refines one propagation move. -/
theorem native_analysis_assert_trace {input : CNF} {s : CDCL.State}
    {original learned : List NativeEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    (entry : Native.Analysis.AnalysisTransitionEntry input s conflict lits rank decision)
    (root : Bool) :
    let result := CDCL.analyze s conflict
    let added : NativeEntry := ⟨result.2, Native.Analysis.analysisLearned s conflict⟩
    LogicalExecution input (nativeState result.1 original (learned ++ [added]))
      (nativeState (result.1.assign result.2 root) original (learned ++ [added])) := by
  dsimp only
  let result := CDCL.analyze s conflict
  let added : NativeEntry := ⟨result.2, Native.Analysis.analysisLearned s conflict⟩
  have ready := entry.ready
  have stored := Native.Analysis.analyze_database_meaning entry.semantic base.database base.meaning
  have member : added ∈ original ++ (learned ++ [added]) := by simp
  have positive : 0 < added.lits.size := ready.nonempty
  apply native_assign_trace stored.1 ready.arrays ready.active ready.distinct member
    ready.nonempty ready.head ready.opposite ?_ ?_ ?_ root
  · change (clauseView added.lits).literals.head? = some (literalView (result.1.db added.id))
    simp only [clauseView_literals, List.head?_eq_getElem?, List.getElem?_map,
      Array.getElem?_toList, Array.getElem?_eq_getElem positive, Option.map_some]
    rw [← getElem!_pos added.lits 0 positive]
    exact congrArg (some ∘ literalView) (ready.packed.literals 0 ready.nonempty).symm
  · exact nativeState_fresh
      (Native.Analysis.freshVariable_of_unmarked_literal ready.active ready.head ready.opposite)
  · intro lit contains
    have words : added.view.literals = added.lits.toList.map literalView := Native.clauseView_literals _
    rw [words] at contains
    obtain ⟨j, beforeTail, value⟩ := List.mem_iff_getElem.mp contains
    have beforeWord : j + 1 < added.lits.size := by
      have size : (added.lits.toList.map literalView).length = added.lits.size := by simp
      rw [List.length_tail, size] at beforeTail
      omega
    have viewed : literalView added.lits[j + 1]! = lit := by
      simpa [List.getElem_tail, getElem!_pos added.lits (j + 1) beforeWord] using value
    rw [← viewed]
    exact (nativeState_false_iff result.1 original (learned ++ [added]) _).mpr
      (ready.tails (j + 1) (by omega) beforeWord)

/-- The complete concrete analyzer/assertion call performs exactly the
logical learning, backjumping, and asserting propagation justified above. -/
theorem native_analyze_assign_trace {input : CNF} {s : CDCL.State}
    {original learned : List NativeEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (base : Native.Search.StateCertificate input s original learned heads rank)
    (entry : Native.Analysis.AnalysisTransitionEntry input s conflict lits rank decision)
    (root : Bool) :
    let result := CDCL.analyze s conflict
    let added : NativeEntry := ⟨result.2, Native.Analysis.analysisLearned s conflict⟩
    LogicalExecution input (nativeState s original learned)
      (nativeState (result.1.assign result.2 root) original (learned ++ [added])) :=
  Logic.execution_trans (native_analyze_trace base entry)
    (native_analysis_assert_trace base entry root)

end MicrosatLean.Verification.Implementation.Bridge
