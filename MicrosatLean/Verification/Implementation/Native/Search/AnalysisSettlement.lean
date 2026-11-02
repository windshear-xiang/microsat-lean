import MicrosatLean.Verification.Implementation.Native.Search.AnalysisState
import MicrosatLean.Verification.Implementation.Native.Analysis.WatchBirth

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Analysis Propagation Std.Sat

private theorem assertion_space {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    (CDCL.analyze s conflict).1.assigned < (CDCL.analyze s conflict).1.trail.size := by
  have ready := entry.ready
  have first : (CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2 = (analysisLearned s conflict)[0]! := by
    simpa using ready.packed.literals 0 ready.nonempty
  have member : (CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2 ∈ analysisLearned s conflict := by
    rw [first, getElem!_pos _ 0 ready.nonempty]
    exact Array.getElem_mem ready.nonempty
  have literal := ready.packed.wellFormed _ member
  have fresh := freshVariable_of_unmarked_literal ready.active ready.head ready.opposite
  have room := assigned_lt_of_fresh ready.active ready.distinct fresh literal.1 literal.2
  rw [ready.arrays.trailSize]
  omega

private theorem asserted_head_true {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) (root : Bool) :
    let result := CDCL.analyze s conflict
    TrueBefore (result.1.assign result.2 root) (result.1.assign result.2 root).assigned
      (analysisLearned s conflict)[0]! := by
  dsimp only
  have first : (CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2 = (analysisLearned s conflict)[0]! := by
    simpa using entry.ready.packed.literals 0 entry.ready.nonempty
  refine ⟨(CDCL.analyze s conflict).1.assigned, by change _ < _ + 1; omega, ?_⟩
  rw [assign_trail_last (assertion_space entry), first]

private theorem asserted_not_false_head {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) (root : Bool)
    (count : Nat) (bound : count ≤ (CDCL.analyze s conflict).1.assigned) :
    ¬ FalseBefore ((CDCL.analyze s conflict).1.assign (CDCL.analyze s conflict).2 root) count
      (analysisLearned s conflict)[0]! := by
  rintro ⟨i, before, value⟩
  have old : i < (CDCL.analyze s conflict).1.assigned := by omega
  rw [assign_trail_prefix old] at value
  have fresh := freshVariable_of_unmarked_literal entry.ready.active entry.ready.head entry.ready.opposite
  apply fresh i old
  have first : (CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2 = (analysisLearned s conflict)[0]! := by
    simpa using entry.ready.packed.literals 0 entry.ready.nonempty
  rw [first]
  exact congrArg Lit.var value

private theorem asserted_old_decision {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) (root : Bool)
    (index : Nat) (before : index < ((CDCL.analyze s conflict).1.assign (CDCL.analyze s conflict).2 root).assigned)
    (zero : ((CDCL.analyze s conflict).1.assign (CDCL.analyze s conflict).2 root).reason
      ((CDCL.analyze s conflict).1.assign (CDCL.analyze s conflict).2 root).trail[index]! = 0) :
    index < (CDCL.analyze s conflict).1.assigned ∧ s.reason s.trail[index]! = 0 := by
  let result := CDCL.analyze s conflict
  have ready := entry.ready
  have first : result.1.db result.2 = (analysisLearned s conflict)[0]! := by
    simpa using ready.packed.literals 0 ready.nonempty
  have member : result.1.db result.2 ∈ analysisLearned s conflict := by
    rw [first, getElem!_pos _ 0 ready.nonempty]
    exact Array.getElem_mem ready.nonempty
  have literal := ready.packed.wellFormed _ member
  have old : index < result.1.assigned := by
    have limit : index < result.1.assigned + 1 := before
    by_cases last : index = result.1.assigned
    · subst index
      rw [assign_trail_last (assertion_space entry)] at zero
      have actual : (result.1.assign result.2 root).reason (Lit.negate (result.1.db result.2)) = result.2 := by
        simpa only [State.reason, negate_var] using assign_reason (root := root) (ready.arrays.variable_index literal.2).1
      have lower : 4 ≤ result.2 := ready.packed.startLower
      have equal := actual.symm.trans zero
      exact False.elim ((by omega : result.2 ≠ 0) equal)
    · omega
  have fresh := freshVariable_of_unmarked_literal ready.active ready.head ready.opposite
  rw [assign_trail_prefix old, assign_reason_prefix fresh old] at zero
  exact ⟨old, by simpa only [State.reason, analyze_trail, Analysis.analyze_reasons] using zero⟩

/-- Real analysis restores all old completed watches from its saved decision
prefix; allocation's newly false tail watch is satisfied by the actual
asserting head. No after-settlement premise is used. -/
theorem StateCertificate.analyze_settled {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionWatchHistory s (original ++ learned) heads)
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) (root : Bool) :
    let result := CDCL.analyze s conflict
    SettledPrefix (result.1.assign result.2 root)
      (original ++ (learned ++ [⟨result.2, analysisLearned s conflict⟩]))
      (analysisHeads s conflict heads) result.1.assigned := by
  let before := analysisBeforeStore s conflict
  let result := CDCL.analyze s conflict
  let after := result.1.assign result.2 root
  have count : result.1.assigned = before.assigned := by
    change (CDCL.analyze s conflict).1.assigned = (analysisBeforeStore s conflict).assigned
    rw [analyze_eq_addClause, addClause_assigned]
  have id : result.2 = before.arena.size + 2 := by
    change (CDCL.analyze s conflict).2 = (analysisBeforeStore s conflict).arena.size + 2
    rw [analyze_eq_addClause, addClause_id]
  have database : Database before original learned := certificate.database.frame
    (analysisBeforeStore_arena _ _) (analysisBeforeStore_nVars _ _) (analysisBeforeStore_fixed _ _)
    (analysisBeforeStore_nLemmas _ _)
  have watches : WatchCertificate before (original ++ learned) heads := certificate.watches.frameArrays
    (analysisBeforeStore_arena _ _) (analysisBeforeStore_first _ _)
  have boundary := analyze_decision_boundary entry.decisionEntry
  have old := history _ boundary.1 (analyze_assigned_lt entry.decisionEntry) boundary.2.2
  have oldBefore : SettledWatches before (original ++ learned) heads before.assigned := by
    rw [← count]
    exact settledWatches_transfer old (fun i _ => congrArg (fun words : Array Lit => words[i]!) (analysisBeforeStore_trail s conflict))
  have equal : PrefixLiterals before after before.assigned := by
    intro i bound
    have old : i < result.1.assigned := by rw [count]; exact bound
    rw [assign_trail_prefix old]
    change (CDCL.analyze s conflict).1.trail[i]! = (analysisBeforeStore s conflict).trail[i]!
    rw [analyze_eq_addClause, addClause_trail]
  have settled := settled_allocate (lits := analysisLearned s conflict) database watches oldBefore equal
    (truthCount := after.assigned) (by change before.assigned ≤ result.1.assigned + 1; omega)
    (by
      intro _ falseHead
      exact False.elim (asserted_not_false_head entry root before.assigned (Nat.le_of_eq count.symm) falseHead))
    (by intro _ _; exact asserted_head_true entry root)
  change SettledPrefix after (original ++ (learned ++ [⟨result.2, analysisLearned s conflict⟩]))
    (analysisHeads s conflict heads) result.1.assigned
  simpa only [SettledPrefix, id, count, analysisHeads, List.append_assoc] using settled

/-- Every old unit is true in the retained decision prefix, and a newly
learned unit is true at the actual asserting slot. Thus unit truth survives
the full analyzer/allocator/assertion branch independently of old witnesses. -/
theorem StateCertificate.analyze_units {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (_certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned))
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) (root : Bool) :
    let result := CDCL.analyze s conflict
    ∀ old ∈ original ++ (learned ++ [⟨result.2, analysisLearned s conflict⟩]), old.lits.size = 1 →
      TrueBefore (result.1.assign result.2 root) (result.1.assign result.2 root).assigned old.lits[0]! := by
  dsimp only
  intro old member unit
  rw [← List.append_assoc] at member
  rcases List.mem_append.mp member with prior | added
  · exact trueBefore_assign (DecisionHistory.analyze_old_units history entry.decisionEntry old prior unit)
  · have equal : old = ⟨(CDCL.analyze s conflict).2, analysisLearned s conflict⟩ := List.mem_singleton.mp added
    subst old
    exact asserted_head_true entry root

/-- Retained decisions keep their old exact watch prefixes. Neither new
watched literal of the learned clause occurs falsely before such a decision:
the head was fresh, and its highest tail is at or above every retained
decision. Thus the actual allocation also preserves saved watch history. -/
theorem StateCertificate.analyze_saved {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionWatchHistory s (original ++ learned) heads)
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) (root : Bool) :
    let result := CDCL.analyze s conflict
    DecisionWatchHistory (result.1.assign result.2 root)
      (original ++ (learned ++ [⟨result.2, analysisLearned s conflict⟩])) (analysisHeads s conflict heads) := by
  let before := analysisBeforeStore s conflict
  let result := CDCL.analyze s conflict
  let after := result.1.assign result.2 root
  have count : result.1.assigned = before.assigned := by
    change (CDCL.analyze s conflict).1.assigned = (analysisBeforeStore s conflict).assigned
    rw [analyze_eq_addClause, addClause_assigned]
  have id : result.2 = before.arena.size + 2 := by
    change (CDCL.analyze s conflict).2 = (analysisBeforeStore s conflict).arena.size + 2
    rw [analyze_eq_addClause, addClause_id]
  have database : Database before original learned := certificate.database.frame
    (analysisBeforeStore_arena _ _) (analysisBeforeStore_nVars _ _) (analysisBeforeStore_fixed _ _)
    (analysisBeforeStore_nLemmas _ _)
  have watches : WatchCertificate before (original ++ learned) heads := certificate.watches.frameArrays
    (analysisBeforeStore_arena _ _) (analysisBeforeStore_first _ _)
  change DecisionWatchHistory after
    (original ++ (learned ++ [⟨result.2, analysisLearned s conflict⟩])) (analysisHeads s conflict heads)
  intro older lower bound zero
  obtain ⟨retained, oldZero⟩ := asserted_old_decision entry root older bound zero
  have lower' : s.forced ≤ older := by
    have forced : result.1.forced = s.forced := analyze_forced s conflict
    change result.1.forced ≤ older at lower
    rw [forced] at lower
    exact lower
  have oldBound : older < s.assigned := Nat.lt_trans retained (analyze_assigned_lt entry.decisionEntry)
  have old := history older lower' oldBound oldZero
  have oldBefore : SettledWatches before (original ++ learned) heads older :=
    settledWatches_transfer old (fun i _ => congrArg (fun words : Array Lit => words[i]!) (analysisBeforeStore_trail s conflict))
  have equal : PrefixLiterals before after older := by
    intro i beforeDecision
    rw [assign_trail_prefix (Nat.lt_trans beforeDecision retained)]
    change (CDCL.analyze s conflict).1.trail[i]! = (analysisBeforeStore s conflict).trail[i]!
    rw [analyze_eq_addClause, addClause_trail]
  have first : 1 < (analysisLearned s conflict).size → FalseBefore after older (analysisLearned s conflict)[0]! →
      TrueBefore after older (analysisLearned s conflict)[1]! := by
    intro _ falseHead
    exact False.elim (asserted_not_false_head entry root older (Nat.le_of_lt retained) falseHead)
  have second : 1 < (analysisLearned s conflict).size → FalseBefore after older (analysisLearned s conflict)[1]! →
      TrueBefore after older (analysisLearned s conflict)[0]! := by
    intro many falseTail
    obtain ⟨tailIndex, afterDecision, kept, tail⟩ := analyze_highest_tail_after_decision entry.decisionEntry many
      older retained oldZero
    obtain ⟨i, beforeDecision, value⟩ := falseTail
    have beforeBirth : i < result.1.assigned := Nat.lt_trans beforeDecision retained
    have oldValue : s.trail[i]! = (analysisLearned s conflict)[1]! := by
      have original : after.trail[i]! = s.trail[i]! :=
        (assign_trail_prefix beforeBirth).trans (congrArg (fun words : Array Lit => words[i]!) (analyze_trail s conflict))
      exact original.symm.trans value
    have same := certificate.distinct i tailIndex
      (Nat.lt_trans beforeBirth (analyze_assigned_lt entry.decisionEntry))
      (Nat.lt_trans kept (analyze_assigned_lt entry.decisionEntry))
      (congrArg Lit.var (oldValue.trans tail.symm))
    exact False.elim (by omega)
  have settled := settled_allocate (lits := analysisLearned s conflict) database watches oldBefore equal
    (Nat.le_refl older) first second
  simpa only [SettledWatches, id, analysisHeads, List.append_assoc] using settled

end MicrosatLean.Verification.Implementation.Native.Search
