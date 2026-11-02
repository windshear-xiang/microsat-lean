import MicrosatLean.Verification.Implementation.Native.Analysis.Tags
import MicrosatLean.Verification.Implementation.Native.Analysis.UIP
import MicrosatLean.Verification.Implementation.Native.Analysis.LevelModel
import MicrosatLean.Verification.Implementation.Native.Analysis.BackjumpClause
import MicrosatLean.Verification.Implementation.Native.Analysis.TagMonotonicity

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation
open Std.Sat

/-- The returned candidate is MARKed and is the sole MARK in its current
decision interval. This says nothing yet about recursive minimization. -/
structure UIPResult (snapshot : State) (count decision : Nat) (s : State) : Prop where
  lower : decision ≤ s.assigned
  upper : s.assigned < count
  marked : s.mark snapshot.trail[s.assigned]! = 2
  clear : ∀ i, decision ≤ i → i < s.assigned → s.mark snapshot.trail[i]! ≠ 2

private structure BlockGeometry (snapshot : State) (s : State) : Prop where
  storage : ReasonStorage snapshot s
  trail : s.trail = snapshot.trail
  vars : s.nVars = snapshot.nVars
  arrays : ArrayBounds s

private theorem BlockGeometry.transport {snapshot before after : State}
    (geometry : BlockGeometry snapshot before) (frame : ResolutionFrame before after) :
    BlockGeometry snapshot after :=
  ⟨frame.reasonStorage geometry.storage, frame.trail.trans geometry.trail,
    frame.nVars.trans geometry.vars, frame.arrayBounds geometry.arrays⟩

private theorem BlockGeometry.decisionBlock {snapshot s : State} {count decision candidate : Nat}
    (geometry : BlockGeometry snapshot s) (block : DecisionBlock snapshot decision count)
    (lower : decision < candidate) (upper : candidate < count) : DecisionBlock s decision candidate := by
  refine ⟨lower, ?_, ?_⟩
  · rw [geometry.trail, geometry.storage.reason]
    exact block.decisionReason
  · intro later after before
    rw [geometry.trail, geometry.storage.reason]
    exact block.noLaterDecision later after (Nat.lt_trans before upper)

private def BlockMark (snapshot : State) (count decision : Nat) (s : State) : Prop :=
  ∃ i, decision ≤ i ∧ i < count ∧ i < s.assigned ∧ s.mark snapshot.trail[i]! = 2

private def UIPStep (snapshot : State) (count decision before : Nat) (result : ForInStep State) : Prop :=
  match result with
  | .done next => UIPResult snapshot count decision next
  | .yield next => BlockGeometry snapshot next ∧ BlockMark snapshot count decision next ∧
      next.assigned + 1 = before

private theorem firstUIP_false_witness {s : State} {decision candidate : Nat}
    (block : DecisionBlock s decision candidate) (notUIP : firstUIP s candidate = false) :
    ∃ i, decision ≤ i ∧ i < candidate ∧ s.mark s.trail[i]! = 2 := by
  by_cases existsMark : ∃ i, decision ≤ i ∧ i < candidate ∧ s.mark s.trail[i]! = 2
  · exact existsMark
  · have clear : ∀ i, decision ≤ i → i < candidate → s.mark s.trail[i]! ≠ 2 := by
      intro i lower upper marked
      exact existsMark ⟨i, lower, upper, marked⟩
    have isUIP := (firstUIP_true_iff_decision_block_clear block).mpr clear
    rw [isUIP] at notUIP
    contradiction

private theorem resolutionBody_uip {formula : CNF Nat} {snapshot s : State} {count decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (block : DecisionBlock snapshot decision count) (geometry : BlockGeometry snapshot s)
    (witness : BlockMark snapshot count decision s) (bound : s.assigned ≤ count) :
    UIPStep snapshot count decision s.assigned (resolutionBody s) := by
  obtain ⟨k, lowerK, beforeK, activeK, markedK⟩ := witness
  let p := s.assigned - 1
  let popped := { s with assigned := p }
  let lit := s.trail[p]!
  have read : lit = snapshot.trail[p]! := by simp only [lit, geometry.trail]
  have cursor : p + 1 = s.assigned := by dsimp only [p]; omega
  have lower : decision ≤ p := by omega
  have upper : p < count := by omega
  have poppedGeometry := geometry.transport (resolutionFrame_setAssigned s p)
  have doneOfDecision (zero : popped.reason lit = 0) : UIPResult snapshot count decision popped := by
    have same : p = decision := by
      by_cases equal : p = decision
      · exact equal
      · have nonzero := block.noLaterDecision p (by omega) upper
        have zero' : snapshot.reason snapshot.trail[p]! = 0 := by
          rw [← geometry.storage.reason, ← read]
          exact zero
        exact False.elim (nonzero zero')
    refine ⟨lower, upper, ?_, ?_⟩
    · have equal : k = p := by omega
      simpa only [popped, State.mark, equal] using markedK
    · intro i after before
      change i < p at before
      omega
  simp only [resolutionBody, Id.run, pure]
  change UIPStep snapshot count decision s.assigned
    (if popped.reason lit == 0 then .done popped
    else if popped.mark lit == 2 then
      if firstUIP popped p then .done popped
      else .yield ((markClause popped (popped.reason lit + 1)).unassign lit)
    else .yield (popped.unassign lit))
  split
  · exact doneOfDecision (by simpa using ‹(popped.reason lit == 0) = true›)
  · have nondecision : popped.reason lit ≠ 0 := by simpa using ‹¬ (popped.reason lit == 0) = true›
    split
    · have marked : popped.mark lit = 2 := by simpa using ‹(popped.mark lit == 2) = true›
      split
      · have uip : firstUIP popped p = true := ‹firstUIP popped p = true›
        refine ⟨lower, upper, ?_, ?_⟩
        · simpa only [read] using marked
        · intro i after before
          change i < p at before
          by_cases atDecision : decision = p
          · omega
          · have currentBlock := poppedGeometry.decisionBlock block (by omega) upper
            have clear := (firstUIP_true_iff_decision_block_clear currentBlock).mp uip i after before
            simpa only [popped, State.mark, geometry.trail] using clear
      · have notUIP : firstUIP popped p = false := by simpa using ‹¬ firstUIP popped p = true›
        have strictlyAfter : decision < p := by
          by_cases equal : decision = p
          · have zero : popped.reason lit = 0 := by
              rw [read, ← equal, poppedGeometry.storage.reason]
              exact block.decisionReason
            exact False.elim (nondecision zero)
          · omega
        have currentBlock := poppedGeometry.decisionBlock block strictlyAfter upper
        obtain ⟨i, after, earlier, oldMarked⟩ := firstUIP_false_witness currentBlock notUIP
        have old : popped.mark snapshot.trail[i]! = 2 := by
          simpa only [popped, State.mark, geometry.trail] using oldMarked
        have member : TrailMember snapshot count snapshot.trail[p]! := ⟨p, upper, rfl⟩
        have nonzero : snapshot.reason snapshot.trail[p]! ≠ 0 := by
          rw [← poppedGeometry.storage.reason, ← read]
          exact nondecision
        obtain ⟨lits, packed, nonempty, _, _, _⟩ := graph.clause_of_member member nonzero
        have packedCurrent : PackedClause popped (popped.reason lit) lits := by
          rw [read, poppedGeometry.storage.reason]
          exact poppedGeometry.storage.packed poppedGeometry.vars packed
        have newlyMarked : (markClause popped (popped.reason lit + 1)).mark snapshot.trail[i]! = 2 :=
          (markClause_mark_two_iff packedCurrent poppedGeometry.arrays 1 (by omega) _).mpr (Or.inl old)
        have different : lit ≠ snapshot.trail[i]! := by
          intro equal
          have positions := congrArg rank (read.symm.trans equal)
          rw [graph.ranks p upper, graph.ranks i (by omega)] at positions
          omega
        refine ⟨(poppedGeometry.transport (resolutionFrame_markClause popped _)).transport
          (resolutionFrame_setMark _ lit 0), ?_, ?_⟩
        · refine ⟨i, after, by omega, ?_, ?_⟩
          · simpa only [State.unassign, State.setMark, markClause_assigned] using earlier
          · rw [unassign_mark_other different]
            exact newlyMarked
        · simpa only [State.unassign, State.setMark, markClause_assigned] using cursor
    · have notMarked : popped.mark lit ≠ 2 := by simpa using ‹¬ (popped.mark lit == 2) = true›
      have earlier : k < p := by
        by_cases equal : k = p
        · have marked : popped.mark lit = 2 := by rw [read, ← equal]; exact markedK
          exact False.elim (notMarked marked)
        · omega
      have different : lit ≠ snapshot.trail[k]! := by
        intro equal
        have positions := congrArg rank (read.symm.trans equal)
        rw [graph.ranks p upper, graph.ranks k beforeK] at positions
        omega
      refine ⟨poppedGeometry.transport (resolutionFrame_setMark popped lit 0), ?_, cursor⟩
      refine ⟨k, lowerK, beforeK, earlier, ?_⟩
      rw [unassign_mark_other different]
      exact markedK

private theorem resolutionScan_uip {formula : CNF Nat} {snapshot : State} {count decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (block : DecisionBlock snapshot decision count) (fuel : Nat) (s : State)
    (geometry : BlockGeometry snapshot s) (witness : BlockMark snapshot count decision s)
    (assigned : s.assigned = fuel) (bound : fuel ≤ count) :
    UIPResult snapshot count decision (resolutionScan fuel s) := by
  induction fuel generalizing s with
  | zero =>
    obtain ⟨_, _, _, active, _⟩ := witness
    omega
  | succ fuel ih =>
    have step := resolutionBody_uip graph block geometry witness (by omega)
    have cursor := resolutionBody_assigned s
    cases result : resolutionBody s with
    | done next => simpa only [resolutionScan, result, UIPStep] using step
    | yield next =>
      have after : BlockGeometry snapshot next ∧ BlockMark snapshot count decision next ∧
          next.assigned + 1 = s.assigned := by simpa only [result, UIPStep] using step
      simpa only [resolutionScan, result] using ih next after.1 after.2.1 (by omega) (by omega)

/-- A real conflict with a MARK in its current nearest-decision interval
reaches a MARKed first UIP. The actual early exits and finite loop budget are
refined; exhaustion cannot occur while the interval retains a MARK. -/
theorem resolveToUIP_marked_uip {formula : CNF Nat} {snapshot : State} {count decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (block : DecisionBlock snapshot decision count) (s : State)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (vars : s.nVars = snapshot.nVars) (arrays : ArrayBounds s) (assigned : s.assigned = count)
    (marked : ∃ i, decision ≤ i ∧ i < count ∧ s.mark snapshot.trail[i]! = 2) :
    UIPResult snapshot count decision (resolveToUIP s) := by
  have witness : BlockMark snapshot count decision s := by
    obtain ⟨i, lower, before, mark⟩ := marked
    exact ⟨i, lower, before, by simpa only [assigned] using before, mark⟩
  rw [resolveToUIP_eq_scan]
  exact resolutionScan_uip graph block s.assigned s ⟨storage, trail, vars, arrays⟩ witness rfl
    (Nat.le_of_eq assigned)

/-- The actual first minimizer call fails on the sole current-level UIP, so
the actual learned array is nonempty and starts with that UIP. The proof uses
the concrete level countermodel and the executable reset of `processed`. -/
theorem buildLearned_retains_uip {formula : CNF Nat} {snapshot s : State} {count decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (parents : ReasonLevelParent snapshot count decision) (tags : ValidMarkTags snapshot count s)
    (uip : UIPResult snapshot count decision s) (forcedBefore : s.forced ≤ decision)
    (rootEarlier : ∀ i, i < count → s.mark snapshot.trail[i]! = 6 → i < decision) :
    0 < (buildLearned s s.assigned).2.1.size ∧
      (buildLearned s s.assigned).2.1[0]! = s.trail[s.assigned]! := by
  let reset := { s with processed := s.assigned }
  have resetStorage : ReasonStorage snapshot reset := ⟨storage.arena, storage.reasons⟩
  have failed := implied_false_of_level_parent graph resetStorage parents (s := reset) tags
    uip.lower uip.upper uip.clear rootEarlier (s.nVars + 1)
  have read : s.trail[s.assigned]! = snapshot.trail[s.assigned]! :=
    congrArg (fun words : Array Lit => words[s.assigned]!) trail
  apply buildLearned_head_of_implied_false s s.assigned (Nat.le_trans forcedBefore uip.lower)
  · rw [read]
    exact uip.marked
  · rw [read]
    exact failed

/-- Resolution followed by recursive minimization retains the actual first
UIP under concrete same-level reason-parent and preexisting-root-tag facts.
The nonempty clause and retained head are conclusions, not entry premises. -/
theorem resolveToUIP_retains_uip {formula : CNF Nat} {snapshot : State} {count decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (block : DecisionBlock snapshot decision count) (parents : ReasonLevelParent snapshot count decision)
    (s : State) (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (vars : s.nVars = snapshot.nVars) (arrays : ArrayBounds s) (assigned : s.assigned = count)
    (marked : ∃ i, decision ≤ i ∧ i < count ∧ s.mark snapshot.trail[i]! = 2)
    (tags : ValidMarkTags snapshot count s) (forcedBefore : s.forced ≤ decision)
    (rootEarlier : ∀ i, i < count → s.mark snapshot.trail[i]! = 6 → i < decision) :
    let resolved := resolveToUIP s
    UIPResult snapshot count decision resolved ∧
      0 < (buildLearned resolved resolved.assigned).2.1.size ∧
      (buildLearned resolved resolved.assigned).2.1[0]! = snapshot.trail[resolved.assigned]! := by
  have uip := resolveToUIP_marked_uip graph block s storage trail vars arrays assigned marked
  have boundary : RootTagBoundary snapshot count 0 s := by intro i impossible; omega
  have resolvedTags := resolveToUIP_tags graph s storage trail vars arrays tags boundary (Nat.le_of_eq assigned)
  have frame := resolveToUIP_frame s
  have forced : (resolveToUIP s).forced = s.forced := by simpa only using congrArg State.forced frame.restore
  have earlier : ∀ i, i < count → (resolveToUIP s).mark snapshot.trail[i]! = 6 → i < decision := by
    intro i before six
    exact rootEarlier i before (resolveToUIP_no_new_six s _ six)
  have retained := buildLearned_retains_uip graph (frame.reasonStorage storage) (frame.trail.trans trail)
    parents resolvedTags.1 uip (by rw [forced]; exact forcedBefore) earlier
  refine ⟨uip, retained.1, ?_⟩
  exact retained.2.trans (congrArg (fun words : Array Lit => words[(resolveToUIP s).assigned]!)
    (frame.trail.trans trail))

end MicrosatLean.Verification.Implementation.Native.Analysis
