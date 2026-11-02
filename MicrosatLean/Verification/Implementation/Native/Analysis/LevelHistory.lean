import MicrosatLean.Verification.Implementation.Native.Analysis.LearnedHistory
import MicrosatLean.Verification.Implementation.Native.Propagation.Database
import MicrosatLean.Verification.Implementation.Native.Representation.ReasonDatabase

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation Std.Sat

theorem PrefixUnitClosed.unit_true {s : State} {decision : Nat} {lits : Array Lit}
    (closed : PrefixUnitClosed s decision lits) (unit : lits.size = 1) :
    TrueBefore s decision lits[0]! := by
  have nonempty : 0 < lits.size := by omega
  apply closed lits[0]!
  · simpa only [getElem!_pos lits 0 nonempty] using Array.getElem_mem nonempty
  · intro lit member different
    obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
    have first : i = 0 := by omega
    subst i
    exact False.elim (different (by simpa only [getElem!_pos lits 0 nonempty] using equal.symm))

theorem DecisionHistory.unit_true {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (decision : Nat) (lower : s.forced ≤ decision)
    (before : decision < s.assigned) (reason : s.reason s.trail[decision]! = 0)
    {entry : StoredClause} (member : entry ∈ entries) (unit : entry.lits.size = 1) :
    TrueBefore s decision entry.lits[0]! :=
  ((history decision lower before reason).closed entry member).unit_true unit

/-- Saved predecision closure forces every nondecision in this level to
depend on an earlier assignment in the same level. Otherwise its reason
would already have forced its head before this decision. -/
theorem DecisionHistory.reasonLevelParent {formula : CNF Nat} {s : State}
    {entries : List StoredClause} {rank : Lit → Nat} (history : DecisionHistory s entries)
    (graph : ReasonGraph formula s s.assigned rank) (proper : ReasonDatabase s entries)
    (stored : ∀ entry ∈ entries, PackedClause s entry.id entry.lits)
    (decision : Nat) (lower : s.forced ≤ decision) (before : decision < s.assigned)
    (reason : s.reason s.trail[decision]! = 0) : ReasonLevelParent s s.assigned decision := by
  classical
  intro i current bound nonzero lits packed
  obtain ⟨words, actual, nonempty, head, _, tails⟩ := graph.clauses i bound nonzero
  have same := actual.unique packed
  subst words
  obtain ⟨entry, member, id⟩ := proper i bound nonzero
  have entryPacked := stored entry member
  rw [← id] at entryPacked
  have sameEntry := packed.unique entryPacked
  have closed : PrefixUnitClosed s decision lits := by
    rw [sameEntry]
    exact (history decision lower before reason).closed entry member
  by_cases parent : ∃ j k, 0 < j ∧ j < lits.size ∧ decision ≤ k ∧ k < i ∧ s.trail[k]! = lits[j]!
  · exact parent
  · have headTrue : TrueBefore s decision lits[0]! := by
      apply closed lits[0]!
      · simpa only [getElem!_pos lits 0 nonempty] using Array.getElem_mem nonempty
      · intro lit member different
        obtain ⟨j, within, equal⟩ := Array.mem_iff_getElem.mp member
        have value : lits[j]! = lit := by simpa only [getElem!_pos lits j within] using equal
        have positive : 0 < j := by
          by_cases first : j = 0
          · subst j
            exact False.elim (different value.symm)
          · omega
        obtain ⟨k, earlier, tail⟩ := tails j positive within
        have old : k < decision := by
          by_cases inLevel : decision ≤ k
          · exact False.elim (parent ⟨j, k, positive, within, inLevel, earlier, tail⟩)
          · omega
        exact ⟨k, old, tail.trans value⟩
    obtain ⟨k, old, trueHead⟩ := headTrue
    have sameVariable : s.trail[k]!.var = s.trail[i]!.var := by
      rw [trueHead, head]
      simp only [negate_var]
    have equal := graph.distinctVariables k i (by omega) bound sameVariable
    omega

/-- An all-false genuine clause cannot have been wholly false before a
retained decision: its saved unit closure would provide a contradictory true
literal there. Thus a conflict contains a current-level false literal. -/
theorem DecisionHistory.conflict_in_level {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (active : ActiveTrail s)
    (decision : Nat) (lower : s.forced ≤ decision) (before : decision < s.assigned)
    (reason : s.reason s.trail[decision]! = 0) {entry : StoredClause}
    (member : entry ∈ entries) (nonempty : 0 < entry.lits.size)
    (covered : ∀ lit ∈ entry.lits, TrailMember s s.assigned lit) :
    ∃ i, decision ≤ i ∧ i < s.assigned ∧ s.trail[i]! ∈ entry.lits := by
  classical
  by_cases witness : ∃ i, decision ≤ i ∧ i < s.assigned ∧ s.trail[i]! ∈ entry.lits
  · exact witness
  · have old : ∀ lit ∈ entry.lits, FalseBefore s decision lit := by
      intro lit contains
      obtain ⟨i, bound, value⟩ := covered lit contains
      have earlier : i < decision := by
        by_cases current : decision ≤ i
        · exact False.elim (witness ⟨i, current, bound, value.symm ▸ contains⟩)
        · omega
      exact ⟨i, earlier, value⟩
    have firstMember : entry.lits[0]! ∈ entry.lits := by
      simpa only [getElem!_pos entry.lits 0 nonempty] using Array.getElem_mem nonempty
    have closed := (history decision lower before reason).closed entry member
    have truth := closed entry.lits[0]! firstMember (fun lit contains _ => old lit contains)
    exact False.elim (trueBefore_not_falseBefore active (Nat.le_of_lt before) truth (old _ firstMember))

/-- A concrete phase property: each nonroot assignment lies at or above an
actual decision boundary. Root propagation can instead use an empty interval
after advancing `forced`; no reason-parent fact is encoded here. -/
def LevelCover (s : State) : Prop :=
  ∀ i, s.forced ≤ i → i < s.assigned →
    ∃ decision, s.forced ≤ decision ∧ decision ≤ i ∧ s.reason s.trail[decision]! = 0

private theorem nearest_decision (s : State) (count : Nat)
    (witness : ∃ decision, s.forced ≤ decision ∧ decision < count ∧ s.reason s.trail[decision]! = 0) :
    ∃ decision, s.forced ≤ decision ∧ DecisionBlock s decision count := by
  induction count with
  | zero => obtain ⟨_, _, bound, _⟩ := witness; omega
  | succ count ih =>
    by_cases last : s.reason s.trail[count]! = 0
    · obtain ⟨_, lower, before, _⟩ := witness
      refine ⟨count, by omega, ⟨by omega, last, ?_⟩⟩
      intro later afterDecision beforeEnd
      omega
    · have prior : ∃ decision, s.forced ≤ decision ∧ decision < count ∧ s.reason s.trail[decision]! = 0 := by
        obtain ⟨decision, lower, before, zero⟩ := witness
        refine ⟨decision, lower, ?_, zero⟩
        by_cases equal : decision = count
        · exact False.elim (last (equal ▸ zero))
        · omega
      obtain ⟨decision, lower, block⟩ := ih prior
      refine ⟨decision, lower, ⟨Nat.lt_trans block.before (Nat.lt_succ_self _), block.decisionReason, ?_⟩⟩
      intro later afterDecision beforeEnd
      by_cases top : later = count
      · simpa only [top] using last
      · exact block.noLaterDecision later afterDecision (by omega)

theorem LevelCover.currentBlock {s : State} (cover : LevelCover s) (nonroot : s.forced < s.assigned) :
    ∃ decision, s.forced ≤ decision ∧ DecisionBlock s decision s.assigned := by
  obtain ⟨decision, lower, before, zero⟩ := cover s.forced (Nat.le_refl _) nonroot
  exact nearest_decision s s.assigned ⟨decision, lower, by omega, zero⟩

theorem LevelCover.root {s : State} (root : s.assigned ≤ s.forced) : LevelCover s := by
  intro i lower before
  omega

/-- Prefix truncation and reason relocation preserve level cover when they
preserve actual zero boundaries. Positive reason identifiers may change. -/
theorem LevelCover.truncate {before after : State} (cover : LevelCover before)
    (cursor : after.assigned ≤ before.assigned) (root : before.forced = after.forced)
    (decisions : ∀ i, i < after.assigned → before.reason before.trail[i]! = 0 →
      after.reason after.trail[i]! = 0) : LevelCover after := by
  intro i lower bound
  obtain ⟨decision, oldLower, beforeI, zero⟩ := cover i (by omega) (by omega)
  exact ⟨decision, by omega, beforeI, decisions decision (by omega) zero⟩

theorem LevelCover.decide {s : State} (cover : LevelCover s) (var : Nat)
    (root : s.forced ≤ s.assigned) (space : s.assigned < s.trail.size)
    (reasonBound : var < s.reasons.size) (fresh : FreshVariable s var) :
    LevelCover (s.decide var) := by
  intro i lower bound
  have limit : i < s.assigned + 1 := bound
  by_cases old : i < s.assigned
  · obtain ⟨decision, oldLower, beforeI, zero⟩ := cover i lower old
    refine ⟨decision, oldLower, beforeI, ?_⟩
    rw [decide_trail_prefix (by omega : decision < s.assigned), decide_reason_prefix fresh (by omega)]
    exact zero
  · have last : i = s.assigned := by omega
    refine ⟨s.assigned, root, by omega, ?_⟩
    rw [decide_trail_last space]
    simpa only [State.reason, negate_var, decisionLiteral_var] using decide_reason reasonBound

theorem LevelCover.assign {s : State} (cover : LevelCover s) (id : Nat) (root : Bool)
    (nonroot : s.forced < s.assigned) (fresh : FreshVariable s (Lit.var (s.db id))) :
    LevelCover (s.assign id root) := by
  intro i lower bound
  have limit : i < s.assigned + 1 := bound
  have oldIndex : ∃ j, s.forced ≤ j ∧ j < s.assigned ∧ j ≤ i := by
    by_cases old : i < s.assigned
    · exact ⟨i, lower, old, Nat.le_refl _⟩
    · exact ⟨s.forced, Nat.le_refl _, nonroot, by omega⟩
  obtain ⟨j, oldLower, oldBound, beforeI⟩ := oldIndex
  obtain ⟨decision, decisionLower, beforeJ, zero⟩ := cover j oldLower oldBound
  refine ⟨decision, decisionLower, Nat.le_trans beforeJ beforeI, ?_⟩
  rw [assign_trail_prefix (by omega : decision < s.assigned), assign_reason_prefix fresh (by omega)]
  exact zero

theorem LevelCover.analyze {formula : CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat} (cover : LevelCover s)
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    LevelCover (CDCL.analyze s conflict).1 := by
  let resolved := analysisResolved s conflict
  let built := buildLearned resolved resolved.assigned
  have facts := entry.historyResolved
  have upper : resolved.assigned < s.assigned := facts.uip.upper
  have frame := buildLearned_frame resolved resolved.assigned
  have ranked : ∀ i, i ≤ resolved.assigned → rank resolved.trail[i]! = i := by
    intro i bound
    rw [facts.trail]
    exact entry.graph.ranks i (by omega)
  have cursor := buildLearned_cursor resolved resolved.assigned rank
    (by rw [facts.forced]; exact Nat.le_trans entry.forcedBefore facts.uip.lower) ranked
  have bound : (analysisBeforeStore s conflict).assigned ≤ s.assigned := by
    simp only [analysisBeforeStore, backjump_assigned]
    exact Nat.le_trans cursor.2.1 (Nat.le_of_lt facts.uip.upper)
  have forced : (analysisBeforeStore s conflict).forced = s.forced := by
    simp only [analysisBeforeStore, backjump_forced]
    exact frame.forced.trans facts.forced
  have trail : (analysisBeforeStore s conflict).trail = s.trail := by
    simp only [analysisBeforeStore, backjump_trail]
    exact frame.trail.trans facts.trail
  have reasons : (analysisBeforeStore s conflict).reasons = s.reasons := by
    simp only [analysisBeforeStore, backjump_reasons]
    exact (congrArg State.reasons frame.restore).trans facts.storage.reasons
  rw [analyze_eq_addClause]
  apply cover.truncate (by rw [addClause_assigned]; exact bound) (by rw [addClause_forced, forced])
  intro i _ zero
  simpa only [State.reason, addClause_trail, addClause_reasons, trail, reasons] using zero

end MicrosatLean.Verification.Implementation.Native.Analysis
