import MicrosatLean.Verification.Implementation.Analysis.Asserting
import MicrosatLean.Verification.Implementation.Analysis.Soundness

namespace MicrosatLean.Verification.Implementation.Analysis

open CDCL Representation
open Std.Sat

def FalseBefore (s : State) (decision : Nat) (lit : Lit) : Prop :=
  ∃ i, i < decision ∧ s.trail[i]! = lit

def TrueBefore (s : State) (decision : Nat) (lit : Lit) : Prop :=
  FalseBefore s decision lit.negate

/-- Conflict-free unit-propagation closure of a clause at the prefix just
before the retained decision. This is a concrete clause/trail property. -/
def PrefixUnitClosed (s : State) (decision : Nat) (lits : Array Lit) : Prop :=
  ∀ head ∈ lits, (∀ tail ∈ lits, tail ≠ head → FalseBefore s decision tail) →
    TrueBefore s decision head

/-- A usable consequence of clause birth history: unit closure at the retained
predecision prefix, or a surviving true asserting head assigned since that
decision. Earlier clauses obtain the first witness from quiescence; later
clauses need a maintained witness, which may migrate to prefix closure after
backjump. Reachability must establish this invariant independently. -/
inductive ClauseOrigin (s : State) (decision : Nat) (entry : StoredClause) : Prop
  | beforeDecision (closed : PrefixUnitClosed s decision entry.lits)
  | sinceDecision (head : Lit) (member : head ∈ entry.lits) (position : Nat)
      (after : decision ≤ position) (active : position < s.assigned)
      (asserted : s.trail[position]! = head.negate)

structure DecisionLearned (s : State) (decision : Nat) (lits : Array Lit) : Prop where
  nonempty : 0 < lits.size
  head : ∃ i, decision ≤ i ∧ i < s.assigned ∧ lits[0]! = s.trail[i]!
  tails : ∀ j, 0 < j → j < lits.size → FalseBefore s decision lits[j]!
  falseLiterals : ∀ lit ∈ lits, FalseAssignment s lit
  bounded : ∀ lit ∈ lits, LiteralBound s.nVars lit

def SameLiterals (left right : Array Lit) : Prop := ∀ lit, lit ∈ left ↔ lit ∈ right

theorem DecisionLearned.fresh_of_origin {s : State} {decision : Nat} {lits : Array Lit}
    {entry : StoredClause} (shape : DecisionLearned s decision lits)
    (active : ActiveTrail s) (distinct : DistinctTrailVariables s)
    (origin : ClauseOrigin s decision entry) : ¬ SameLiterals lits entry.lits := by
  intro same
  cases origin with
  | beforeDecision closed =>
    have headMember : lits[0]! ∈ lits := by
      simpa only [getElem!_pos lits 0 shape.nonempty] using Array.getElem_mem shape.nonempty
    have trueHead := closed lits[0]! ((same _).mp headMember) (by
      intro tail member different
      obtain ⟨j, before, equal⟩ := Array.mem_iff_getElem.mp ((same tail).mpr member)
      have equal' : lits[j]! = tail := by simpa only [getElem!_pos lits j before] using equal
      by_cases first : j = 0
      · subst j
        exact False.elim (different equal'.symm)
      · simpa only [equal'] using shape.tails j (by omega) before)
    obtain ⟨root, earlier, trueHead⟩ := trueHead
    obtain ⟨position, current, before, head⟩ := shape.head
    have sameVar : s.trail[root]!.var = s.trail[position]!.var := by
      simp only [trueHead, negate_var, head]
    have equal := distinct root position (by omega) before sameVar
    omega
  | sinceDecision head member position after before asserted =>
    have falseHead := shape.falseLiterals head ((same head).mpr member)
    have trueHead := (active position before).2.1
    rw [asserted] at trueHead
    exact trueHead falseHead.2

theorem buildLearned_decision_shape {formula : Std.Sat.CNF Nat} {snapshot s : State} {decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot snapshot.assigned rank)
    (active : ActiveTrail snapshot) (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (parents : ReasonLevelParent snapshot snapshot.assigned decision) (tags : ValidMarkTags snapshot snapshot.assigned s)
    (uip : UIPResult snapshot snapshot.assigned decision s) (forcedBefore : s.forced ≤ decision)
    (rootEarlier : ∀ i, i < snapshot.assigned → s.mark snapshot.trail[i]! = 6 → i < decision) :
    DecisionLearned snapshot decision (buildLearned s s.assigned).2.1 := by
  have retained := buildLearned_retains_uip graph storage trail parents tags uip forcedBefore rootEarlier
  have lower : s.forced ≤ s.assigned := Nat.le_trans forcedBefore uip.lower
  have ranked : ∀ i, i ≤ s.assigned → rank s.trail[i]! = i := by
    intro i before
    rw [trail]
    exact graph.ranks i (Nat.lt_of_le_of_lt before uip.upper)
  have cursor := buildLearned_cursor s s.assigned rank lower ranked
  have headRank : rank (buildLearned s s.assigned).2.1[0]! = s.assigned := by
    rw [retained.2]
    exact ranked s.assigned (Nat.le_refl _)
  have position : ∀ j, j < (buildLearned s s.assigned).2.1.size →
      rank (buildLearned s s.assigned).2.1[j]! < snapshot.assigned ∧
        snapshot.trail[rank (buildLearned s s.assigned).2.1[j]!]! = (buildLearned s s.assigned).2.1[j]! := by
    intro j before
    have old := cursor.2.2.1 j before
    exact ⟨Nat.lt_of_le_of_lt old.2.1 uip.upper, by simpa only [trail] using old.2.2⟩
  refine ⟨retained.1, ⟨s.assigned, uip.lower, uip.upper, ?_⟩, ?_, ?_, ?_⟩
  · exact retained.2.trans (congrArg (fun words : Array Lit => words[s.assigned]!) trail)
  · intro j positive before
    have pos := position j before
    have earlier := cursor.2.2.2.2.1 0 j positive before
    rw [headRank] at earlier
    have below : rank (buildLearned s s.assigned).2.1[j]! < decision := by
      by_cases current : decision ≤ rank (buildLearned s s.assigned).2.1[j]!
      · have clear := uip.clear _ current earlier
        have original := buildLearned_original_marks s s.assigned (buildLearned s s.assigned).2.1[j]!
          (by simpa only [getElem!_pos (buildLearned s s.assigned).2.1 j before] using Array.getElem_mem before)
        exact False.elim (clear (by simpa only [pos.2] using original))
      · omega
    exact ⟨_, below, pos.2⟩
  · intro lit member
    obtain ⟨j, before, equal⟩ := Array.mem_iff_getElem.mp member
    have equal' : (buildLearned s s.assigned).2.1[j]! = lit := by
      simpa only [getElem!_pos (buildLearned s s.assigned).2.1 j before] using equal
    have pos := position j before
    have equalLit := pos.2.trans equal'
    simpa only [equalLit] using (active _ pos.1).2
  · intro lit member
    obtain ⟨j, before, equal⟩ := Array.mem_iff_getElem.mp member
    have equal' : (buildLearned s s.assigned).2.1[j]! = lit := by
      simpa only [getElem!_pos (buildLearned s s.assigned).2.1 j before] using equal
    have pos := position j before
    have equalLit := pos.2.trans equal'
    simpa only [equalLit] using (active _ pos.1).1

/-- Conflict-analysis entry with a concrete current decision interval. The
conflict contains an actual false literal from that interval, and the
same-level parent and root-tag facts are incoming reachability invariants. -/
structure DecisionAnalysisEntry (formula : Std.Sat.CNF Nat) (s : State) (conflict : Nat)
    (conflictLits : Array Lit) (rank : Lit → Nat) (decision : Nat) : Prop
    extends AnalysisEntry formula s conflict conflictLits rank where
  block : DecisionBlock s decision s.assigned
  parents : ReasonLevelParent s s.assigned decision
  forcedBefore : s.forced ≤ decision
  rootEarlier : ∀ i, i < s.assigned → s.mark s.trail[i]! = 6 → i < decision
  conflictInBlock : ∃ i, decision ≤ i ∧ i < s.assigned ∧ s.trail[i]! ∈ conflictLits

theorem DecisionAnalysisEntry.learned_shape {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {conflictLits : Array Lit} {rank : Lit → Nat}
    (entry : DecisionAnalysisEntry formula s conflict conflictLits rank decision) :
    DecisionLearned s decision (analysisLearned s conflict) := by
  let marked := markClause (analysisStart s) conflict
  let resolved := resolveToUIP marked
  have startArrays : ArrayBounds (analysisStart s) :=
    ⟨entry.arrays.firstSize, entry.arrays.marksSize, entry.arrays.reasonsSize, entry.arrays.phasesSize,
      entry.arrays.trailSize, entry.arrays.previousSize, entry.arrays.nextSize⟩
  have packed : PackedClause (analysisStart s) conflict conflictLits := entry.packed.frame rfl rfl
  have markFrame := resolutionFrame_markClause (analysisStart s) conflict
  have storage : ReasonStorage s marked := markFrame.reasonStorage ⟨rfl, rfl⟩
  have trail : marked.trail = s.trail := markFrame.trail
  have vars : marked.nVars = s.nVars := markFrame.nVars
  have arrays : ArrayBounds marked := markFrame.arrayBounds startArrays
  have assigned : marked.assigned = s.assigned := markClause_assigned (analysisStart s) conflict
  have tags : ValidMarkTags s s.assigned marked := by
    simpa only [Nat.add_zero] using markClause_validTags (s := analysisStart s) entry.tags
      packed startArrays 0 (Nat.zero_le _)
  have earlier : ∀ i, i < s.assigned → marked.mark s.trail[i]! = 6 → i < decision := by
    intro i before six
    exact entry.rootEarlier i before (markClause_sixSubset (analysisStart s) conflict _ six)
  have witness : ∃ i, decision ≤ i ∧ i < s.assigned ∧ marked.mark s.trail[i]! = 2 := by
    obtain ⟨i, lower, before, member⟩ := entry.conflictInBlock
    refine ⟨i, lower, before, ?_⟩
    have nonroot : (analysisStart s).mark s.trail[i]! ≠ 6 := by
      intro six
      have below := entry.rootEarlier i before six
      omega
    simpa only [Nat.add_zero] using markClause_mark_member packed startArrays 0 (Nat.zero_le _)
      (by simpa using member) nonroot
  have uip := resolveToUIP_marked_uip entry.graph entry.block marked storage trail vars arrays assigned witness
  have boundary : RootTagBoundary s s.assigned 0 marked := by intro i impossible; omega
  have resolvedTags := resolveToUIP_tags entry.graph marked storage trail vars arrays tags boundary
    (Nat.le_of_eq assigned)
  have frame := resolveToUIP_frame marked
  have forced : resolved.forced ≤ decision := by
    have same : resolved.forced = marked.forced := by simpa only using congrArg State.forced frame.restore
    rw [same]
    change (markClause (analysisStart s) conflict).forced ≤ decision
    rw [markClause_forced]
    exact entry.forcedBefore
  have rootEarlier : ∀ i, i < s.assigned → resolved.mark s.trail[i]! = 6 → i < decision := by
    intro i before six
    exact earlier i before (resolveToUIP_no_new_six marked _ six)
  exact buildLearned_decision_shape entry.graph entry.active (frame.reasonStorage storage)
    (frame.trail.trans trail) entry.parents resolvedTags.1 uip forced rootEarlier

def viewedLiterals (lits : Array Lit) : Logic.ClauseSpace.Literals := lits.toList.map literalView

def canonicalKey (n : Nat) (lits : Array Lit) : Logic.ClauseSpace.Literals :=
  Logic.ClauseSpace.canonicalize n (viewedLiterals lits)

@[simp] theorem viewedLiterals_mem {lit : Lit} {lits : Array Lit} :
    literalView lit ∈ viewedLiterals lits ↔ lit ∈ lits := by
  constructor
  · intro member
    obtain ⟨encoded, original, equal⟩ := List.mem_map.mp member
    have same := literalView_injective equal
    simpa [same] using original
  · intro member
    exact List.mem_map.mpr ⟨lit, by simpa using member, rfl⟩

theorem viewedLiterals_bounded {n : Nat} {lits : Array Lit}
    (bounded : ∀ lit ∈ lits, LiteralBound n lit) : Logic.ClauseSpace.Bounded n (viewedLiterals lits) := by
  intro viewed member
  obtain ⟨lit, original, rfl⟩ := List.mem_map.mp member
  exact bounded lit (by simpa using original)

theorem DecisionLearned.noClash {s : State} {decision : Nat} {lits : Array Lit}
    (shape : DecisionLearned s decision lits) : Logic.ClauseSpace.NoClash (viewedLiterals lits) := by
  intro var positive negative
  obtain ⟨pos, posMember, posView⟩ := List.mem_map.mp positive
  obtain ⟨neg, negMember, negView⟩ := List.mem_map.mp negative
  have complement : pos.negate = neg := by
    apply literalView_injective
    rw [literalView_negate, posView, negView]
    rfl
  have falsePos := shape.falseLiterals pos (by simpa using posMember)
  have falseNeg := shape.falseLiterals neg (by simpa using negMember)
  exact falseNeg.1 (complement ▸ falsePos.2)

theorem DecisionLearned.canonical_fresh {s : State} {decision : Nat} {lits : Array Lit}
    {entry : StoredClause} (shape : DecisionLearned s decision lits)
    (active : ActiveTrail s) (distinct : DistinctTrailVariables s) (origin : ClauseOrigin s decision entry)
    (bounded : ∀ lit ∈ entry.lits, LiteralBound s.nVars lit)
    (normalized : Logic.ClauseSpace.NoClash (viewedLiterals entry.lits)) :
    canonicalKey s.nVars lits ≠ canonicalKey s.nVars entry.lits := by
  intro equal
  have members := (Logic.ClauseSpace.canonicalize_eq_iff
    (viewedLiterals_bounded shape.bounded) shape.noClash (viewedLiterals_bounded bounded) normalized).mp equal
  apply shape.fresh_of_origin active distinct origin
  intro lit
  simpa only [viewedLiterals_mem] using members (literalView lit)

/-- Canonical freshness follows from actual clause origins, predecision unit
closure and surviving asserting heads. It is not an incoming no-duplicate
assumption. Bounded, nontautological old clauses make canonical equality exact. -/
theorem analyze_canonical_fresh {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {conflictLits : Array Lit} {rank : Lit → Nat} {original learned : List StoredClause}
    (entry : DecisionAnalysisEntry formula s conflict conflictLits rank decision)
    (database : Database s original learned)
    (origins : ∀ old ∈ original ++ learned, ClauseOrigin s decision old)
    (normalized : ∀ old ∈ original ++ learned, Logic.ClauseSpace.NoClash (viewedLiterals old.lits)) :
    ∀ old ∈ original ++ learned,
      canonicalKey s.nVars (analysisLearned s conflict) ≠ canonicalKey s.nVars old.lits := by
  intro old member
  exact entry.learned_shape.canonical_fresh entry.active entry.graph.distinctVariables (origins old member)
    (database.layout.packed member).wellFormed (normalized old member)

theorem analyze_canonical_distinct {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {conflictLits : Array Lit} {rank : Lit → Nat} {original learned : List StoredClause}
    (entry : DecisionAnalysisEntry formula s conflict conflictLits rank decision)
    (database : Database s original learned)
    (origins : ∀ old ∈ original ++ learned, ClauseOrigin s decision old)
    (normalized : ∀ old ∈ original ++ learned, Logic.ClauseSpace.NoClash (viewedLiterals old.lits))
    (distinct : (learned.map fun old => canonicalKey s.nVars old.lits).Nodup) :
    let added : StoredClause := ⟨(analyze s conflict).2, analysisLearned s conflict⟩
    ((learned ++ [added]).map fun old => canonicalKey s.nVars old.lits).Nodup := by
  have fresh := analyze_canonical_fresh entry database origins normalized
  simp only [List.map_append, List.map_cons, List.map_nil]
  apply List.nodup_append.mpr
  refine ⟨distinct, by simp, ?_⟩
  intro key member other singleton collision
  have otherKey : other = canonicalKey s.nVars (analysisLearned s conflict) := by simpa using singleton
  obtain ⟨old, oldMember, oldKey⟩ := List.mem_map.mp member
  apply fresh old (List.mem_append_right original oldMember)
  exact (oldKey.trans (collision.trans otherKey)).symm

end MicrosatLean.Verification.Implementation.Analysis
