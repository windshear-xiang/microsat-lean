import MicrosatLean.Verification.Implementation.Native.Analysis.ReasonGraph
import MicrosatLean.Verification.Implementation.Native.Representation.Capacity
import MicrosatLean.Verification.Implementation.Native.Representation.DatabaseUpdates

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation Std.Sat

/-- Assign the new variable its appended position; existing active variables
retain their original ranks. Values outside the active snapshot are immaterial. -/
def extendTrailRank (rank : Lit → Nat) (var position : Nat) (lit : Lit) : Nat :=
  if lit.var = var then position else rank lit

theorem extendTrailRank_prefix {s : State} {rank : Lit → Nat} {var i : Nat}
    (fresh : FreshVariable s var) (before : i < s.assigned) :
    extendTrailRank rank var s.assigned s.trail[i]! = rank s.trail[i]! := by
  exact ite_eq_right (fresh i before)

private theorem polarities_of_same_variable {left right : Lit} (same : left.var = right.var) :
    left = right ∨ left = right.negate := by
  have different := negate_ne right
  have leftEncoding := literal_encoding left
  have rightEncoding := literal_encoding right
  have negativeEncoding := literal_encoding right.negate
  rw [same] at leftEncoding
  rw [negate_var] at negativeEncoding
  rcases leftEncoding with positive | negative
  · rcases rightEncoding with positive' | negative'
    · exact Or.inl (positive.trans positive'.symm)
    · right
      rcases negativeEncoding with positive'' | negative''
      · exact positive.trans positive''.symm
      · exact False.elim (different (negative''.trans negative'.symm))
  · rcases rightEncoding with positive' | negative'
    · right
      rcases negativeEncoding with positive'' | negative''
      · exact False.elim (different (positive''.trans positive'.symm))
      · exact negative.trans negative''.symm
    · exact Or.inl (negative.trans negative'.symm)

theorem freshVariable_of_unmarked_literal {s : State} {lit : Lit} (active : ActiveTrail s)
    (head : s.mark lit = 0) (opposite : s.mark lit.negate = 0) :
    FreshVariable s lit.var := by
  intro i before same
  have marked := (active i before).2.1
  rcases polarities_of_same_variable same with equal | equal
  · exact marked ((congrArg s.mark equal).trans head)
  · exact marked ((congrArg s.mark equal).trans opposite)

/-- Updating the fresh variable's reason cannot overwrite any active reason. -/
theorem assign_reason_prefix {s : State} {id i : Nat} {root : Bool}
    (fresh : FreshVariable s (Lit.var (s.db id))) (before : i < s.assigned) :
    (s.assign id root).reason s.trail[i]! = s.reason s.trail[i]! :=
  Array.getElem!_set!_ne s.reasons _ _ _ (Ne.symm (fresh i before))

theorem decide_reason_prefix {s : State} {var i : Nat}
    (fresh : FreshVariable s var) (before : i < s.assigned) :
    (s.decide var).reason s.trail[i]! = s.reason s.trail[i]! :=
  Array.getElem!_set!_ne s.reasons _ _ _ (Ne.symm (fresh i before))

/-- Actual propagation appends a fresh reason node whose non-head literals
already occur on the active trail. Capacity follows from the old graph's
distinct variables; it is not assumed for the output write. -/
theorem ReasonGraph.assign_of_fresh {formula : Std.Sat.CNF Nat} {s : State} {rank : Lit → Nat}
    (graph : ReasonGraph formula s s.assigned rank) (arrays : ArrayBounds s)
    (active : ActiveTrail s) {id : Nat} {lits : Array Lit}
    (packed : PackedClause s id lits) (nonempty : 0 < lits.size)
    (entailed : CNF.EntailsClause formula (clauseView lits))
    (tails : ∀ j, 0 < j → j < lits.size → TrailMember s s.assigned lits[j]!)
    (fresh : FreshVariable s (Lit.var (s.db id))) (root : Bool) :
    ReasonGraph formula (s.assign id root) (s.assign id root).assigned
      (extendTrailRank rank (Lit.var (s.db id)) s.assigned) := by
  have head : s.db id = lits[0]! := by simpa using packed.literals 0 nonempty
  have headMember : s.db id ∈ lits := by
    rw [head, getElem!_pos lits 0 nonempty]
    exact Array.getElem_mem nonempty
  have literal := packed.wellFormed _ headMember
  have distinct : DistinctTrailVariables s := graph.distinctVariables
  have room := assigned_lt_of_fresh active distinct fresh literal.1 literal.2
  have space : s.assigned < s.trail.size := by rw [arrays.trailSize]; omega
  constructor
  · change s.assigned + 1 ≤ (s.trail.set! s.assigned _).size
    simp only [Array.size_set!]
    omega
  · intro i before
    have bound : i < s.assigned + 1 := before
    by_cases last : i = s.assigned
    · subst i
      rw [assign_trail_last space]
      simp [extendTrailRank]
    · have earlier : i < s.assigned := by omega
      rw [assign_trail_prefix earlier, extendTrailRank_prefix fresh earlier]
      exact graph.ranks i earlier
  · exact distinct.assign fresh space
  · intro i before nondecision
    have bound : i < s.assigned + 1 := before
    by_cases last : i = s.assigned
    · subst i
      rw [assign_trail_last space]
      have reason : (s.assign id root).reason (Lit.negate (s.db id)) = id := by
        simpa only [State.reason, negate_var] using
          (assign_reason (root := root) (arrays.variable_index literal.2).1)
      rw [reason]
      refine ⟨lits, packed.frame rfl rfl, nonempty, ?_, entailed, ?_⟩
      · simpa only [negate_negate] using head.symm
      · intro j positive within
        obtain ⟨k, beforeK, equal⟩ := tails j positive within
        exact ⟨k, beforeK, (assign_trail_prefix beforeK).trans equal⟩
    · have earlier : i < s.assigned := by omega
      rw [assign_trail_prefix earlier, assign_reason_prefix fresh earlier] at nondecision ⊢
      obtain ⟨oldLits, oldPacked, oldNonempty, oldHead, oldEntailed, oldTails⟩ :=
        graph.clauses i earlier nondecision
      refine ⟨oldLits, oldPacked.frame rfl rfl, oldNonempty, oldHead, oldEntailed, ?_⟩
      intro j positive within
      obtain ⟨k, beforeK, equal⟩ := oldTails j positive within
      exact ⟨k, beforeK, (assign_trail_prefix (Nat.lt_trans beforeK earlier)).trans equal⟩

/-- The actual unassigned mark test supplies the fresh node required above. -/
theorem ReasonGraph.assign {formula : Std.Sat.CNF Nat} {s : State} {rank : Lit → Nat}
    (graph : ReasonGraph formula s s.assigned rank) (arrays : ArrayBounds s)
    (active : ActiveTrail s) {id : Nat} {lits : Array Lit}
    (packed : PackedClause s id lits) (nonempty : 0 < lits.size)
    (entailed : CNF.EntailsClause formula (clauseView lits))
    (tails : ∀ j, 0 < j → j < lits.size → TrailMember s s.assigned lits[j]!)
    (head : s.mark (s.db id) = 0) (opposite : s.mark (Lit.negate (s.db id)) = 0)
    (root : Bool) :
    ReasonGraph formula (s.assign id root) (s.assign id root).assigned
      (extendTrailRank rank (Lit.var (s.db id)) s.assigned) :=
  graph.assign_of_fresh arrays active packed nonempty entailed tails
    (freshVariable_of_unmarked_literal active head opposite) root

/-- A decision appends a rank but has reason zero; all older graph edges and
their concrete packed clauses are retained by the real array updates. -/
theorem ReasonGraph.decide_of_fresh {formula : Std.Sat.CNF Nat} {s : State} {rank : Lit → Nat}
    (graph : ReasonGraph formula s s.assigned rank) (arrays : ArrayBounds s)
    (active : ActiveTrail s) {var : Nat} (lower : 1 ≤ var) (upper : var ≤ s.nVars)
    (fresh : FreshVariable s var) :
    ReasonGraph formula (s.decide var) (s.decide var).assigned
      (extendTrailRank rank var s.assigned) := by
  have distinct : DistinctTrailVariables s := graph.distinctVariables
  have room := assigned_lt_of_fresh active distinct fresh lower upper
  have space : s.assigned < s.trail.size := by rw [arrays.trailSize]; omega
  constructor
  · change s.assigned + 1 ≤ (s.trail.set! s.assigned _).size
    simp only [Array.size_set!]
    omega
  · intro i before
    have bound : i < s.assigned + 1 := before
    by_cases last : i = s.assigned
    · subst i
      rw [decide_trail_last space]
      simp [extendTrailRank]
    · have earlier : i < s.assigned := by omega
      rw [decide_trail_prefix earlier, extendTrailRank_prefix fresh earlier]
      exact graph.ranks i earlier
  · exact distinct.decide fresh space
  · intro i before nondecision
    have bound : i < s.assigned + 1 := before
    by_cases last : i = s.assigned
    · subst i
      rw [decide_trail_last space] at nondecision
      have reason : (s.decide var).reason (decisionLiteral s var).negate = 0 := by
        simpa only [State.reason, negate_var, decisionLiteral_var] using
          (decide_reason (arrays.variable_index upper).1)
      exact False.elim (nondecision reason)
    · have earlier : i < s.assigned := by omega
      rw [decide_trail_prefix earlier, decide_reason_prefix fresh earlier] at nondecision ⊢
      obtain ⟨oldLits, oldPacked, oldNonempty, oldHead, oldEntailed, oldTails⟩ :=
        graph.clauses i earlier nondecision
      refine ⟨oldLits, oldPacked.frame rfl rfl, oldNonempty, oldHead, oldEntailed, ?_⟩
      intro j positive within
      obtain ⟨k, beforeK, equal⟩ := oldTails j positive within
      exact ⟨k, beforeK, (decide_trail_prefix (Nat.lt_trans beforeK earlier)).trans equal⟩

theorem ReasonGraph.decide {formula : Std.Sat.CNF Nat} {s : State} {rank : Lit → Nat}
    (graph : ReasonGraph formula s s.assigned rank) (arrays : ArrayBounds s)
    (active : ActiveTrail s) {var : Nat} (lower : 1 ≤ var) (upper : var ≤ s.nVars)
    (positive : s.mark (2 * var) = 0) (negative : s.mark (2 * var + 1) = 0) :
    ReasonGraph formula (s.decide var) (s.decide var).assigned
      (extendTrailRank rank var s.assigned) :=
  graph.decide_of_fresh arrays active lower upper
    (freshVariable_of_unmarked active positive negative)

/-- A reason graph restricts to any earlier trail prefix because every edge
already points to a strictly smaller index. -/
theorem ReasonGraph.prefix {formula : Std.Sat.CNF Nat} {s : State} {count keep : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula s count rank) (bound : keep ≤ count) :
    ReasonGraph formula s keep rank :=
  ⟨Nat.le_trans bound graph.countBound,
    fun i before => graph.ranks i (Nat.lt_of_lt_of_le before bound),
    fun i j beforeI beforeJ => graph.distinctVariables i j
      (Nat.lt_of_lt_of_le beforeI bound) (Nat.lt_of_lt_of_le beforeJ bound),
    fun i before => graph.clauses i (Nat.lt_of_lt_of_le before bound)⟩

theorem ReasonGraph.frame {formula : Std.Sat.CNF Nat} {before after : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula before count rank)
    (arena : after.arena = before.arena) (reasons : after.reasons = before.reasons)
    (trail : after.trail = before.trail) (variables : after.nVars = before.nVars) :
    ReasonGraph formula after count rank := by
  constructor
  · simpa only [trail] using graph.countBound
  · simpa only [trail] using graph.ranks
  · simpa only [trail] using graph.distinctVariables
  · intro i bound nondecision
    have reason : after.reason after.trail[i]! = before.reason before.trail[i]! := by
      simp only [State.reason, trail, reasons]
    rw [reason] at nondecision ⊢
    obtain ⟨lits, packed, nonempty, head, entailed, tails⟩ := graph.clauses i bound nondecision
    exact ⟨lits, packed.frame arena variables, nonempty, by simpa only [trail] using head,
      entailed, by simpa only [trail] using tails⟩

/-- Actual restart retains the forced prefix and leaves all its reason data
unchanged. Restricting the DAG therefore preserves every surviving edge. -/
theorem ReasonGraph.restart {formula : Std.Sat.CNF Nat} {s : State} {rank : Lit → Nat}
    (graph : ReasonGraph formula s s.assigned rank) (bounds : TrailBounds s) :
    ReasonGraph formula s.restart s.restart.assigned rank := by
  have forced := Nat.le_trans bounds.forcedProcessed bounds.processedAssigned
  have restricted := graph.prefix forced
  rw [restart_assigned bounds]
  exact restricted.frame restart_arena restart_reasons restart_trail restart_nVars

theorem ReasonGraph.addClause {formula : Std.Sat.CNF Nat} {s : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula s count rank) (lits : Array Lit) (original : Bool) :
    ReasonGraph formula (s.addClause lits original).1 count rank := by
  constructor
  · simpa only [addClause_trail] using graph.countBound
  · simpa only [addClause_trail] using graph.ranks
  · simpa only [addClause_trail] using graph.distinctVariables
  · intro i before nondecision
    have old : s.reason s.trail[i]! ≠ 0 := by
      simpa only [State.reason, addClause_reasons, addClause_trail] using nondecision
    obtain ⟨reason, packed, nonempty, head, entailed, earlier⟩ := graph.clauses i before old
    refine ⟨reason, ?_, nonempty, ?_, entailed, ?_⟩
    · simpa only [State.reason, addClause_reasons, addClause_trail] using packed.addClause lits
    · simpa only [addClause_trail] using head
    · simpa only [addClause_trail] using earlier

/-- Concrete earlier reason tails establish the semantic dependency used for
root soundness and compatible-model preservation. -/
theorem ReasonGraph.reasonConsequences {formula : Std.Sat.CNF Nat} {s : State} {rank : Lit → Nat}
    (graph : ReasonGraph formula s s.assigned rank) : ReasonConsequences formula s := by
  intro i before nondecision a model compatible
  obtain ⟨lits, _, nonempty, head, entailed, earlier⟩ := graph.clauses i before nondecision
  have trueHead : a (literalView s.trail[i]!.negate).1 = (literalView s.trail[i]!.negate).2 := by
    apply Logic.forced_of_sat (entailed a model)
    intro viewed member different
    obtain ⟨lit, original, equal⟩ := clauseView_mem.mp member
    obtain ⟨j, bound, value⟩ := Array.mem_iff_getElem.mp original
    have read : lits[j]! = lit := by simpa only [getElem!_pos lits j bound] using value
    by_cases first : j = 0
    · subst j
      exact False.elim (different (equal.symm.trans (congrArg literalView (read.symm.trans head))))
    · obtain ⟨k, lower, prior⟩ := earlier j (by omega) bound
      have falseLit := compatible k lower
      simpa only [Falsifies, prior, read, equal] using falseLit
  have falseLit := (falsifies_negate_iff a s.trail[i]!.negate).mpr trueHead
  simpa only [negate_negate] using falseLit

end MicrosatLean.Verification.Implementation.Native.Analysis
