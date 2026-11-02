import MicrosatLean.Verification.Implementation.Search.WatchState
import MicrosatLean.Verification.Implementation.Search.WatchUnit

namespace MicrosatLean.Verification.Implementation.Search

open CDCL Bridge

/-- Root mode makes the entire active trail unconditional. Recording those
roots exposes the genuine false clause required by the readable UNSAT gate. -/
theorem root_conflict_trace {formula : Formula} {s : State}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) s original learned heads rank)
    (roots : ∀ i, i < s.assigned → s.mark s.trail[i]! = 6)
    {entry : StoredClause} (stored : entry ∈ original ++ learned)
    (falseClause : ∀ lit ∈ entry.lits, s.mark lit ≠ 0) (stats : Stats) :
    ∃ after, LogicalExecution (formulaView formula) (logicalView s original learned) after ∧
      Terminal formula after (.unsat stats) := by
  obtain ⟨order, ordered⟩ := base.order
  let machine : Machine := ⟨s, 0, .watch, 0, true, 0, 0⟩
  let before := logicalView s original learned
  have rep : Rep machine before (representationWitness original learned heads order) := view_rep base ordered
  let after := { before with rootSize := s.assigned }
  refine ⟨after, Logic.single_move (.commitRoots before s.assigned ?_ ?_ ?_), ?_⟩
  · exact Nat.le_trans base.bounds.forcedProcessed base.bounds.processedAssigned
  · simp only [before, logicalView, trailView_length, Nat.le_refl]
  · intro lit member valuation model
    obtain ⟨i, bound, equal⟩ := (prefix_mem_iff
      (by simp only [before, logicalView, trailView_length, Nat.le_refl]) lit).mp member
    have falseValue := base.roots s.trail[i]! ⟨i, bound, rfl⟩ (roots i bound) valuation model
    rw [← equal, rep.trail i bound]
    exact view_true_of_falsifies valuation _ falseValue
  · refine ⟨by simp only [after, before, logicalView, trailView_length], entry.view, ?_, ?_⟩
    · change entry.view ∈ before.database
      rw [logicalView_database]
      exact List.mem_map.mpr ⟨entry, stored, rfl⟩
    · intro lit member
      obtain ⟨encoded, contained, equal⟩ := clauseView_mem.mp member
      rw [← equal]
      have falseBefore := (falseBefore_iff rep (Nat.le_refl s.assigned) encoded).mpr
        (base.marked encoded (falseClause encoded contained))
      have whole : (trailView s (original ++ learned)).take s.assigned =
          trailView s (original ++ learned) :=
        List.take_of_length_le (by simp only [trailView_length, Nat.le_refl])
      simpa only [FalseBefore, prefixLiterals, before, logicalView, trailView_length, List.take_length,
        after, LogicalState.trueTrail, whole] using falseBefore

end MicrosatLean.Verification.Implementation.Search

namespace MicrosatLean.Verification.Implementation.Search

open CDCL Bridge
open Representation Propagation Concrete

/-- A concrete watch result has a trace to its represented endpoint, or to a
logical state satisfying the final result gate. -/
def WatchTrace (formula : Formula) (before : LogicalState) : Progress → Prop
  | .running after => ∃ original learned heads rank,
      StateCertificate (formulaView formula) after.solver original learned heads rank ∧
      LogicalExecution (formulaView formula) before (logicalView after.solver original learned)
  | .finished result => ∃ after, LogicalExecution (formulaView formula) before after ∧
      Terminal formula after result

theorem WatchTrace.prepend {formula : Formula} {before middle : LogicalState} {result : Progress}
    (first : LogicalExecution (formulaView formula) before middle)
    (rest : WatchTrace formula middle result) : WatchTrace formula before result := by
  cases result with
  | running after =>
    obtain ⟨original, learned, heads, rank, base, trace⟩ := rest
    exact ⟨original, learned, heads, rank, base, Logic.execution_trans first trace⟩
  | finished result =>
    obtain ⟨after, trace, terminal⟩ := rest
    exact ⟨after, Logic.execution_trans first trace, terminal⟩

/-- The finite source traversal records every database permutation before
the selected unit or conflict exit. The analyzer refinement is supplied
separately, so this induction follows only watched-literal control flow. -/
theorem propagateWatches_trace {formula : Formula} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat} {count : Nat}
    (facts : WatchScanFacts (formulaView formula) (restoreWatchArrays s arena first)
      original learned heads rank count lit previous remaining)
    (mode : Search.Concrete.PropagationMode s root) (processed : s.processed = count + 1)
    (value : s.trail[count]! = lit) (budget : remaining.length < fuel)
    (analysis : ∀ (state : State) (original learned : List StoredClause) (heads : Lit → List Nat) (rank : Lit → Nat),
      StateCertificate (formulaView formula) state original learned heads rank →
      Analysis.DecisionHistory state (original ++ learned) →
      Search.Concrete.NonrootPhase state → ∀ entry ∈ original ++ learned,
      (∀ literal ∈ entry.lits, state.mark literal ≠ 0) →
      let result := analyze state entry.id
      let root := result.1.db (result.2 + 1) == 0
      WatchTrace formula (logicalView state original learned)
        (.running ⟨result.1.assign result.2 root, decision, .nextLiteral, oldLemmas, root, 0, 0⟩)) :
    WatchTrace formula (logicalView (restoreWatchArrays s arena first) original learned)
      (propagateWatches fuel s arena first decision oldLemmas root lit previous) := by
  have countBefore : count < s.assigned := by
    have assigned := facts.base.bounds.processedAssigned
    change s.processed ≤ s.assigned at assigned
    omega
  have literal : Representation.LiteralBound s.nVars lit := by
    simpa only [restoreWatchArrays, value] using (facts.base.active count countBefore).1
  have falseLit : s.mark lit ≠ 0 := by
    simpa only [restoreWatchArrays, State.mark, value] using (facts.base.active count countBefore).2.1
  induction remaining generalizing fuel arena first previous original learned heads rank with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have empty : currentWatchRef arena first lit previous = 0 := by
        simpa only [restoreWatchArrays, List.headD_nil] using facts.cursor.current (facts.base.watches.links lit)
      simp only [currentWatchRef, beq_iff_eq] at empty
      simp only [propagateWatches, Id.run, pure, beq_iff_eq, empty, ite_true, WatchTrace]
      exact ⟨original, learned, heads, rank, facts.base, .refl _⟩
  | cons ref rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have current : currentWatchRef arena first lit previous = ref := by
        simpa only [restoreWatchArrays, List.headD_cons] using facts.cursor.current (facts.base.watches.links lit)
      have nonzero := storedWatchRef_nonzero facts.base.database
        (facts.base.watches.references lit ref facts.cursor.member)
      have currentNonzero : currentWatchRef arena first lit previous ≠ 0 := by simpa only [current] using nonzero
      cases found : replacement (orientWatch arena (watchClause ref) lit) s.marks (watchClause ref) with
      | some pos =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = some pos := by simpa only [current] using found
        obtain ⟨nextOriginal, nextLearned, nextFacts⟩ := facts.move literal falseLit found
        have next := ih fuel (movedWatchArrays arena first lit ref previous pos).1
          (movedWatchArrays arena first lit ref previous pos).2 previous nextFacts
          (by simp only [List.length_cons] at budget; omega)
        have trace := moved_trace facts.base facts.cursor found nextFacts.base.database
        have combined := next.prepend trace
        rw [propagateWatches_replacement fuel s arena first decision oldLemmas root lit previous pos currentNonzero foundCurrent]
        simpa only [current] using combined
      | none =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = none := by simpa only [current] using found
        let retained := Propagation.retainWatch arena (watchClause ref) lit
        let other : Lit := retained[watchClause ref]!
        by_cases satisfied : s.mark other.negate ≠ 0
        · have satisfiedCurrent : s.mark (Lit.negate
              ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) ≠ 0 := by simpa only [current] using satisfied
          obtain ⟨nextOriginal, nextLearned, nextFacts⟩ := facts.skip falseLit satisfied
          have next := ih fuel retained first ref nextFacts (by simp only [List.length_cons] at budget; omega)
          have trace := retained_trace facts.base facts.cursor.member falseLit nextFacts.base.database
          have combined := next.prepend trace
          rw [propagateWatches_skip fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent satisfiedCurrent]
          simpa only [current] using combined
        · have opposite : s.mark other.negate = 0 := by simpa using satisfied
          by_cases unmarked : s.mark other = 0
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) = 0 := by simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by simpa only [current] using opposite
            obtain ⟨nextOriginal, nextLearned, nextRank, nextFacts⟩ :=
              facts.unit falseLit root mode.roots found unmarked opposite
            have trace := watch_unit_trace facts.base facts.cursor.member falseLit found unmarked opposite root nextFacts.base.database
            rw [propagateWatches_unit fuel s arena first decision oldLemmas root lit previous
              currentNonzero foundCurrent headCurrent oppositeCurrent]
            simp only [current, WatchTrace]
            exact ⟨nextOriginal, nextLearned, heads, nextRank, nextFacts.base, trace⟩
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) ≠ 0 := by simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by simpa only [current] using opposite
            rw [propagateWatches_conflict fuel s arena first decision oldLemmas root lit previous
              currentNonzero foundCurrent oppositeCurrent headCurrent]
            simp only [current]
            obtain ⟨nextOriginal, nextLearned, conflict, nextBase, _, member, id, allFalse⟩ :=
              facts.base.retainedConflict facts.cursor.member falseLit found unmarked
            have orient := retained_trace facts.base facts.cursor.member falseLit nextBase.database
            cases root with
            | false =>
              simp only [Bool.false_eq_true, ite_false]
              have oldPhase := mode.nonroot rfl
              have phase : Search.Concrete.NonrootPhase
                  (restoreWatchArrays s retained first) := ⟨oldPhase.levels, oldPhase.caches, oldPhase.nonroot⟩
              obtain ⟨orientedOriginal, orientedLearned, oriented⟩ := facts.orient falseLit
              obtain ⟨sameOriginal, sameLearned⟩ := oriented.base.database.unique nextBase.database
              rw [sameOriginal, sameLearned] at oriented
              have next := analysis _ nextOriginal nextLearned _ _ nextBase oriented.history phase conflict member allFalse
              have combined := next.prepend orient
              simpa only [id, restoreWatchArrays] using combined
            | true =>
              simp only [ite_true, WatchTrace]
              obtain ⟨after, trace, terminal⟩ := root_conflict_trace nextBase (mode.roots rfl) member allFalse s.stats
              exact ⟨after, Logic.execution_trans orient trace, terminal⟩

end MicrosatLean.Verification.Implementation.Search
