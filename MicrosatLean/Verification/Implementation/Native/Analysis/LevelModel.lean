import MicrosatLean.Verification.Implementation.Native.Analysis.Tags
import MicrosatLean.Verification.Implementation.Native.Analysis.ImpliedSound

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation
open Std.Sat

/-- Every nondecision in the current block has an actual reason-tail parent
in that same block. Earlier-trail order comes from the concrete reason graph.
Reachability must establish this property from propagation quiescence. -/
def ReasonLevelParent (snapshot : State) (count decision : Nat) : Prop :=
  ∀ i, decision ≤ i → i < count → snapshot.reason snapshot.trail[i]! ≠ 0 →
    ∀ lits, PackedClause snapshot (snapshot.reason snapshot.trail[i]!) lits →
      ∃ j k, 0 < j ∧ j < lits.size ∧ decision ≤ k ∧ k < i ∧ snapshot.trail[k]! = lits[j]!

/-- A proof-only assignment reverses the current block and keeps all earlier
trail assignments. Distinct variables make its indexed choices unambiguous. -/
noncomputable def blockAssignment (snapshot : State) (count decision : Nat) (var : Nat) : Bool := by
  classical
  exact if found : ∃ i, i < count ∧ snapshot.trail[i]!.var = var then
    let i := Classical.choose found
    if decision ≤ i then (literalView snapshot.trail[i]!).2 else !(literalView snapshot.trail[i]!).2
  else false

theorem blockAssignment_at {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (decision i : Nat) (before : i < count) :
    blockAssignment snapshot count decision snapshot.trail[i]!.var =
      if decision ≤ i then (literalView snapshot.trail[i]!).2 else !(literalView snapshot.trail[i]!).2 := by
  classical
  have found : ∃ j, j < count ∧ snapshot.trail[j]!.var = snapshot.trail[i]!.var := ⟨i, before, rfl⟩
  have chosen := Classical.choose_spec found
  have equal := graph.distinctVariables (Classical.choose found) i chosen.1 before chosen.2
  simp only [blockAssignment, dite_eq_left found]
  rw [equal]

theorem blockAssignment_true {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (decision i : Nat) (before : i < count)
    (current : decision ≤ i) :
    blockAssignment snapshot count decision (literalView snapshot.trail[i]!).1 =
      (literalView snapshot.trail[i]!).2 := by
  change blockAssignment snapshot count decision snapshot.trail[i]!.var = _
  rw [blockAssignment_at graph decision i before, ite_eq_left current]

theorem blockAssignment_false {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (decision i : Nat) (before : i < count)
    (earlier : i < decision) : Falsifies (blockAssignment snapshot count decision) snapshot.trail[i]! := by
  change blockAssignment snapshot count decision snapshot.trail[i]!.var ≠ (literalView snapshot.trail[i]!).2
  rw [blockAssignment_at graph decision i before, ite_eq_right (by omega)]
  cases (literalView snapshot.trail[i]!).2 <;> decide

noncomputable def reasonWords {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (i : Nat) : Array Lit := by
  classical
  exact if before : i < count then
    if propagated : snapshot.reason snapshot.trail[i]! ≠ 0 then
      Classical.choose (graph.clauses i before propagated)
    else #[]
  else #[]

theorem reasonWords_spec {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (i : Nat) (before : i < count)
    (propagated : snapshot.reason snapshot.trail[i]! ≠ 0) :
    let lits := reasonWords graph i
    PackedClause snapshot (snapshot.reason snapshot.trail[i]!) lits ∧
      0 < lits.size ∧ lits[0]! = snapshot.trail[i]!.negate ∧
      CNF.EntailsClause formula (clauseView lits) ∧
      ∀ j, 0 < j → j < lits.size → ∃ k, k < i ∧ snapshot.trail[k]! = lits[j]! := by
  classical
  simpa only [reasonWords, dite_eq_left before, dite_eq_left propagated] using
    Classical.choose_spec (graph.clauses i before propagated)

private noncomputable def reasonViews {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) : List (CNF.Clause Nat) := by
  classical
  exact (List.range count).filterMap fun i =>
    if snapshot.reason snapshot.trail[i]! ≠ 0 then some (clauseView (reasonWords graph i)) else none

private def rootViews (snapshot : State) (count : Nat) (s : State) : List (CNF.Clause Nat) :=
  (List.range count).filterMap fun i =>
    if s.mark snapshot.trail[i]! == 6 then some (clauseView #[snapshot.trail[i]!.negate]) else none

/-- The concrete proof-only CNF contains all actual reason clauses and a unit
for every initial tag-six entry. It is independent of the input's models. -/
noncomputable def explanationFormula {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (s : State) : CNF Nat :=
  ⟨(reasonViews graph ++ rootViews snapshot count s).toArray⟩

private theorem reason_mem {formula : CNF Nat} {snapshot s : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (i : Nat) (before : i < count)
    (propagated : snapshot.reason snapshot.trail[i]! ≠ 0) :
    clauseView (reasonWords graph i) ∈ explanationFormula graph s := by
  classical
  apply List.mem_toArray.mpr
  apply List.mem_append_left
  apply List.mem_filterMap.mpr
  exact ⟨i, List.mem_range.mpr before, by simp only [ite_eq_left propagated]⟩

private theorem root_mem {formula : CNF Nat} {snapshot s : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (i : Nat) (before : i < count)
    (six : s.mark snapshot.trail[i]! = 6) :
    clauseView #[snapshot.trail[i]!.negate] ∈ explanationFormula graph s := by
  apply List.mem_toArray.mpr
  apply List.mem_append_right
  apply List.mem_filterMap.mpr
  exact ⟨i, List.mem_range.mpr before, by simp only [six, beq_self_eq_true, ↓reduceIte]⟩

private theorem unit_negate_false {a : Nat → Bool} {lit : Lit}
    (satisfied : CNF.Clause.Sat a (clauseView #[lit.negate])) : Falsifies a lit := by
  obtain ⟨viewed, member, value⟩ := CNF.Clause.sat_iff_exists_mem_eq.mp satisfied
  obtain ⟨encoded, encodedMember, equal⟩ := clauseView_mem.mp member
  have same : encoded = lit.negate := by simpa using encodedMember
  have head : a (literalView lit.negate).1 = (literalView lit.negate).2 := by
    simpa only [← equal, same] using value
  have falseLit := (falsifies_negate_iff a lit.negate).mpr head
  simpa only [negate_negate] using falseLit

private theorem assignment_sat_reason {formula : CNF Nat} {snapshot : State} {count decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (parents : ReasonLevelParent snapshot count decision) (i : Nat) (before : i < count)
    (propagated : snapshot.reason snapshot.trail[i]! ≠ 0) :
    CNF.Clause.Sat (blockAssignment snapshot count decision) (clauseView (reasonWords graph i)) := by
  have spec := reasonWords_spec graph i before propagated
  by_cases earlier : i < decision
  · have headTrue := (falsifies_negate_iff (blockAssignment snapshot count decision) snapshot.trail[i]!.negate).mp
      (by simpa only [negate_negate] using blockAssignment_false graph decision i before earlier)
    apply CNF.Clause.sat_of_mem_of_eq (lit := literalView snapshot.trail[i]!.negate) _ headTrue
    apply clauseView_mem.mpr
    refine ⟨(reasonWords graph i)[0]!, ?_, congrArg literalView spec.2.2.1⟩
    simpa only [getElem!_pos (reasonWords graph i) 0 spec.2.1] using Array.getElem_mem spec.2.1
  · obtain ⟨j, k, positive, bound, current, parentBefore, equal⟩ :=
      parents i (by omega) before propagated (reasonWords graph i) spec.1
    have parentTrue := blockAssignment_true graph decision k (Nat.lt_trans parentBefore before) current
    apply CNF.Clause.sat_of_mem_of_eq (lit := literalView snapshot.trail[k]!) _ parentTrue
    apply clauseView_mem.mpr
    refine ⟨(reasonWords graph i)[j]!, ?_, congrArg literalView equal.symm⟩
    simpa only [getElem!_pos (reasonWords graph i) j bound] using Array.getElem_mem bound

theorem explanationFormula_sat {formula : CNF Nat} {snapshot s : State} {count decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (parents : ReasonLevelParent snapshot count decision)
    (rootEarlier : ∀ i, i < count → s.mark snapshot.trail[i]! = 6 → i < decision) :
    CNF.Sat (blockAssignment snapshot count decision) (explanationFormula graph s) := by
  classical
  apply CNF.sat_of_all_mem_sat
  intro clause member
  change clause ∈ (reasonViews graph ++ rootViews snapshot count s).toArray at member
  rcases List.mem_append.mp (List.mem_toArray.mp member) with reason | root
  · obtain ⟨i, inRange, entry⟩ := List.mem_filterMap.mp reason
    have before := List.mem_range.mp inRange
    by_cases propagated : snapshot.reason snapshot.trail[i]! ≠ 0
    · have equal : clauseView (reasonWords graph i) = clause := by
        simpa only [ite_eq_left propagated, Option.some.injEq] using entry
      rw [← equal]
      exact assignment_sat_reason graph parents i before propagated
    · simp only [ite_eq_right propagated, reduceCtorEq] at entry
  · obtain ⟨i, inRange, entry⟩ := List.mem_filterMap.mp root
    have before := List.mem_range.mp inRange
    by_cases six : s.mark snapshot.trail[i]! = 6
    · have equal : clauseView #[snapshot.trail[i]!.negate] = clause := by
        simpa only [six, beq_self_eq_true, ↓reduceIte, Option.some.injEq] using entry
      rw [← equal]
      have falseLit := blockAssignment_false graph decision i before (rootEarlier i before six)
      have headTrue := (falsifies_negate_iff (blockAssignment snapshot count decision) snapshot.trail[i]!.negate).mp
        (by simpa only [negate_negate] using falseLit)
      apply CNF.Clause.sat_of_mem_of_eq (lit := literalView snapshot.trail[i]!.negate) _ headTrue
      exact clauseView_mem.mpr ⟨_, by simp, rfl⟩
    · simp only [beq_iff_eq, six, ↓reduceIte, reduceCtorEq] at entry

theorem explanationFormula_graph {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (s : State) :
    ReasonGraph (explanationFormula graph s) snapshot count rank := by
  refine ⟨graph.countBound, graph.ranks, graph.distinctVariables, ?_⟩
  intro i before propagated
  have spec := reasonWords_spec graph i before propagated
  exact ⟨reasonWords graph i, spec.1, spec.2.1, spec.2.2.1,
    fun _ model => CNF.sat_of_mem model (reason_mem graph i before propagated), spec.2.2.2.2⟩

theorem explanationFormula_cache {formula : CNF Nat} {snapshot s : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (tags : ValidMarkTags snapshot count s) :
    ImpliedCache (explanationFormula graph s) snapshot count rank
      (fun lit => TrailMember snapshot count lit ∧ s.mark lit = 2) s := by
  refine ⟨tags, fun _ member marked => ⟨member, marked⟩, ?_⟩
  intro lit member six a model _
  obtain ⟨i, before, equal⟩ := member
  have rootUnit := root_mem graph i before (by simpa only [equal] using six)
  have falseLit := unit_negate_false (CNF.sat_of_mem model rootUnit)
  simpa only [equal] using falseLit

/-- The sole current-level UIP cannot be removed by the actual recursive
minimizer. The concrete synthetic CNF has a proved model in which that UIP is
true while all its strictly earlier original MARK assumptions are false.
No satisfiability assumption about the original input is used. -/
theorem implied_false_of_level_parent {formula : CNF Nat} {snapshot s : State}
    {count decision candidate : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (storage : ReasonStorage snapshot s)
    (parents : ReasonLevelParent snapshot count decision) (tags : ValidMarkTags snapshot count s)
    (lower : decision ≤ candidate) (before : candidate < count)
    (clear : ∀ i, decision ≤ i → i < candidate → s.mark snapshot.trail[i]! ≠ 2)
    (rootEarlier : ∀ i, i < count → s.mark snapshot.trail[i]! = 6 → i < decision)
    (fuel : Nat) : (implied fuel s snapshot.trail[candidate]!).2 = false := by
  have model := explanationFormula_sat graph parents rootEarlier
  have trueCandidate := blockAssignment_true graph decision candidate before lower
  have cache := explanationFormula_cache graph tags
  have sound := implied_sound (explanationFormula_graph graph s) fuel s snapshot.trail[candidate]!
    storage cache ⟨candidate, before, rfl⟩
  have notTrue : (implied fuel s snapshot.trail[candidate]!).2 ≠ true := by
    intro successful
    have falseCandidate := sound.2 successful (blockAssignment snapshot count decision) model
    apply falseCandidate
    · intro lit leaf earlier
      obtain ⟨⟨i, inRange, equal⟩, marked⟩ := leaf
      have earlierIndex : i < candidate := by
        rw [← equal, graph.ranks i inRange, graph.ranks candidate before] at earlier
        exact earlier
      have belowDecision : i < decision := by
        by_cases current : decision ≤ i
        · exact False.elim (clear i current earlierIndex (by simpa only [equal] using marked))
        · omega
      simpa only [equal] using blockAssignment_false graph decision i inRange belowDecision
    · exact trueCandidate
  exact Bool.eq_false_iff.mpr notTrue

end MicrosatLean.Verification.Implementation.Native.Analysis
