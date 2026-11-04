import MicrosatLean.Verification.Implementation.Analysis.Asserting

namespace MicrosatLean.Verification.Implementation.Analysis

open CDCL Representation
open Std.Sat

private structure LevelContext where
  source : State
  candidate : Nat
  rank : Lit → Nat
  lower : source.forced ≤ candidate
  ranked : ∀ i, i ≤ candidate → rank source.trail[i]! = i

private structure LevelInv (c : LevelContext) (offset : Nat) (acc : LearnedAcc) : Prop where
  frame : LearnedFrame c.source acc.1
  positive : 0 < acc.2.1.size
  upper : acc.1.processed ≤ c.candidate
  single : acc.2.1.size = 1 → ∀ i, c.candidate < i + offset → i < acc.1.processed →
    c.source.reason c.source.trail[i]! ≠ 0
  multiple : 1 < acc.2.1.size → ∀ i, c.rank acc.2.1[1]! < i → i < acc.1.processed →
    c.source.reason c.source.trail[i]! ≠ 0

private structure LevelPending (c : LevelContext) (offset pivot : Nat) (acc : LearnedAcc) : Prop where
  frame : LearnedFrame c.source acc.1
  positive : 0 < acc.2.1.size
  upper : acc.1.processed ≤ c.candidate
  single : acc.2.1.size = 1 → ∀ i, c.candidate < i + offset → i < acc.1.processed →
    i = pivot ∨ c.source.reason c.source.trail[i]! ≠ 0
  multiple : 1 < acc.2.1.size → ∀ i, c.rank acc.2.1[1]! < i → i < acc.1.processed →
    c.source.reason c.source.trail[i]! ≠ 0

private theorem levelFrame_setProcessed (s : State) (p : Nat) :
    LearnedFrame s { s with processed := p } := ⟨rfl, rfl⟩

private theorem LevelInv.retuple {c : LevelContext} {offset : Nat} {acc : LearnedAcc}
    (inv : LevelInv c offset acc) (lbd : Nat) (used : Bool) :
    LevelInv c offset (acc.1, acc.2.1, lbd, used) :=
  ⟨inv.frame, inv.positive, inv.upper, inv.single, inv.multiple⟩

private theorem LevelInv.clear {c : LevelContext} {offset : Nat} {acc : LearnedAcc}
    (inv : LevelInv c offset acc) (lit : Lit) :
    LevelInv c offset (acc.1.setMark lit 1, acc.2.1, acc.2.2.1, acc.2.2.2) :=
  ⟨inv.frame.trans (.ofMarkFrame (markFrame_setMark acc.1 lit 1)),
    inv.positive, inv.upper, inv.single, inv.multiple⟩

private theorem LevelPending.nondecision {c : LevelContext} {offset pivot : Nat} {acc : LearnedAcc}
    (inv : LevelPending c offset pivot acc)
    (nonzero : c.source.reason c.source.trail[pivot]! ≠ 0) : LevelInv c offset acc := by
  refine ⟨inv.frame, inv.positive, inv.upper, ?_, inv.multiple⟩
  intro single i visited before
  rcases inv.single single i visited before with equal | nonzeroI
  · simpa only [equal] using nonzero
  · exact nonzeroI

private theorem LevelPending.singleDecision {c : LevelContext} {offset pivot : Nat} {acc : LearnedAcc}
    (inv : LevelPending c offset pivot acc) (single : acc.2.1.size = 1)
    (frontier : c.candidate + 1 = pivot + offset) (upper : pivot ≤ c.candidate) :
    LevelInv c offset ({ acc.1 with processed := pivot }, acc.2.1, acc.2.2.1, acc.2.2.2) := by
  refine ⟨inv.frame.trans (levelFrame_setProcessed acc.1 pivot), inv.positive, upper, ?_, ?_⟩
  · intro _ i visited before
    change i < pivot at before
    omega
  · intro many
    change 1 < acc.2.1.size at many
    omega

private theorem LevelPending.multipleDecision {c : LevelContext} {offset pivot : Nat} {acc : LearnedAcc}
    (inv : LevelPending c offset pivot acc) (many : acc.2.1.size ≠ 1) : LevelInv c offset acc := by
  refine ⟨inv.frame, inv.positive, inv.upper, ?_, inv.multiple⟩
  intro single
  exact False.elim (many single)

private theorem finish_level {c : LevelContext} {offset pivot : Nat} {s : State} {lits : Array Lit}
    {lbd : Nat} {used : Bool} (inv : LevelPending c offset pivot (s, lits, lbd, used))
    (frontier : c.candidate + 1 = pivot + offset) (upper : pivot ≤ c.candidate)
    (lit : Lit) (read : lit = c.source.trail[pivot]!) :
    LevelInv c offset (finishBody pivot lit s lits lbd used).value := by
  have reasons : s.reasons = c.source.reasons := by simpa only using congrArg State.reasons inv.frame.restore
  have nondecision (nonzero : s.reason lit ≠ 0) : LevelInv c offset (s, lits, lbd, used) := by
    apply inv.nondecision
    simpa only [State.reason, reasons, read] using nonzero
  simp only [finishBody, Id.run, pure]
  split
  · split <;> split
    · have single : lits.size = 1 := by simpa using ‹(lits.size == 1) = true›
      exact ((inv.singleDecision single frontier upper).clear lit).retuple _ _
    · have many : lits.size ≠ 1 := by simpa using ‹¬ (lits.size == 1) = true›
      exact ((inv.multipleDecision many).clear lit).retuple _ _
    · have single : lits.size = 1 := by simpa using ‹(lits.size == 1) = true›
      exact ((inv.singleDecision single frontier upper).clear lit).retuple _ _
    · have many : lits.size ≠ 1 := by simpa using ‹¬ (lits.size == 1) = true›
      exact ((inv.multipleDecision many).clear lit).retuple _ _
  · have nonzero : s.reason lit ≠ 0 := by simpa using ‹¬ (s.reason lit == 0) = true›
    exact (nondecision nonzero).clear lit

private theorem pending_no_push {c : LevelContext} {offset : Nat} {acc : LearnedAcc}
    (inv : LevelInv c offset acc) (within : offset ≤ c.candidate) (next : State)
    (frame : MarkFrame acc.1 next) (lbd : Nat) (used : Bool) :
    LevelPending c (offset + 1) (c.candidate - offset) (next, acc.2.1, lbd, used) := by
  have processed : next.processed = acc.1.processed := by simpa only using congrArg State.processed frame.restore
  refine ⟨inv.frame.trans (.ofMarkFrame frame), inv.positive, ?_, ?_, ?_⟩
  · simpa only [processed] using inv.upper
  · intro single i visited before
    by_cases current : i = c.candidate - offset
    · exact Or.inl current
    · exact Or.inr (inv.single single i (by omega) (by simpa only [processed] using before))
  · intro many i above before
    exact inv.multiple many i above (by simpa only [processed] using before)

private theorem pending_push {c : LevelContext} {offset : Nat} {acc : LearnedAcc}
    (inv : LevelInv c offset acc) (within : offset ≤ c.candidate) (next : State)
    (frame : MarkFrame acc.1 next) (lbd : Nat) (used : Bool) :
    LevelPending c (offset + 1) (c.candidate - offset)
      (next, acc.2.1.push acc.1.trail[c.candidate - offset]!, lbd, used) := by
  have processed : next.processed = acc.1.processed := by simpa only using congrArg State.processed frame.restore
  have trail : acc.1.trail = c.source.trail := inv.frame.trail
  refine ⟨inv.frame.trans (.ofMarkFrame frame), by simp only [Array.size_push]; omega, ?_, ?_, ?_⟩
  · simpa only [processed] using inv.upper
  · intro single
    have := inv.positive
    simp only [Array.size_push] at single
    omega
  · intro _ i above before
    by_cases single : acc.2.1.size = 1
    · have tail : (acc.2.1.push acc.1.trail[c.candidate - offset]!)[1]! = acc.1.trail[c.candidate - offset]! := by
        rw [← single]
        simp
      have rankTail : c.rank acc.1.trail[c.candidate - offset]! = c.candidate - offset := by
        rw [trail]
        exact c.ranked _ (Nat.sub_le _ _)
      rw [tail, rankTail] at above
      exact inv.single single i (by omega) (by simpa only [processed] using before)
    · have many : 1 < acc.2.1.size := by have := inv.positive; omega
      have tail : (acc.2.1.push acc.1.trail[c.candidate - offset]!)[1]! = acc.2.1[1]! := by
        rw [getElem!_pos _ 1 (by simp only [Array.size_push]; omega), Array.getElem_push_lt many,
          ← getElem!_pos acc.2.1 1 many]
      rw [tail] at above
      exact inv.multiple many i above (by simpa only [processed] using before)

private theorem level_step {c : LevelContext} {offset : Nat} {acc : LearnedAcc}
    (inv : LevelInv c offset acc) (bound : offset < c.candidate + 1 - c.source.forced) :
    LevelInv c (offset + 1) (learnedBody c.candidate offset acc).value := by
  have within : offset ≤ c.candidate := by omega
  have frontier : c.candidate + 1 = c.candidate - offset + (offset + 1) := by omega
  have read : acc.1.trail[c.candidate - offset]! = c.source.trail[c.candidate - offset]! :=
    congrArg (fun words : Array Lit => words[c.candidate - offset]!) inv.frame.trail
  rw [learnedBody_eq]
  dsimp only
  split
  · let result := implied (acc.1.nVars + 1) acc.1 acc.1.trail[c.candidate - offset]!
    have frame : MarkFrame acc.1 result.1 := implied_markFrame _ _ _
    split
    · exact finish_level (pending_push inv within result.1 frame _ _) frontier (Nat.sub_le _ _) _ read
    · exact finish_level (pending_no_push inv within result.1 frame _ _) frontier (Nat.sub_le _ _) _ read
  · exact finish_level (pending_no_push inv within acc.1 (MarkFrame.refl _) _ _)
      frontier (Nat.sub_le _ _) _ read

private theorem level_loop (c : LevelContext) (fuel start : Nat) (acc : LearnedAcc)
    (bound : start + fuel ≤ c.candidate + 1 - c.source.forced) (inv : LevelInv c start acc) :
    LevelInv c (start + fuel) (forIn (m := Id) (List.range' start fuel) acc (learnedBody c.candidate)) := by
  induction fuel generalizing start acc with
  | zero => simpa only [List.range'_zero, List.forIn_nil, pure, Nat.add_zero] using inv
  | succ fuel ih =>
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨next, execute⟩ := learnedBody_yields c.candidate start acc
    have step := level_step inv (by omega)
    rw [execute]
    simp only [bind]
    have nextInv : LevelInv c (start + 1) next := by simpa only [execute, ForInStep.value_yield] using step
    have final := ih (start + 1) next (by omega) nextInv
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final

/-- Once the actual UIP has been appended first, the real loop tracks the
nearest decision above its highest tail. The cursor changes while only the
head is present; the gap freezes when the second literal is appended. -/
private theorem buildLearned_level_gaps (s : State) (candidate : Nat) (rank : Lit → Nat)
    (lower : s.forced ≤ candidate) (ranked : ∀ i, i ≤ candidate → rank s.trail[i]! = i)
    (marked : s.mark s.trail[candidate]! = 2)
    (failed : (implied (s.nVars + 1) { s with processed := candidate } s.trail[candidate]!).2 = false) :
    let built := buildLearned s candidate
    (built.2.1.size = 1 → ∀ i, s.forced ≤ i → i < built.1.processed →
      s.reason s.trail[i]! ≠ 0) ∧
    (1 < built.2.1.size → ∀ i, rank built.2.1[1]! < i → i < built.1.processed →
      s.reason s.trail[i]! ≠ 0) := by
  let c : LevelContext := ⟨s, candidate, rank, lower, ranked⟩
  let initial : LearnedAcc := ({ s with processed := candidate }, #[], 0, false)
  let next := (implied (s.nVars + 1) { s with processed := candidate } s.trail[candidate]!).1
  have markFrame : MarkFrame { s with processed := candidate } next := implied_markFrame _ _ _
  have processed : next.processed = candidate := by simpa only using congrArg State.processed markFrame.restore
  have frame : LearnedFrame s next := (levelFrame_setProcessed s candidate).trans (.ofMarkFrame markFrame)
  have pending : LevelPending c 1 candidate (next, #[s.trail[candidate]!], 0, true) := by
    refine ⟨frame, by simp, ?_, ?_, ?_⟩
    · change next.processed ≤ candidate
      rw [processed]
      exact Nat.le_refl _
    · intro _ i visited before
      change candidate < i + 1 at visited
      change i < next.processed at before
      rw [processed] at before
      omega
    · intro many
      change 1 < (#[s.trail[candidate]!] : Array Lit).size at many
      simp at many
  have first : learnedBody candidate 0 initial = finishBody candidate s.trail[candidate]! next
      #[s.trail[candidate]!] 0 true := by
    rw [learnedBody_eq]
    simp only [initial, Nat.sub_zero]
    simp only [State.mark] at marked
    simp only [State.mark, marked, beq_self_eq_true, failed, Bool.not_false, ↓reduceIte]
    rfl
  have firstInv : LevelInv c 1 (learnedBody candidate 0 initial).value := by
    rw [first]
    exact finish_level pending rfl (Nat.le_refl _) _ rfl
  obtain ⟨firstAcc, execute⟩ := learnedBody_yields candidate 0 initial
  have firstInv' : LevelInv c 1 firstAcc := by simpa only [execute, ForInStep.value_yield] using firstInv
  have remaining := level_loop c (candidate - s.forced) 1 firstAcc (by dsimp only [c]; omega) firstInv'
  have count : candidate + 1 - s.forced = (candidate - s.forced) + 1 := by omega
  have final : LevelInv c (candidate + 1 - s.forced)
      (forIn (m := Id) (List.range' 0 (candidate + 1 - s.forced)) initial (learnedBody candidate)) := by
    rw [count, List.range'_succ, List.forIn_cons, execute]
    simp only [bind]
    simpa only [Nat.zero_add, Nat.add_comm] using remaining
  rw [buildLearned_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  constructor
  · intro single i above before
    exact final.single single i (by dsimp only [c]; omega) before
  · exact final.multiple

/-- A singleton learned clause leaves no decision in the actual retained
nonroot prefix: while the head is alone, every encountered decision lowers
the runtime cursor. -/
theorem buildLearned_single_no_retained_decision (s : State) (candidate : Nat) (rank : Lit → Nat)
    (lower : s.forced ≤ candidate) (ranked : ∀ i, i ≤ candidate → rank s.trail[i]! = i)
    (marked : s.mark s.trail[candidate]! = 2)
    (failed : (implied (s.nVars + 1) { s with processed := candidate } s.trail[candidate]!).2 = false)
    (single : (buildLearned s candidate).2.1.size = 1) :
    ∀ i, s.forced ≤ i → i < (buildLearned s candidate).1.processed →
      s.reason s.trail[i]! ≠ 0 :=
  (buildLearned_level_gaps s candidate rank lower ranked marked failed).1 single

/-- The exact gap maintained after the second retained literal is appended. -/
theorem buildLearned_no_decision_above_highest_tail (s : State) (candidate : Nat) (rank : Lit → Nat)
    (lower : s.forced ≤ candidate) (ranked : ∀ i, i ≤ candidate → rank s.trail[i]! = i)
    (marked : s.mark s.trail[candidate]! = 2)
    (failed : (implied (s.nVars + 1) { s with processed := candidate } s.trail[candidate]!).2 = false) :
    let built := buildLearned s candidate
    1 < built.2.1.size → ∀ i, rank built.2.1[1]! < i → i < built.1.processed →
      s.reason s.trail[i]! ≠ 0 :=
  (buildLearned_level_gaps s candidate rank lower ranked marked failed).2

/-- A real decision retained in the birth prefix cannot lie above the highest
tail. This supplies the concrete older-decision/tail inequality required by
clause-origin migration, without assuming cursor minimality. -/
theorem buildLearned_retained_decision_le_tail (s : State) (candidate : Nat) (rank : Lit → Nat)
    (lower : s.forced ≤ candidate) (ranked : ∀ i, i ≤ candidate → rank s.trail[i]! = i)
    (marked : s.mark s.trail[candidate]! = 2)
    (failed : (implied (s.nVars + 1) { s with processed := candidate } s.trail[candidate]!).2 = false)
    (many : 1 < (buildLearned s candidate).2.1.size) (decision : Nat)
    (retained : decision < (buildLearned s candidate).1.processed)
    (isDecision : s.reason s.trail[decision]! = 0) :
    decision ≤ rank (buildLearned s candidate).2.1[1]! := by
  by_cases below : decision ≤ rank (buildLearned s candidate).2.1[1]!
  · exact below
  · have gap := buildLearned_no_decision_above_highest_tail s candidate rank lower ranked marked failed
      many decision (by omega) retained
    exact False.elim (gap isDecision)

end MicrosatLean.Verification.Implementation.Analysis
