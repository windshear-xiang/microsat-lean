import MicrosatLean.Verification.Implementation.Analysis.LearnedFrame
import MicrosatLean.Verification.Implementation.Analysis.Backjump
import MicrosatLean.Verification.Implementation.Analysis.ReasonUpdates
import MicrosatLean.Verification.Implementation.Analysis.MarkSupport

namespace MicrosatLean.Verification.Implementation.Analysis

open CDCL Representation Std.Sat

private structure CursorContext where
  source : State
  candidate : Nat
  rank : Lit → Nat
  lower : source.forced ≤ candidate
  ranked : ∀ i, i ≤ candidate → rank source.trail[i]! = i

private structure CursorInvariant (c : CursorContext) (offset : Nat) (acc : LearnedAcc) : Prop where
  frame : LearnedFrame c.source acc.1
  lower : c.source.forced ≤ acc.1.processed
  upper : acc.1.processed ≤ c.candidate
  frontier : c.candidate < acc.1.processed + offset ∨ offset = 0 ∧ acc.1.processed = c.candidate
  size : acc.2.1.size ≤ offset
  positions : ∀ j, j < acc.2.1.size →
    c.source.forced ≤ c.rank acc.2.1[j]! ∧ c.rank acc.2.1[j]! ≤ c.candidate ∧
      c.source.trail[c.rank acc.2.1[j]!]! = acc.2.1[j]! ∧ c.candidate < c.rank acc.2.1[j]! + offset
  tails : ∀ j, 0 < j → j < acc.2.1.size → c.rank acc.2.1[j]! < acc.1.processed
  descending : ∀ i j, i < j → j < acc.2.1.size → c.rank acc.2.1[j]! < c.rank acc.2.1[i]!
  cursor : acc.1.processed = c.candidate ∨ c.source.reason c.source.trail[acc.1.processed]! = 0

private theorem cursor_markFrame {c : CursorContext} {offset : Nat} {acc : LearnedAcc}
    (inv : CursorInvariant c offset acc) (next : State) (frame : MarkFrame acc.1 next)
    (lbd : Nat) (used : Bool) : CursorInvariant c offset (next, acc.2.1, lbd, used) := by
  have processed : next.processed = acc.1.processed := by
    simpa only using congrArg State.processed frame.restore
  exact ⟨inv.frame.trans (.ofMarkFrame frame), by simpa only [processed] using inv.lower,
    by simpa only [processed] using inv.upper, by simpa only [processed] using inv.frontier,
    inv.size, inv.positions, by simpa only [processed] using inv.tails, inv.descending,
    by simpa only [processed] using inv.cursor⟩

private theorem cursor_advance {c : CursorContext} {offset : Nat} {acc : LearnedAcc}
    (inv : CursorInvariant c offset acc) : CursorInvariant c (offset + 1) acc := by
  refine ⟨inv.frame, inv.lower, inv.upper, Or.inl ?_, by have := inv.size; omega,
    ?_, inv.tails, inv.descending, inv.cursor⟩
  · rcases inv.frontier with bound | ⟨zero, cursor⟩ <;> omega
  · intro j before
    obtain ⟨lower, upper, read, visited⟩ := inv.positions j before
    exact ⟨lower, upper, read, by omega⟩

private theorem cursor_push {c : CursorContext} {offset : Nat} {acc : LearnedAcc}
    (inv : CursorInvariant c offset acc) (bound : offset < c.candidate + 1 - c.source.forced) :
    CursorInvariant c (offset + 1)
      (acc.1, acc.2.1.push acc.1.trail[c.candidate - offset]!, acc.2.2.1, true) := by
  let p := c.candidate - offset
  have before : offset ≤ c.candidate := by omega
  have rank : c.rank acc.1.trail[p]! = p := by rw [inv.frame.trail]; exact c.ranked p (by omega)
  have read : c.source.trail[p]! = acc.1.trail[p]! := by rw [inv.frame.trail]
  have oldRead (j : Nat) (jBound : j < acc.2.1.size) :
      (acc.2.1.push acc.1.trail[p]!)[j]! = acc.2.1[j]! := by
    simp [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_push,
      Nat.ne_of_lt jBound]
  have lastRead : (acc.2.1.push acc.1.trail[p]!)[acc.2.1.size]! = acc.1.trail[p]! := by simp
  constructor
  · exact inv.frame
  · exact inv.lower
  · exact inv.upper
  · apply Or.inl
    change c.candidate < acc.1.processed + (offset + 1)
    rcases inv.frontier with bound | ⟨zero, cursor⟩ <;> omega
  · simp only [Array.size_push]
    have := inv.size
    omega
  · intro j within
    have within' : j < acc.2.1.size + 1 := by simpa only [Array.size_push] using within
    by_cases last : j = acc.2.1.size
    · subst j
      rw [lastRead, rank]
      exact ⟨by dsimp [p]; omega, by dsimp [p]; omega, read, by dsimp [p]; omega⟩
    · have earlier : j < acc.2.1.size := by omega
      rw [oldRead j earlier]
      obtain ⟨lower, upper, read, visited⟩ := inv.positions j earlier
      exact ⟨lower, upper, read, by omega⟩
  · intro j positive within
    have within' : j < acc.2.1.size + 1 := by simpa only [Array.size_push] using within
    by_cases last : j = acc.2.1.size
    · subst j
      rw [lastRead, rank]
      have hasOld : 0 < offset := by have := inv.size; omega
      rcases inv.frontier with frontier | ⟨zero, _⟩ <;> dsimp [p] <;> omega
    · have earlier : j < acc.2.1.size := by omega
      rw [oldRead j earlier]
      exact inv.tails j positive earlier
  · intro i j order within
    have within' : j < acc.2.1.size + 1 := by simpa only [Array.size_push] using within
    have beforeI : i < acc.2.1.size := by omega
    rw [oldRead i beforeI]
    by_cases last : j = acc.2.1.size
    · subst j
      rw [lastRead, rank]
      have visited := (inv.positions i beforeI).2.2.2
      dsimp [p]
      omega
    · have earlier : j < acc.2.1.size := by omega
      rw [oldRead j earlier]
      exact inv.descending i j order earlier
  · exact inv.cursor

private theorem cursor_setProcessed {c : CursorContext} {offset : Nat} {acc : LearnedAcc}
    (inv : CursorInvariant c (offset + 1) acc) (bound : offset < c.candidate + 1 - c.source.forced)
    (single : acc.2.1.size = 1)
    (decision : acc.1.reason acc.1.trail[c.candidate - offset]! = 0) :
    CursorInvariant c (offset + 1)
      ({ acc.1 with processed := c.candidate - offset }, acc.2.1, acc.2.2) := by
  have reason : c.source.reason c.source.trail[c.candidate - offset]! = 0 := by
    have reasons : acc.1.reasons = c.source.reasons := by
      simpa only using congrArg State.reasons inv.frame.restore
    simpa only [State.reason, inv.frame.trail, reasons] using decision
  refine ⟨inv.frame.trans ⟨rfl, rfl⟩, by dsimp; omega, by dsimp; omega,
    Or.inl (by dsimp; omega), inv.size, inv.positions, ?_, inv.descending, Or.inr reason⟩
  intro j positive within
  change j < acc.2.1.size at within
  omega

private theorem cursor_finish {c : CursorContext} {offset : Nat} {acc : LearnedAcc}
    (inv : CursorInvariant c (offset + 1) acc) (bound : offset < c.candidate + 1 - c.source.forced) :
    CursorInvariant c (offset + 1)
      (finishBody (c.candidate - offset) acc.1.trail[c.candidate - offset]!
        acc.1 acc.2.1 acc.2.2.1 acc.2.2.2).value := by
  simp only [finishBody, Id.run, pure]
  split
  · rename_i decision
    have decision' : acc.1.reason acc.1.trail[c.candidate - offset]! = 0 := by simpa using decision
    split <;> split <;> repeat first
      | rename_i single
        have single' : acc.2.1.size = 1 := by simpa using single
        exact cursor_markFrame (cursor_setProcessed inv bound single' decision') _
          (markFrame_setMark _ _ 1) _ _
      | exact cursor_markFrame inv _ (markFrame_setMark _ _ 1) _ _
  · exact cursor_markFrame inv _ (markFrame_setMark _ _ 1) _ _

private theorem cursor_step {c : CursorContext} {offset : Nat} {acc : LearnedAcc}
    (inv : CursorInvariant c offset acc) (bound : offset < c.candidate + 1 - c.source.forced) :
    CursorInvariant c (offset + 1) (learnedBody c.candidate offset acc).value := by
  rw [learnedBody_eq]
  dsimp only
  split
  · let result := implied (acc.1.nVars + 1) acc.1 acc.1.trail[c.candidate - offset]!
    have frame : MarkFrame acc.1 result.1 := implied_markFrame _ _ _
    have next := cursor_markFrame inv result.1 frame acc.2.2.1 acc.2.2.2
    have read : result.1.trail = acc.1.trail := frame.trail
    split
    · have appended := cursor_push next bound
      rw [read] at appended
      simpa only [read, result] using cursor_finish appended bound
    · have advanced := cursor_advance next
      simpa only [read, result] using cursor_finish advanced bound
  · exact cursor_finish (cursor_advance inv) bound

private theorem cursor_loop (c : CursorContext) (fuel start : Nat)
    (bound : start + fuel ≤ c.candidate + 1 - c.source.forced) (acc : LearnedAcc)
    (inv : CursorInvariant c start acc) :
    CursorInvariant c (start + fuel)
      (forIn (m := Id) (List.range' start fuel) acc (learnedBody c.candidate)) := by
  induction fuel generalizing start acc with
  | zero => simpa only [List.range'_zero, List.forIn_nil, pure, Nat.add_zero] using inv
  | succ fuel ih =>
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨next, execute⟩ := learnedBody_yields c.candidate start acc
    have step := cursor_step inv (by omega)
    rw [execute]
    simp only [bind]
    have nextInv : CursorInvariant c (start + 1) next := by
      simpa only [execute, ForInStep.value_yield] using step
    have final := ih (start + 1) (by omega) next nextInv
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using final

/-- The actual processed cursor stays between the forced prefix and candidate.
Every learned tail lies strictly below it, while the returned clause is ordered
by decreasing original trail position. Any changed cursor names a decision. -/
theorem buildLearned_cursor (s : State) (candidate : Nat) (rank : Lit → Nat)
    (lower : s.forced ≤ candidate) (ranked : ∀ i, i ≤ candidate → rank s.trail[i]! = i) :
    let built := buildLearned s candidate
    s.forced ≤ built.1.processed ∧ built.1.processed ≤ candidate ∧
      (∀ j, j < built.2.1.size → s.forced ≤ rank built.2.1[j]! ∧
        rank built.2.1[j]! ≤ candidate ∧ s.trail[rank built.2.1[j]!]! = built.2.1[j]!) ∧
      (∀ j, 0 < j → j < built.2.1.size → rank built.2.1[j]! < built.1.processed) ∧
      (∀ i j, i < j → j < built.2.1.size → rank built.2.1[j]! < rank built.2.1[i]!) ∧
      (built.1.processed = candidate ∨ s.reason s.trail[built.1.processed]! = 0) := by
  let c : CursorContext := ⟨s, candidate, rank, lower, ranked⟩
  have initial : CursorInvariant c 0 ({ s with processed := candidate }, #[], 0, false) := by
    refine ⟨⟨rfl, rfl⟩, lower, Nat.le_refl _, Or.inr ⟨rfl, rfl⟩, by simp, ?_, ?_, ?_, Or.inl rfl⟩ <;>
      intros <;> simp_all
  have loop := cursor_loop c (candidate + 1 - s.forced) 0 (by dsimp [c]; omega) _ initial
  rw [buildLearned_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at *
  exact ⟨loop.lower, loop.upper, fun j before => (loop.positions j before).imp_right
    (fun h => ⟨h.1, h.2.1⟩), loop.tails, loop.descending, loop.cursor⟩

private def LearnedHead (lit : Lit) (learned : Array Lit) : Prop :=
  0 < learned.size ∧ learned[0]! = lit

private theorem learnedHead_push {lit : Lit} {learned : Array Lit} (head : LearnedHead lit learned)
    (appended : Lit) : LearnedHead lit (learned.push appended) := by
  constructor
  · simp only [Array.size_push]
    omega
  · have old : (learned.push appended)[0]! = learned[0]! := by
      have within : 0 < (learned.push appended).size := by simp
      have oldWithin : 0 < learned.size := head.1
      calc
        (learned.push appended)[0]! = (learned.push appended)[0] := getElem!_pos _ 0 within
        _ = learned[0] := Array.getElem_push_lt head.1
        _ = learned[0]! := (getElem!_pos learned 0 head.1).symm
    exact old.trans head.2

private theorem finishBody_head {lit : Lit} {s : State} {learned : Array Lit} {lbd : Nat}
    {used : Bool} (head : LearnedHead lit learned) (p target : Nat) :
    LearnedHead lit (finishBody p target s learned lbd used).value.2.1 := by
  simp only [finishBody, Id.run, pure]
  split <;> repeat first | split | exact head

private theorem learnedBody_head {lit : Lit} {acc : LearnedAcc} (head : LearnedHead lit acc.2.1)
    (candidate offset : Nat) : LearnedHead lit (learnedBody candidate offset acc).value.2.1 := by
  rw [learnedBody_eq]
  dsimp only
  split
  · split
    · exact finishBody_head (learnedHead_push head _) _ _
    · exact finishBody_head head _ _
  · exact finishBody_head head _ _

private theorem learned_loop_head {lit : Lit} (candidate fuel start : Nat) (acc : LearnedAcc)
    (head : LearnedHead lit acc.2.1) :
    LearnedHead lit (forIn (m := Id) (List.range' start fuel) acc (learnedBody candidate)).2.1 := by
  induction fuel generalizing start acc with
  | zero => simpa only [List.range'_zero, List.forIn_nil, pure] using head
  | succ fuel ih =>
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨next, execute⟩ := learnedBody_yields candidate start acc
    have nextHead := learnedBody_head head candidate start
    rw [execute]
    simp only [bind]
    apply ih (start + 1) next
    simpa only [execute, ForInStep.value_yield] using nextHead

/-- If the first actual minimizer call fails, the candidate is appended first
and every later loop iteration preserves that head. The query state includes
the executable reset of `processed` performed before the loop. -/
theorem buildLearned_head_of_implied_false (s : State) (candidate : Nat)
    (lower : s.forced ≤ candidate) (marked : s.mark s.trail[candidate]! = 2)
    (failed : (implied (s.nVars + 1) { s with processed := candidate } s.trail[candidate]!).2 = false) :
    0 < (buildLearned s candidate).2.1.size ∧
      (buildLearned s candidate).2.1[0]! = s.trail[candidate]! := by
  let initial : LearnedAcc := ({ s with processed := candidate }, #[], 0, false)
  obtain ⟨next, execute⟩ := learnedBody_yields candidate 0 initial
  have firstHead : LearnedHead s.trail[candidate]! next.2.1 := by
    have first : LearnedHead s.trail[candidate]! (learnedBody candidate 0 initial).value.2.1 := by
      rw [learnedBody_eq]
      simp only [initial, Nat.sub_zero]
      simp only [State.mark] at marked
      simp only [State.mark, marked, beq_self_eq_true, Bool.not_false, failed, ite_true]
      apply finishBody_head
      exact ⟨by simp, by simp⟩
    simpa only [execute, ForInStep.value_yield] using first
  have count : candidate + 1 - s.forced = (candidate - s.forced) + 1 := by omega
  have finalHead := learned_loop_head candidate (candidate - s.forced) 1 next firstHead
  rw [buildLearned_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  rw [count, List.range'_succ, List.forIn_cons, execute]
  exact finalHead

/-- Every actual learned tail still names a position in the real retained
trail after backjump, independently of the minimizer's return decisions. -/
theorem buildLearned_backjump_tails (s : State) (candidate : Nat) (rank : Lit → Nat)
    (lower : s.forced ≤ candidate) (ranked : ∀ i, i ≤ candidate → rank s.trail[i]! = i) :
    let built := buildLearned s candidate
    ∀ j, 0 < j → j < built.2.1.size →
      TrailMember (backjump built.1 candidate) (backjump built.1 candidate).assigned built.2.1[j]! := by
  intro built j positive within
  have cursor := buildLearned_cursor s candidate rank lower ranked
  have position := cursor.2.2.1 j within
  refine ⟨rank built.2.1[j]!, ?_, ?_⟩
  · rw [backjump_assigned]
    exact cursor.2.2.2.1 j positive within
  · rw [backjump_trail, (buildLearned_frame s candidate).trail]
    exact position.2.2

/-- If the candidate is the learned head, its variable is absent from the
actual retained prefix; this is freshness for the later asserting assignment. -/
theorem buildLearned_backjump_head_fresh (s : State) (candidate : Nat) (rank : Lit → Nat)
    (lower : s.forced ≤ candidate) (ranked : ∀ i, i ≤ candidate → rank s.trail[i]! = i)
    (distinct : DistinctTrailVariables { s with assigned := candidate + 1 })
    (head : (buildLearned s candidate).2.1[0]! = s.trail[candidate]!) :
    FreshVariable (backjump (buildLearned s candidate).1 candidate)
      (buildLearned s candidate).2.1[0]!.var := by
  intro i before same
  rw [backjump_assigned] at before
  have upper := (buildLearned_cursor s candidate rank lower ranked).2.1
  have beforeCandidate : i < candidate := by omega
  have same' : s.trail[i]!.var = s.trail[candidate]!.var := by
    simpa only [backjump_trail, (buildLearned_frame s candidate).trail, head] using same
  have equal := distinct i candidate (by dsimp; omega) (by dsimp; omega) same'
  omega

private structure LearnedMarkSupport (allowed : Lit → Prop) (source current : State) : Prop where
  frame : LearnedFrame source current
  outside : ∀ lit, ¬ allowed lit → current.mark lit = source.mark lit
  nonzero : ∀ lit, source.mark lit ≠ 0 → current.mark lit ≠ 0

private theorem LearnedMarkSupport.markSupport {allowed : Lit → Prop} {source current next : State}
    (facts : LearnedMarkSupport allowed source current) (support : MarkSupport allowed current next) :
    LearnedMarkSupport allowed source next :=
  ⟨facts.frame.trans (.ofMarkFrame support.frame), fun lit outside =>
    (support.outside lit outside).trans (facts.outside lit outside),
    fun lit marked => support.nonzero lit (facts.nonzero lit marked)⟩

private theorem LearnedMarkSupport.setProcessed {allowed : Lit → Prop} {source current : State}
    (facts : LearnedMarkSupport allowed source current) (p : Nat) :
    LearnedMarkSupport allowed source { current with processed := p } :=
  ⟨facts.frame.trans ⟨rfl, rfl⟩, facts.outside, facts.nonzero⟩

private theorem learned_support_finish {allowed : Lit → Prop} {source current : State}
    (facts : LearnedMarkSupport allowed source current) (p target : Nat)
    (member : allowed target) (learned : Array Lit) (lbd : Nat) (used : Bool) :
    LearnedMarkSupport allowed source (finishBody p target current learned lbd used).value.1 := by
  simp only [finishBody, Id.run, pure]
  split <;> repeat first
    | split
    | exact facts.markSupport (markSupport_setMark _ _ 1 member (by decide))
    | exact (facts.setProcessed p).markSupport (markSupport_setMark _ _ 1 member (by decide))

private theorem learned_support_step {formula : Std.Sat.CNF Nat} {snapshot source : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (storage : ReasonStorage snapshot source) (trail : source.trail = snapshot.trail)
    (candidate offset : Nat) (candidateBound : candidate < count)
    (acc : LearnedAcc)
    (facts : LearnedMarkSupport (TrailMember snapshot count) source acc.1) :
    LearnedMarkSupport (TrailMember snapshot count) source (learnedBody candidate offset acc).value.1 := by
  have stateStorage : ReasonStorage snapshot acc.1 := by
    have arena : acc.1.arena = source.arena := by
      simpa only using congrArg State.arena facts.frame.restore
    have reasons : acc.1.reasons = source.reasons := by
      simpa only using congrArg State.reasons facts.frame.restore
    exact ⟨arena.trans storage.arena, reasons.trans storage.reasons⟩
  have member : TrailMember snapshot count acc.1.trail[candidate - offset]! := by
    refine ⟨candidate - offset, by omega, ?_⟩
    rw [facts.frame.trail, trail]
  rw [learnedBody_eq]
  dsimp only
  split
  · have recursive := implied_markSupport graph (acc.1.nVars + 1) acc.1
      acc.1.trail[candidate - offset]! stateStorage member
    have next := facts.markSupport recursive
    split <;> exact learned_support_finish next _ _ member _ _ _
  · exact learned_support_finish facts _ _ member _ _ _

private theorem learned_support_loop {formula : Std.Sat.CNF Nat} {snapshot source : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (storage : ReasonStorage snapshot source) (trail : source.trail = snapshot.trail)
    (candidate : Nat) (candidateBound : candidate < count) (fuel start : Nat)
    (bound : start + fuel ≤ candidate + 1 - source.forced) (acc : LearnedAcc)
    (facts : LearnedMarkSupport (TrailMember snapshot count) source acc.1) :
    LearnedMarkSupport (TrailMember snapshot count) source
      (forIn (m := Id) (List.range' start fuel) acc (learnedBody candidate)).1 := by
  induction fuel generalizing start acc with
  | zero => simpa only [List.range'_zero, List.forIn_nil, pure] using facts
  | succ fuel ih =>
    rw [List.range'_succ, List.forIn_cons]
    obtain ⟨next, execute⟩ := learnedBody_yields candidate start acc
    have step := learned_support_step graph storage trail candidate start candidateBound acc facts
    rw [execute]
    simp only [bind]
    apply ih (start + 1) (by omega) next
    simpa only [execute, ForInStep.value_yield] using step

/-- Actual learned construction never clears a nonzero mark, and changes no
literal outside the concrete reason snapshot. Cursor changes are immaterial. -/
theorem buildLearned_markSupport {formula : Std.Sat.CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (candidate : Nat) (candidateBound : candidate < count) :
    (∀ lit, ¬ TrailMember snapshot count lit → (buildLearned s candidate).1.mark lit = s.mark lit) ∧
      (∀ lit, s.mark lit ≠ 0 → (buildLearned s candidate).1.mark lit ≠ 0) := by
  have initial : LearnedMarkSupport (TrailMember snapshot count) s { s with processed := candidate } :=
    ⟨⟨rfl, rfl⟩, fun _ _ => rfl, fun _ marked => marked⟩
  have result := learned_support_loop graph storage trail candidate candidateBound
    (candidate + 1 - s.forced) 0 (by omega) ({ s with processed := candidate }, #[], 0, false) initial
  rw [buildLearned_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at *
  exact ⟨result.outside, result.nonzero⟩

/-- The actual minimizer keeps the candidate-inclusive false trail consistent:
all false tags stay nonzero and their opposite literals are outside its writes. -/
theorem buildLearned_activeTrail {formula : Std.Sat.CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (candidate : Nat) (candidateBound : candidate < count)
    (active : ActiveTrail { s with assigned := candidate + 1 }) :
    ActiveTrail { (buildLearned s candidate).1 with assigned := candidate + 1 } := by
  have support := buildLearned_markSupport graph storage trail candidate candidateBound
  have frame := buildLearned_frame s candidate
  intro i before
  have within : i < candidate + 1 := before
  have beforeCount : i < count := by omega
  have old := active i within
  rw [frame.trail]
  constructor
  · simpa only [frame.nVars] using old.1
  · constructor
    · exact support.2 _ old.2.1
    · have outside : ¬ TrailMember snapshot count s.trail[i]!.negate := by
        rintro ⟨j, beforeJ, equal⟩
        have sameVariable : snapshot.trail[j]!.var = snapshot.trail[i]!.var := by
          simpa only [negate_var, trail] using congrArg Lit.var equal
        have same := graph.distinctVariables j i beforeJ beforeCount sameVariable
        subst j
        have impossible : s.trail[i]! = s.trail[i]!.negate := by simpa only [trail] using equal
        exact negate_ne s.trail[i]! impossible.symm
      exact (support.1 _ outside).trans old.2.2

/-- With the retained UIP identified, the real backjump clears both head
polarities, retains every tail as a false active literal, and frees the head's
variable for the next actual asserting assignment. -/
theorem buildLearned_backjump_asserting {formula : Std.Sat.CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (storage : ReasonStorage snapshot s) (trail : s.trail = snapshot.trail)
    (candidate : Nat) (candidateBound : candidate < count) (lower : s.forced ≤ candidate)
    (arrays : ArrayBounds s) (active : ActiveTrail { s with assigned := candidate + 1 })
    (head : (buildLearned s candidate).2.1[0]! = s.trail[candidate]!) :
    let built := buildLearned s candidate
    let jumped := backjump built.1 candidate
    FreshVariable jumped built.2.1[0]!.var ∧ jumped.mark built.2.1[0]! = 0 ∧
      jumped.mark built.2.1[0]!.negate = 0 ∧
      ∀ j, 0 < j → j < built.2.1.size → TrailMember jumped jumped.assigned built.2.1[j]! ∧
        FalseAssignment jumped built.2.1[j]! := by
  have ranked : ∀ i, i ≤ candidate → rank s.trail[i]! = i := by
    intro i before
    rw [trail]
    exact graph.ranks i (by omega)
  have distinct : DistinctTrailVariables { s with assigned := candidate + 1 } := by
    intro i j beforeI beforeJ same
    apply graph.distinctVariables i j (by dsimp at beforeI; omega) (by dsimp at beforeJ; omega)
    simpa only [trail] using same
  have frame := buildLearned_frame s candidate
  have builtActive := buildLearned_activeTrail graph storage trail candidate candidateBound active
  have builtDistinct : DistinctTrailVariables
      { (buildLearned s candidate).1 with assigned := candidate + 1 } := by
    simpa only [DistinctTrailVariables, frame.trail] using distinct
  have cursor := buildLearned_cursor s candidate rank lower ranked
  have afterActive := backjump_activeTrail builtActive builtDistinct (by have := cursor.2.1; omega)
  refine ⟨buildLearned_backjump_head_fresh s candidate rank lower ranked distinct head, ?_, ?_, ?_⟩
  · rw [head, ← frame.trail]
    exact backjump_mark_cleared (frame.arrayBounds arrays) builtActive candidate cursor.2.1 (Nat.le_refl _)
  · rw [head, ← frame.trail]
    exact backjump_mark_unmarked (builtActive candidate (by dsimp; omega)).2.2
  · intro j positive within
    have member := buildLearned_backjump_tails s candidate rank lower ranked j positive within
    refine ⟨member, ?_⟩
    obtain ⟨i, before, equal⟩ := member
    exact equal ▸ (afterActive i before).2

theorem buildLearned_nodup (s : State) (candidate : Nat) (rank : Lit → Nat)
    (lower : s.forced ≤ candidate) (ranked : ∀ i, i ≤ candidate → rank s.trail[i]! = i) :
    (buildLearned s candidate).2.1.toList.Nodup := by
  apply List.nodup_iff_eq_of_getElem_eq.mpr
  intro i j beforeI beforeJ same
  have boundI : i < (buildLearned s candidate).2.1.size := by simpa only [Array.length_toList] using beforeI
  have boundJ : j < (buildLearned s candidate).2.1.size := by simpa only [Array.length_toList] using beforeJ
  have literalSame : (buildLearned s candidate).2.1[i]! = (buildLearned s candidate).2.1[j]! := by
    simpa only [Array.getElem_toList, getElem!_pos (buildLearned s candidate).2.1 i boundI,
      getElem!_pos (buildLearned s candidate).2.1 j boundJ] using same
  have ranks := congrArg rank literalSame
  have descending := (buildLearned_cursor s candidate rank lower ranked).2.2.2.2.1
  by_cases before : i < j
  · have := descending i j before boundJ
    omega
  · by_cases after : j < i
    · have := descending j i after boundI
      omega
    · omega

end MicrosatLean.Verification.Implementation.Analysis
