import MicrosatLean.Verification.Analysis.Learned

namespace MicrosatLean.Verification.Analysis

open CDCL Representation

/-- Learned-clause construction changes only mark values and the backjump
cursor. This frame holds for every executable state, without reason invariants. -/
structure LearnedFrame (before after : State) : Prop where
  restore : { after with marks := before.marks, processed := before.processed } = before
  marksSize : after.marks.size = before.marks.size

theorem LearnedFrame.refl (s : State) : LearnedFrame s s := ⟨rfl, rfl⟩

theorem LearnedFrame.trans {first middle last : State}
    (before : LearnedFrame first middle) (after : LearnedFrame middle last) :
    LearnedFrame first last := by
  constructor
  · have h := congrArg (fun s : State =>
        { s with marks := first.marks, processed := first.processed }) after.restore
    exact h.trans before.restore
  · exact after.marksSize.trans before.marksSize

theorem LearnedFrame.ofMarkFrame {before after : State} (h : MarkFrame before after) :
    LearnedFrame before after := by
  constructor
  · exact congrArg (fun s : State => { s with processed := before.processed }) h.restore
  · exact h.marksSize

private theorem learnedFrame_setProcessed (s : State) (p : Nat) :
    LearnedFrame s { s with processed := p } := ⟨rfl, rfl⟩

private theorem learnedFrame_setMark (s : State) (lit value : Nat) :
    LearnedFrame s (s.setMark lit value) := .ofMarkFrame (markFrame_setMark s lit value)

theorem learnedBody_frame (candidate offset : Nat) (acc : LearnedAcc) :
    LearnedFrame acc.1 (learnedBody candidate offset acc).value.1 := by
  simp only [learnedBody, Id.run, pure]
  split
  · have frame := LearnedFrame.ofMarkFrame
      (implied_markFrame (acc.1.nVars + 1) acc.1 acc.1.trail[candidate - offset]!)
    split <;> split <;> repeat first
      | split
      | exact frame.trans (learnedFrame_setMark _ _ 1)
      | exact (frame.trans (learnedFrame_setProcessed _ _)).trans (learnedFrame_setMark _ _ 1)
  · split <;> repeat first
      | split
      | exact learnedFrame_setMark _ _ 1
      | exact (learnedFrame_setProcessed _ _).trans (learnedFrame_setMark _ _ 1)

private theorem list_frame (candidate : Nat) (xs : List Nat) (acc : LearnedAcc) :
    LearnedFrame acc.1 (forIn (m := Id) xs acc (learnedBody candidate)).1 := by
  induction xs generalizing acc with
  | nil => exact .refl acc.1
  | cons head tail ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    have step := learnedBody_frame candidate head acc
    cases body : learnedBody candidate head acc with
    | done next => simpa only [body, ForInStep.value_done] using step
    | yield next =>
      have frame : LearnedFrame acc.1 next.1 := by
        simpa only [body, ForInStep.value_yield] using step
      exact frame.trans (ih next)

theorem buildLearned_frame (s : State) (candidate : Nat) :
    LearnedFrame s (buildLearned s candidate).1 := by
  rw [buildLearned_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only
  exact (learnedFrame_setProcessed s candidate).trans
    (list_frame candidate (List.range' 0 [:candidate + 1 - s.forced].size)
      ({ s with processed := candidate }, #[], 0, false))

theorem LearnedFrame.nVars {before after : State} (frame : LearnedFrame before after) :
    after.nVars = before.nVars := by simpa only using congrArg State.nVars frame.restore

theorem LearnedFrame.nLemmas {before after : State} (frame : LearnedFrame before after) :
    after.nLemmas = before.nLemmas := by simpa only using congrArg State.nLemmas frame.restore

theorem LearnedFrame.maxLemmas {before after : State} (frame : LearnedFrame before after) :
    after.maxLemmas = before.maxLemmas := by simpa only using congrArg State.maxLemmas frame.restore

theorem LearnedFrame.assigned {before after : State} (frame : LearnedFrame before after) :
    after.assigned = before.assigned := by simpa only using congrArg State.assigned frame.restore

theorem LearnedFrame.forced {before after : State} (frame : LearnedFrame before after) :
    after.forced = before.forced := by simpa only using congrArg State.forced frame.restore

theorem LearnedFrame.trail {before after : State} (frame : LearnedFrame before after) :
    after.trail = before.trail := by simpa only using congrArg State.trail frame.restore

theorem LearnedFrame.arrayBounds {before after : State} (frame : LearnedFrame before after)
    (arrays : ArrayBounds before) : ArrayBounds after := by
  have old : ArrayBounds { after with marks := before.marks, processed := before.processed } := by
    rw [frame.restore]
    exact arrays
  exact ⟨old.firstSize, frame.marksSize.trans old.marksSize, old.reasonsSize, old.phasesSize,
    old.trailSize, old.previousSize, old.nextSize⟩

end MicrosatLean.Verification.Analysis
