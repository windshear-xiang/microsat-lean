import MicrosatLean.Verification.Representation.State

namespace MicrosatLean.Verification.Reduction

open CDCL Representation

/-- Filtering learned watches changes only arena links and watch heads, while
preserving the dimensions of both arrays even on malformed states. -/
structure WatchFilterFrame (before after : State) : Prop where
  restore : { after with arena := before.arena, first := before.first } = before
  arenaSize : after.arena.size = before.arena.size
  firstSize : after.first.size = before.first.size

theorem WatchFilterFrame.refl (s : State) : WatchFilterFrame s s := ⟨rfl, rfl, rfl⟩

theorem WatchFilterFrame.trans {first middle last : State}
    (before : WatchFilterFrame first middle) (after : WatchFilterFrame middle last) :
    WatchFilterFrame first last := by
  constructor
  · exact (congrArg (fun s : State => { s with arena := first.arena, first := first.first })
      after.restore).trans before.restore
  · exact after.arenaSize.trans before.arenaSize
  · exact after.firstSize.trans before.firstSize

abbrev WatchFilterAcc := State × Nat × Option Nat

def watchFilterBody (lit : Lit) (_ : Nat) (acc : WatchFilterAcc) :
    Id (ForInStep WatchFilterAcc) := Id.run do
  let mut s := acc.1
  let ref := acc.2.1
  let mut previousLink := acc.2.2
  if ref == 0 then return .done acc
  let linkPos := watchLinkPos ref
  let nextRef := s.db linkPos
  if watchClause ref < s.fixed then
    previousLink := some linkPos
  else
    match previousLink with
    | none => s := { s with first := s.first.set! lit nextRef }
    | some pos => s := { s with arena := s.arena.set! pos nextRef }
  return .yield (s, nextRef, previousLink)

def watchFilterList (lit : Lit) (s : State) : Id (ForInStep State) :=
  let result := forIn (m := Id) [:s.arena.size] (s, s.first[lit]!, none) (watchFilterBody lit)
  .yield result.1

theorem removeLearnedWatches_eq_loop (s : State) :
    s.removeLearnedWatches = forIn (m := Id) [2:s.first.size] s watchFilterList := by
  rfl

private theorem filterBody_frame (lit index : Nat) (acc : WatchFilterAcc) :
    WatchFilterFrame acc.1 (watchFilterBody lit index acc).value.1 := by
  simp only [watchFilterBody, Id.run, pure]
  split
  · exact .refl _
  · split
    · exact .refl _
    · split <;> constructor <;> first | rfl | simp

private theorem list_frame {β : Type} (state : β → State) (xs : List Nat)
    (body : Nat → β → Id (ForInStep β))
    (step : ∀ index acc, WatchFilterFrame (state acc) (state (body index acc).value))
    (initial : β) : WatchFilterFrame (state initial) (state (forIn (m := Id) xs initial body)) := by
  induction xs generalizing initial with
  | nil => exact .refl _
  | cons head tail ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    have frame := step head initial
    cases result : body head initial with
    | done next => simpa only [result, ForInStep.value_done] using frame
    | yield next =>
      have nextFrame : WatchFilterFrame (state initial) (state next) := by
        simpa only [result, ForInStep.value_yield] using frame
      exact nextFrame.trans (ih next)

private theorem filterList_frame (lit : Nat) (s : State) :
    WatchFilterFrame s (watchFilterList lit s).value := by
  simp only [watchFilterList, ForInStep.value_yield]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact list_frame Prod.fst _ _ (filterBody_frame lit) (s, s.first[lit]!, none)

theorem removeLearnedWatches_frame (s : State) : WatchFilterFrame s s.removeLearnedWatches := by
  rw [removeLearnedWatches_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  exact list_frame id _ _ filterList_frame s

theorem WatchFilterFrame.arrayBounds {before after : State} (frame : WatchFilterFrame before after)
    (arrays : ArrayBounds before) : ArrayBounds after := by
  have old : ArrayBounds { after with arena := before.arena, first := before.first } := by
    rw [frame.restore]
    exact arrays
  exact ⟨frame.firstSize.trans old.firstSize, old.marksSize, old.reasonsSize, old.phasesSize,
    old.trailSize, old.previousSize, old.nextSize⟩

end MicrosatLean.Verification.Reduction
