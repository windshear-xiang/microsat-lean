import MicrosatLean.Faithful.Microsat

/-!
# Termination of `solve`'s main loop, in general

`run` is defined by `partial_fixpoint`, so its definition alone says nothing about
termination. `RunsTo` is the inductive meaning of "the loop finishes after finitely
many `step`s", and `runsTo_of_rank` is the generic well-founded argument that
`Main.lean` instantiates with the solver's invariant and rank.
-/

namespace MicrosatLean.Faithful.Verification

/-- `RunsTo S d out`: from loop state `(S, d)`, finitely many `step`s reach
`finished`, and `out` is the final state and result. -/
inductive RunsTo : solver → CInt → solver × CInt → Prop
  | finished {S d S' r} : step S d = .finished S' r → RunsTo S d (S', r)
  | running {S d S' d' out} : step S d = .running S' d' → RunsTo S' d' out → RunsTo S d out

/-- A finishing loop computes `run`'s value. Used to turn `RunsTo` into facts
about `solve`; uses only `run`'s unfolding equation. -/
theorem RunsTo.run_eq {S : solver} {d : CInt} {out : solver × CInt} (h : RunsTo S d out) :
    run S d = out := by
  induction h with
  | finished hs => rw [run, hs]
  | running hs _ ih => rw [run, hs]; exact ih

/-- Generic termination with a postcondition: an invariant preserved by every
non-final step, a well-founded rank that every non-final step decreases, and a
postcondition established by every final step give a finishing run that meets the
postcondition. Used by `Main.lean` with the contracts of `Step.lean`. -/
theorem runsTo_of_rank {α : Type} {lt : α → α → Prop} (wf : WellFounded lt)
    (Inv : solver → CInt → Prop) (rank : solver → CInt → α) (Post : solver × CInt → Prop)
    (preserve : ∀ {S d S' d'}, Inv S d → step S d = .running S' d' → Inv S' d')
    (decrease : ∀ {S d S' d'}, Inv S d → step S d = .running S' d' → lt (rank S' d') (rank S d))
    (finish : ∀ {S d S' r}, Inv S d → step S d = .finished S' r → Post (S', r)) :
    ∀ S d, Inv S d → ∃ out, RunsTo S d out ∧ Post out := by
  suffices key : ∀ x S d, rank S d = x → Inv S d → ∃ out, RunsTo S d out ∧ Post out from
    fun S d => key _ S d rfl
  intro x
  refine wf.induction (C := fun x => ∀ S d, rank S d = x → Inv S d → ∃ out, RunsTo S d out ∧ Post out) x ?_
  intro x ih S d hx inv
  match hs : step S d with
  | .finished S' r => exact ⟨(S', r), .finished hs, finish inv hs⟩
  | .running S' d' =>
    obtain ⟨out, hrun, hpost⟩ := ih _ (hx ▸ decrease inv hs) S' d' rfl (preserve inv hs)
    exact ⟨out, .running hs hrun, hpost⟩

end MicrosatLean.Faithful.Verification
