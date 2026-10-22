import MicrosatLean.CDCL.Search

namespace MicrosatLean.Verification.Search

open CDCL

/-!
Execution lemmas for the actual `CDCL.step` and `CDCL.runFor`. Their preservation
and rank hypotheses are proof obligations, not assertions that the current
solver already satisfies an invariant or a global termination measure.
-/

/-- A running machine retains its invariant; a finished result has the desired
semantic property. The result predicate can mention the original input formula. -/
def ValidProgress (invariant : Machine → Prop) (correct : SolveResult → Prop) :
    Progress → Prop
  | .running machine => invariant machine
  | .finished result => correct result

/-- Running transitions reachable from the actual initial machine. Finished
results have no outgoing transition in this relation. -/
inductive RunningReachable (initial : Machine) : Machine → Prop where
  | initial : RunningReachable initial initial
  | advance {before after : Machine} :
      RunningReachable initial before → step before = .running after →
      RunningReachable initial after

/-- Splitting the real runner's fuel preserves both resumptions and early
termination. This equation does not assume that either execution finishes. -/
theorem runFor_add (first second : Nat) (machine : Machine) :
    runFor (first + second) machine =
      match runFor first machine with
      | .running next => runFor second next
      | .finished result => .finished result := by
  induction first generalizing machine with
  | zero => simp [runFor]
  | succ first ih =>
    cases hStep : step machine with
    | running next => simpa [Nat.succ_add, runFor, hStep] using ih next
    | finished result => simp [Nat.succ_add, runFor, hStep]

theorem runFor_finished_add {fuel : Nat} {machine : Machine} {result : SolveResult}
    (hFinished : runFor fuel machine = .finished result) (extra : Nat) :
    runFor (fuel + extra) machine = .finished result := by
  rw [runFor_add, hFinished]

/-- One-step invariant and result preservation lift to every finite execution. -/
theorem runFor_preserves (invariant : Machine → Prop) (correct : SolveResult → Prop)
    (hStep : ∀ machine, invariant machine →
      ValidProgress invariant correct (step machine))
    (fuel : Nat) {machine : Machine} (hInvariant : invariant machine) :
    ValidProgress invariant correct (runFor fuel machine) := by
  induction fuel generalizing machine with
  | zero => exact hInvariant
  | succ fuel ih =>
    have hNext := hStep machine hInvariant
    cases hTransition : step machine with
    | running next =>
      have hInvariantNext : invariant next := by
        simpa [ValidProgress, hTransition] using hNext
      simpa [runFor, hTransition] using ih hInvariantNext
    | finished result =>
      simpa [runFor, ValidProgress, hTransition] using hNext

theorem invariant_of_runningReachable (invariant : Machine → Prop)
    {initial machine : Machine} (hInitial : invariant initial)
    (hStep : ∀ before after, invariant before → step before = .running after →
      invariant after)
    (hReachable : RunningReachable initial machine) : invariant machine := by
  induction hReachable with
  | initial => exact hInitial
  | advance _ hTransition ih => exact hStep _ _ ih hTransition

theorem runningReachable_of_runFor_running {initial machine next : Machine}
    (hCurrent : RunningReachable initial machine) {fuel : Nat}
    (hRun : runFor fuel machine = .running next) : RunningReachable initial next := by
  have hValid := runFor_preserves (RunningReachable initial) (fun _ => True)
    (fun current hReachable => by
      cases hTransition : step current with
      | running after =>
        exact RunningReachable.advance hReachable hTransition
      | finished result => trivial)
    fuel hCurrent
  simpa [hRun, ValidProgress] using hValid

/-- A genuinely decreasing natural-number rank on every reachable running
transition implies that the actual runner eventually returns a result. The
proof uses well-founded induction on the rank, with no assumed success fuel. -/
theorem exists_runFor_finished_of_reachable_rank (initial : Machine)
    (rank : Machine → Nat)
    (hDecrease : ∀ before after, RunningReachable initial before →
      step before = .running after → rank after < rank before) :
    ∃ fuel result, runFor fuel initial = .finished result := by
  have terminates : ∀ value, ∀ machine, rank machine = value →
      RunningReachable initial machine →
      ∃ fuel result, runFor fuel machine = .finished result := by
    intro value
    induction value using Nat.strongRecOn with
    | ind value ih =>
      intro machine hRank hReachable
      cases hTransition : step machine with
      | finished result =>
        exact ⟨1, result, by simp [runFor, hTransition]⟩
      | running next =>
        have hLess : rank next < value := by
          simpa [hRank] using hDecrease machine next hReachable hTransition
        obtain ⟨fuel, result, hFinished⟩ := ih (rank next) hLess next rfl
          (RunningReachable.advance hReachable hTransition)
        exact ⟨fuel + 1, result, by simpa [runFor, hTransition] using hFinished⟩
  exact terminates (rank initial) initial rfl .initial

/-- An invariant can supply reachability's strict rank obligation once its
preservation has been established for the actual step function. -/
theorem exists_runFor_finished_of_invariant_rank (invariant : Machine → Prop)
    (rank : Machine → Nat) {initial : Machine} (hInitial : invariant initial)
    (hPreserve : ∀ before after, invariant before → step before = .running after →
      invariant after)
    (hDecrease : ∀ before after, invariant before → step before = .running after →
      rank after < rank before) :
    ∃ fuel result, runFor fuel initial = .finished result := by
  apply exists_runFor_finished_of_reachable_rank initial rank
  intro before after hReachable hTransition
  exact hDecrease before after
    (invariant_of_runningReachable invariant hInitial hPreserve hReachable) hTransition

/-- Preservation plus a strictly decreasing reachable rank yields a finite,
correct result from the actual runner. Establishing these hypotheses for the
packed CDCL representation remains the solver verification task. -/
theorem exists_runFor_finished_correct (invariant : Machine → Prop)
    (correct : SolveResult → Prop) (rank : Machine → Nat) {initial : Machine}
    (hInitial : invariant initial)
    (hStep : ∀ machine, invariant machine →
      ValidProgress invariant correct (step machine))
    (hDecrease : ∀ before after, RunningReachable initial before →
      step before = .running after → rank after < rank before) :
    ∃ fuel result, runFor fuel initial = .finished result ∧ correct result := by
  obtain ⟨fuel, result, hFinished⟩ :=
    exists_runFor_finished_of_reachable_rank initial rank hDecrease
  have hCorrect := runFor_preserves invariant correct hStep fuel hInitial
  exact ⟨fuel, result, hFinished, by simpa [hFinished, ValidProgress] using hCorrect⟩

end MicrosatLean.Verification.Search
