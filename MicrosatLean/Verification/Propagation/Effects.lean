import MicrosatLean.Verification.Search.AnalysisProgress
import MicrosatLean.CDCL.Search

namespace MicrosatLean.Verification.Propagation

open CDCL Search

/-- The actual watch traversal either keeps its trail cursors, extends the
trail by one unit assignment, or learns exactly one clause before returning. -/
inductive WatchChange (before : State) (after : Machine) : Prop where
  | scan (count : after.solver.nLemmas = before.nLemmas)
      (assigned : after.solver.assigned = before.assigned)
      (processed : after.solver.processed = before.processed)
      (phase : after.phase = .watch ∨ after.phase = .nextLiteral)
  | assign (count : after.solver.nLemmas = before.nLemmas)
      (assigned : after.solver.assigned = before.assigned + 1)
      (processed : after.solver.processed = before.processed)
      (phase : after.phase = .watch)
  | learn (count : after.solver.nLemmas = before.nLemmas + 1)
      (phase : after.phase = .nextLiteral)

structure WatchRunningEffect (before : State) (decision oldLemmas : Nat) (after : Machine) : Prop where
  variables : after.solver.nVars = before.nVars
  limit : after.solver.maxLemmas = before.maxLemmas
  decision : after.decision = decision
  oldLemmas : after.oldLemmas = oldLemmas
  change : WatchChange before after

/-- This classifies effects, without claiming that a returned UNSAT answer is
sound. Semantic correctness is supplied by the root/watch invariants. -/
def WatchEffects (before : State) (decision oldLemmas : Nat) : Progress → Prop
  | .running after => WatchRunningEffect before decision oldLemmas after
  | .finished (.unsat _) => True
  | .finished (.sat _ _) => False

theorem propagateWatches_effects (fuel : Nat) (s : State) (arena first : Array Nat)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat) :
    WatchEffects s decision oldLemmas
      (propagateWatches fuel s arena first decision oldLemmas root lit previous) := by
  induction fuel generalizing arena first previous with
  | zero =>
    exact ⟨rfl, rfl, rfl, rfl, .scan rfl rfl rfl (Or.inl rfl)⟩
  | succ fuel ih =>
    simp only [propagateWatches, Id.run, pure]
    generalize refEq : (if previous == 0 then first[lit]! else arena[watchLinkPos previous]!) = ref
    split
    · exact ⟨rfl, rfl, rfl, rfl, .scan rfl rfl rfl (Or.inr rfl)⟩
    · generalize orientedEq : (if arena[watchClause ref]! == lit then
          arena.set! (watchClause ref) arena[watchClause ref + 1]! else arena) = oriented
      cases found : replacement oriented s.marks (watchClause ref) with
      | some pos =>
        simp only
        exact ih _ _ _
      | none =>
        simp only
        split
        · exact ih _ _ _
        · split
          · exact ⟨rfl, rfl, rfl, rfl, .assign rfl rfl rfl rfl⟩
          · split
            · exact True.intro
            · refine ⟨?_, ?_, rfl, rfl, .learn ?_ rfl⟩
              · simpa only [State.assign, Id.run, pure, restoreWatchArrays] using analyze_nVars _ _
              · simpa only [State.assign, Id.run, pure, restoreWatchArrays] using analyze_maxLemmas _ _
              · simpa only [State.assign, Id.run, pure, restoreWatchArrays] using analyze_nLemmas _ _

theorem propagateWatches_running_count {fuel : Nat} {s : State} {arena first : Array Nat}
    {decision oldLemmas : Nat} {root : Bool} {lit : Lit} {previous : Nat} {after : Machine}
    (running : propagateWatches fuel s arena first decision oldLemmas root lit previous =
      .running after) :
    after.solver.nLemmas = s.nLemmas ∨ after.solver.nLemmas = s.nLemmas + 1 := by
  have effect := propagateWatches_effects fuel s arena first decision oldLemmas root lit previous
  rw [running] at effect
  cases effect.change with
  | scan count _ _ _ => exact Or.inl count
  | assign count _ _ _ => exact Or.inl count
  | learn count _ => exact Or.inr count

end MicrosatLean.Verification.Propagation
