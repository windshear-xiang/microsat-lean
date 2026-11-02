import MicrosatLean.Verification.Implementation.Native.Propagation.WatchUnit

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL

/-- The exact terminal source branch for a failed scan and two false watches. -/
theorem propagateWatches_conflict (fuel : Nat) (s : State) (arena first : Array Nat)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat)
    (nonzero : currentWatchRef arena first lit previous ≠ 0)
    (missing : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
      s.marks (watchClause (currentWatchRef arena first lit previous)) = none)
    (opposite : s.mark (Lit.negate
      ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0)
    (head : s.mark
      ((retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) ≠ 0) :
    propagateWatches (fuel + 1) s arena first decision oldLemmas root lit previous =
      let id := watchClause (currentWatchRef arena first lit previous)
      let retained := restoreWatchArrays s (retainWatch arena id lit) first
      if root then .finished (.unsat retained.stats)
      else
        let result := analyze retained id
        let root := result.1.db (result.2 + 1) == 0
        .running ⟨result.1.assign result.2 root, decision, .nextLiteral, oldLemmas, root, 0, 0⟩ := by
  simp only [currentWatchRef, beq_iff_eq] at nonzero
  simp only [currentWatchRef, orientWatch, beq_iff_eq] at missing
  simp only [currentWatchRef, retainWatch, orientWatch, beq_iff_eq, ne_eq] at opposite head
  cases root <;>
    simp only [propagateWatches, currentWatchRef, orientWatch, retainWatch, Id.run, pure, beq_iff_eq,
      nonzero, ite_false, missing, bne_iff_ne, ne_eq, opposite, not_true_eq_false,
      restoreWatchArrays_mark, head, ite_true, Bool.false_eq_true]

end MicrosatLean.Verification.Implementation.Native.Propagation
