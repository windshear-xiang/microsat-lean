import MicrosatLean.Verification.Propagation.WatchBounds

namespace MicrosatLean.Verification.Propagation

open CDCL Representation

/-- Nonzero references and the concrete next links determine a finite chain. -/
theorem WatchChain.unique {s : State} {left right : List Nat}
    (leftChain : WatchChain s left) (rightChain : WatchChain s right)
    (leftNonzero : ∀ ref ∈ left, ref ≠ 0) (rightNonzero : ∀ ref ∈ right, ref ≠ 0)
    (head : left.headD 0 = right.headD 0) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons ref rest =>
      have zero : ref = 0 := by simpa only [List.headD_nil, List.headD_cons] using head.symm
      exact False.elim (rightNonzero ref (by simp) zero)
  | cons ref rest ih =>
    cases right with
    | nil =>
      have zero : ref = 0 := by simpa only [List.headD_nil, List.headD_cons] using head
      exact False.elim (leftNonzero ref (by simp) zero)
    | cons other tail =>
      have equal : ref = other := by simpa only [List.headD_cons] using head
      subst other
      exact congrArg (ref :: ·) (ih leftChain.2 rightChain.2
        (fun old member => leftNonzero old (by simp [member]))
        (fun old member => rightNonzero old (by simp [member]))
        (leftChain.1.symm.trans rightChain.1))

/-- Simultaneous proper watch ghosts of the same actual arrays coincide. -/
theorem WatchCertificate.heads_unique {s : State} {original learned : List StoredClause}
    {left right : Nat → List Nat} (database : Database s original learned)
    (leftCertificate : WatchCertificate s (original ++ learned) left)
    (rightCertificate : WatchCertificate s (original ++ learned) right) : left = right := by
  funext lit
  exact (leftCertificate.links lit).chain.unique (rightCertificate.links lit).chain
    (fun ref member => storedWatchRef_nonzero database (leftCertificate.references lit ref member))
    (fun ref member => storedWatchRef_nonzero database (rightCertificate.references lit ref member))
    ((leftCertificate.links lit).2.1.symm.trans (rightCertificate.links lit).2.1)

end MicrosatLean.Verification.Propagation
