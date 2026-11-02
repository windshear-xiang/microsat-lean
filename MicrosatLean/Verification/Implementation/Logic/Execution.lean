import MicrosatLean.Verification.Transitions

namespace MicrosatLean.Verification.Implementation.Logic

/-! Small trace combinators for concrete refinement proofs. -/

theorem single_move {input : CNF} {before after : LogicalState}
    (move : LogicalMove input before after) : LogicalExecution input before after :=
  .advance (.refl _) move

theorem execution_trans {input : CNF} {before middle after : LogicalState}
    (first : LogicalExecution input before middle) (second : LogicalExecution input middle after) :
    LogicalExecution input before after := by
  induction second with
  | refl => exact first
  | advance _ move ih => exact .advance ih move

/-- Learning is separate from forgetting: temporary duplicate clauses are
allowed by logical semantics. The concrete progress invariant handles freshness. -/
theorem learn_many {input : CNF} (before : LogicalState) (clauses : List Clause)
    (entailed : ∀ clause ∈ clauses, Std.Sat.CNF.EntailsClause input clause)
    (declared : ∀ clause ∈ clauses, ∀ lit ∈ clause, LiteralBound before.numVars lit)
    (nonempty : ∀ clause ∈ clauses, clause.literals ≠ []) :
    LogicalExecution input before { before with learned := before.learned ++ clauses } := by
  induction clauses generalizing before with
  | nil => simpa only [List.append_nil] using (LogicalExecution.refl before (input := input))
  | cons clause rest ih =>
    let next := { before with learned := before.learned ++ [clause] }
    have first : LogicalExecution input before next := single_move
      (.learn before clause (entailed clause (by simp))
        (declared clause (by simp)) (nonempty clause (by simp)))
    have tail := ih next (fun item member => entailed item (by simp [member]))
      (fun item member => declared item (by simp [member]))
      (fun item member => nonempty item (by simp [member]))
    have combined := execution_trans first tail
    simpa only [next, List.append_assoc, List.singleton_append] using combined

end MicrosatLean.Verification.Implementation.Logic
