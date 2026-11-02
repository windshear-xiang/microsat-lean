import MicrosatLean.Verification
import Lean.Util.CollectAxioms
import Lean.Util.Sorry
import Lean.Elab.Command

/-!
This is a scaffold audit, not a completed-verification audit. It accepts only
the eight named direct admissions, rejects admitted definitions/statements and
additional axioms, and checks that generic composition has no sorry dependency.
It also confirms that the experimental specialized result still exposes its
admissions. Remove this allowance as the implementation proofs are completed.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected := #[
    `MicrosatLean.Verification.Implementation.logical_moves,
    `MicrosatLean.Verification.Implementation.terminal,
    `MicrosatLean.Verification.Implementation.initialization,
    `MicrosatLean.Verification.Implementation.begin_propagation,
    `MicrosatLean.Verification.Implementation.next_literal,
    `MicrosatLean.Verification.Implementation.watch,
    `MicrosatLean.Verification.Implementation.choose,
    `MicrosatLean.Verification.Implementation.decreases]
  let allowed := #[`propext, `Classical.choice, `Quot.sound, `sorryAx]
  let declarations := env.constants.fold (init := #[]) fun found name info =>
    if (`MicrosatLean.Verification).isPrefixOf (privateToUserName name) then
      found.push (name, info)
    else found
  let mut admitted : Array Name := #[]
  let mut theorems : Nat := 0
  for (name, info) in declarations do
    if info.isTheorem then theorems := theorems + 1
    if info.type.hasSorry then throwError "Admitted statement: {name}"
    if let some body := info.value? (allowOpaque := true) then
      if body.hasSorry then
        unless info.isTheorem && expected.contains name do
          throwError "Unexpected direct admission: {name}"
        admitted := admitted.push name
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
  for name in expected do
    unless admitted.contains name do throwError "Update the admission inventory for {name}"
  for name in #[`MicrosatLean.Verification.satisfiedBy_iff_models,
      `MicrosatLean.Verification.unsat_iff_complete_models,
      `MicrosatLean.Verification.step_correct_with,
      `MicrosatLean.Verification.runFor_correct_with,
      `MicrosatLean.Verification.initialized_search_correct_with,
      `MicrosatLean.Verification.solve_correct_with] do
    if (← collectAxioms name).contains `sorryAx then
      throwError "Generic bridge/composition unexpectedly depends on sorry: {name}"
  unless (← collectAxioms `MicrosatLean.Verification.solveScaffold_correct).contains `sorryAx do
    throwError "The specialized scaffold must disclose its current admissions"
  logInfo m!"Scaffold audit: {theorems} theorems, {declarations.size} declarations, {admitted.size} explicit admissions."
  logInfo "Generic bridge/composition has no sorry dependency; specialized solver correctness still depends on sorryAx."

#print axioms MicrosatLean.Verification.solveScaffold_correct
