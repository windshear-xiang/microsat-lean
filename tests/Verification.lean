import MicrosatLean.Verification
import MicrosatLean.Solver
import Lean.Util.CollectAxioms
import Lean.Util.Sorry
import Lean.Elab.Command

/-!
Strict axiom audit for the complete imported verification graph. Private and
generated declarations are checked together with public declarations. No
admission is permitted in a statement, a body, or a transitive dependency.
The public IO solver theorem is checked explicitly even though its namespace
is outside the verification tree.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let declarations := env.constants.fold (init := #[]) fun found name info =>
    if (`MicrosatLean.Verification).isPrefixOf (privateToUserName name) then
      found.push (name, info)
    else found
  let mut theorems : Nat := 0
  for (name, info) in declarations do
    if info.isTheorem then theorems := theorems + 1
    if info.type.hasSorry then throwError "Admitted statement: {name}"
    if let some body := info.value? (allowOpaque := true) then
      if body.hasSorry then
        throwError "Admitted proof or definition: {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in {name}"
  unless theorems > 0 do
    throwError "The verification audit did not find any theorems"
  for name in #[`MicrosatLean.Verification.satisfiedBy_iff_models,
      `MicrosatLean.Verification.unsat_iff_complete_models,
      `MicrosatLean.Verification.step_correct_with,
      `MicrosatLean.Verification.runFor_correct_with,
      `MicrosatLean.Verification.initialized_search_correct_with,
      `MicrosatLean.Verification.solve_correct_with,
      `MicrosatLean.Verification.solveCertified_correct,
      `MicrosatLean.Verification.solveScaffold_correct,
      `MicrosatLean.Verification.initialized_search_terminates,
      `MicrosatLean.CDCL.solve_correct] do
    let info ← getConstInfo name
    unless info.isTheorem do throwError "Expected a correctness theorem: {name}"
    if info.type.hasSorry then throwError "Admitted correctness statement: {name}"
    if let some body := info.value? (allowOpaque := true) then
      if body.hasSorry then throwError "Admitted correctness proof: {name}"
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "Unexpected axiom {axiomName} in correctness theorem {name}"
  logInfo m!"Strict verification audit: {theorems} theorems, {declarations.size} declarations, no admissions."
  logInfo "Only propext, Classical.choice, and Quot.sound are permitted, including in the public IO solver theorem."

#print axioms MicrosatLean.Verification.solveCertified_correct
#print axioms MicrosatLean.Verification.solveScaffold_correct
#print axioms MicrosatLean.Verification.initialized_search_terminates
#print axioms MicrosatLean.CDCL.solve_correct
