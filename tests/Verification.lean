import MicrosatLean.Verification
import Lean.Util.CollectAxioms
import Lean.Elab.Command

/-!
Audit every declaration in the verification namespace, including private
helpers, for project axioms or admitted proofs. Standard Lean foundations are
permitted explicitly. Building the proof modules remains the kernel check;
this audit does not establish their unproved integration hypotheses.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let declarations := env.constants.fold (init := #[]) fun names name info =>
    if (`MicrosatLean.Verification).isPrefixOf (privateToUserName name) then
      names.push (name, info.isTheorem)
    else names
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let mut theorems : Nat := 0
  let mut used : Array Name := #[]
  for (name, isTheorem) in declarations do
    if isTheorem then theorems := theorems + 1
    for axiomName in ← collectAxioms name do
      unless allowed.contains axiomName do
        throwError "{name} depends on an unapproved axiom: {axiomName}"
      unless used.contains axiomName do used := used.push axiomName
  unless 0 < theorems do throwError "No verification theorems were imported"
  logInfo m!"Audited {theorems} verification theorems ({declarations.size} declarations); axioms: {used}"
