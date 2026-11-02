import MicrosatLean.CDCL.Search

namespace MicrosatLean.CDCL

/-- Resume the copied CDCL transition runner without proof dependencies.
Only this unbounded IO driver is partial; each batch remains total. -/
private partial def drive (machine : Machine) : IO SolveResult := do
  match runFor 4096 machine with
  | .finished result => return result
  | .running next => drive next

/-- Check all input bounds before initialization, then execute the CDCL core.
The precheck matches the public entry point in `Tim-dev-verification`. -/
def solve (formula : Formula) (config : Config := {}) : IO (Except String SolveResult) := do
  if !formula.wellFormed then
    return .error "literal outside the declared variable bounds"
  match initState formula config with
  | .error message => return .error message
  | .ok none => return .ok (.unsat {})
  | .ok (some state) =>
    return .ok (← drive { solver := state, decision := state.head })

end MicrosatLean.CDCL
