import MicrosatLean.Verification.Search.MachineNext
import MicrosatLean.Verification.Search.MachineChoice
import MicrosatLean.Verification.Search.MachineWatch

namespace MicrosatLean.Verification.Search

open CDCL

/-- Every actual total core step preserves the concrete machine invariant or
returns a valid result. All four executable phase branches are proved. -/
theorem step_preserves_invariant {formula : Formula} {machine : Machine}
    (invariant : MachineInvariant formula machine) : InvariantProgress formula (step machine) := by
  cases phase : machine.phase with
  | beginPropagation => exact step_beginPropagation_invariant invariant phase
  | nextLiteral => exact step_nextLiteral_invariant invariant phase
  | watch => exact step_watch_invariant invariant phase
  | choose => exact step_choose_invariant invariant phase

theorem step_running_invariant {formula : Formula} {before after : Machine}
    (invariant : MachineInvariant formula before) (running : step before = .running after) :
    MachineInvariant formula after := by
  simpa only [running, InvariantProgress] using step_preserves_invariant invariant

theorem step_finished_valid {formula : Formula} {before : Machine} {result : SolveResult}
    (invariant : MachineInvariant formula before) (finished : step before = .finished result) :
    ValidResult formula result := by
  simpa only [finished, InvariantProgress] using step_preserves_invariant invariant

end MicrosatLean.Verification.Search
