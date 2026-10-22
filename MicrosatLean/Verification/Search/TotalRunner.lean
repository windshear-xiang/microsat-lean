import MicrosatLean.Verification.Search.Termination

namespace MicrosatLean.Verification.Search

open CDCL

/-- The value is computed by actual transitions; its erased proof records
semantic validity and equality to a finite prefix of the existing runner. -/
def TotalRunSpec (formula : Formula) (machine : Machine) (result : SolveResult) : Prop :=
  ValidResult formula result ∧ ∃ fuel, runFor fuel machine = .finished result

/-- A computable evaluator for the actual CDCL transition. Every running
branch has a strictly smaller concrete lexicographic control rank. The
invariant and preservation arguments live in Prop and are erased from code;
neither an assumed successful budget nor an alternative solver is used. -/
def runCertified (formula : Formula)
    (preserves : ∀ machine, MachineInvariant formula machine → InvariantProgress formula (step machine))
    (variables : Nat) (machine : Machine) (invariant : MachineInvariant formula machine)
    (variablesEq : machine.solver.nVars = variables) :
    { result : SolveResult // TotalRunSpec formula machine result } :=
  match transition : step machine with
  | .finished result =>
    ⟨result, by
      have valid := preserves machine invariant
      exact ⟨by simpa only [transition, InvariantProgress] using valid,
        ⟨1, by simp only [runFor, transition]⟩⟩⟩
  | .running after =>
    let afterInvariant : MachineInvariant formula after := by
      have valid := preserves machine invariant
      simpa only [transition, InvariantProgress] using valid
    let result := runCertified formula preserves variables after afterInvariant
      ((step_nVars transition).trans variablesEq)
    ⟨result.val, by
      obtain ⟨valid, fuel, finished⟩ := result.property
      exact ⟨valid, ⟨fuel + 1, by simpa only [runFor, transition] using finished⟩⟩⟩
termination_by controlRank (3 ^ variables) variables machine
decreasing_by
  exact MachineInvariant.step_rank invariant afterInvariant variables variablesEq transition

/-- The executable value projection retains no certificate at runtime. -/
def totalRun (formula : Formula)
    (preserves : ∀ machine, MachineInvariant formula machine → InvariantProgress formula (step machine))
    (variables : Nat) (machine : Machine) (invariant : MachineInvariant formula machine)
    (variablesEq : machine.solver.nVars = variables) : SolveResult :=
  (runCertified formula preserves variables machine invariant variablesEq).val

theorem totalRun_valid (formula : Formula)
    (preserves : ∀ machine, MachineInvariant formula machine → InvariantProgress formula (step machine))
    (variables : Nat) (machine : Machine) (invariant : MachineInvariant formula machine)
    (variablesEq : machine.solver.nVars = variables) :
    ValidResult formula (totalRun formula preserves variables machine invariant variablesEq) :=
  (runCertified formula preserves variables machine invariant variablesEq).property.1

theorem totalRun_runFor (formula : Formula)
    (preserves : ∀ machine, MachineInvariant formula machine → InvariantProgress formula (step machine))
    (variables : Nat) (machine : Machine) (invariant : MachineInvariant formula machine)
    (variablesEq : machine.solver.nVars = variables) :
    ∃ fuel, runFor fuel machine = .finished (totalRun formula preserves variables machine invariant variablesEq) :=
  (runCertified formula preserves variables machine invariant variablesEq).property.2

/-- Any completed finite run has the same result as the total evaluator.
Appending fuel compares both executions at one common actual run length. -/
theorem totalRun_eq_of_runFor_finished (formula : Formula)
    (preserves : ∀ machine, MachineInvariant formula machine → InvariantProgress formula (step machine))
    (variables : Nat) (machine : Machine) (invariant : MachineInvariant formula machine)
    (variablesEq : machine.solver.nVars = variables) {fuel : Nat} {result : SolveResult}
    (finished : runFor fuel machine = .finished result) :
    totalRun formula preserves variables machine invariant variablesEq = result := by
  obtain ⟨actualFuel, actual⟩ := totalRun_runFor formula preserves variables machine invariant variablesEq
  have first := runFor_finished_add actual fuel
  have second := runFor_finished_add finished actualFuel
  rw [Nat.add_comm fuel actualFuel] at second
  exact Progress.finished.inj (first.symm.trans second)

end MicrosatLean.Verification.Search
