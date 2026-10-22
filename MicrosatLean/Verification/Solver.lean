import MicrosatLean.Verification.Search.TotalRunner
import MicrosatLean.Verification.Search.MachinePreservation

namespace MicrosatLean.Verification

open CDCL Search Std.Sat

/-- Initialize and execute the actual CDCL solver with its proved total
transition evaluator. The impossible initialization error is ruled out by
the input-bound specification; early UNSAT retains the real initializer. -/
def solveWellFormed (formula : Formula) (wellFormed : WellFormed formula) (config : Config := {}) :
    SolveResult :=
  match initialized : initState formula config with
  | .error message => False.elim (Initialization.initState_no_error wellFormed config message initialized)
  | .ok none => .unsat {}
  | .ok (some s) =>
    totalRun formula (fun _ invariant => step_preserves_invariant invariant) s.nVars
      { solver := s, decision := s.head }
      (initState_some_machineInvariant wellFormed initialized) rfl

/-- The public total value includes a computable finite input-bound check.
No model checking, alternate solver, or successful fuel is used to obtain
the returned SAT/UNSAT result. -/
def solveVerified (formula : Formula) (config : Config := {}) : Except String SolveResult :=
  if wellFormed : WellFormed formula then .ok (solveWellFormed formula wellFormed config)
  else .error "literal outside the declared variable bounds"

/-- Every well-formed input returns a genuine SAT model or sound UNSAT.
The function itself is total, and the nontrivial search follows the actual
transition with its proved decreasing rank. -/
theorem solveWellFormed_valid (formula : Formula) (wellFormed : WellFormed formula) (config : Config := {}) :
    ValidResult formula (solveWellFormed formula wellFormed config) := by
  unfold solveWellFormed
  split
  · rename_i message initialized
    exact False.elim (Initialization.initState_no_error wellFormed config message initialized)
  · rename_i initialized
    exact Initialization.initState_none_unsat wellFormed initialized
  · rename_i s initialized
    exact totalRun_valid formula (fun _ invariant => step_preserves_invariant invariant) s.nVars
      { solver := s, decision := s.head }
      (initState_some_machineInvariant wellFormed initialized) rfl

theorem solveVerified_correct (formula : Formula) (wellFormed : WellFormed formula) (config : Config := {}) :
    ∃ result, solveVerified formula config = .ok result ∧ ValidResult formula result := by
  exact ⟨solveWellFormed formula wellFormed config,
    by simp only [solveVerified, dite_eq_left wellFormed], solveWellFormed_valid formula wellFormed config⟩

theorem solveVerified_ok_valid {formula : Formula} {config : Config} {result : SolveResult}
    (returned : solveVerified formula config = .ok result) : ValidResult formula result := by
  unfold solveVerified at returned
  split at returned
  · cases returned
    exact solveWellFormed_valid _ _ _
  · cases returned

/-- The certified evaluator returns exactly the answer of a finite actual
`runFor` execution from the original initialized machine. -/
theorem solveWellFormed_runFor {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (initialized : initState formula config = .ok (some s)) :
    ∃ fuel, runFor fuel { solver := s, decision := s.head } =
      .finished (solveWellFormed formula wellFormed config) := by
  unfold solveWellFormed
  split
  · rename_i message impossible
    rw [initialized] at impossible
    cases impossible
  · rename_i impossible
    rw [initialized] at impossible
    cases impossible
  · rename_i actual initializedActual
    have same : actual = s := Option.some.inj (Except.ok.inj (initializedActual.symm.trans initialized))
    subst actual
    exact totalRun_runFor formula (fun _ invariant => step_preserves_invariant invariant) s.nVars
      { solver := s, decision := s.head }
      (initState_some_machineInvariant wellFormed initializedActual) rfl

end MicrosatLean.Verification
