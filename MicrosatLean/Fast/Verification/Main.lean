import MicrosatLean.Fast.Verification.Step
import MicrosatLean.Fast.Verification.Analyze
import MicrosatLean.Fast.Verification.Parse

/-!
# Main theorems of the fast port: it terminates, and its answers are correct

For a valid input (`ASSUMPTIONS.md`, section 1; no other assumption), the fast port's
`main` without I/O (`microsatFast`) finishes (`FTerminates`), and answers either "out of
memory", or SAT with a printed model that satisfies the input, or UNSAT for an
unsatisfiable input (`FastCorrect`). Out of memory replaces the faithful port's memory
assumption E3; `Int32` cells replace E2.
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- `conflict_fast` has the statement `propagate`'s proof assumes. -/
theorem conflictSpec : ConflictSpec := by
  intros; apply conflict_fast <;> assumption

/-- `FastMain.lean`'s `main` without I/O: `parse`, then `solve` unless `parse` already
answered (out of memory, a parse error or UNSAT). `none`: out of memory in `initCDCL`. -/
def microsatFast (input : Input) : Option (Lay × St × UInt8) :=
  match parse input.nVars input.nClauses input.tokens with
  | none => none
  | some (L, s, r) =>
    if r == OOM || r == PARSE_ERROR || r == UNSAT then some (L, s, r) else some (L, solve L s)

/-- The fast port finishes: `parse` returns, and unless it already answered, `solve`'s loop
finishes after finitely many steps (`FRunsTo`). -/
def FTerminates (input : Input) : Prop :=
  match parse input.nVars input.nClauses input.tokens with
  | none => True
  | some (L, s, r) => (r == OOM || r == PARSE_ERROR || r == UNSAT) = true ∨ ∃ out, FRunsTo L s s.head out

/-- A correct answer: out of memory, or SAT with a printed model that satisfies the input, or
UNSAT for an unsatisfiable input. -/
def FastCorrect (input : Input) : Option (Lay × St × UInt8) → Prop
  | none => True
  | some (_, s, r) => r = OOM ∨ (r = SAT ∧ input.Sat (fastModel s)) ∨ (r = UNSAT ∧ input.Unsat)

/-- Termination and correctness together, for every valid input. -/
theorem microsatFast_correct {input : Input} (valid : input.Valid) :
    FTerminates input ∧ FastCorrect input (microsatFast input) := by
  have hp := parse_fast valid
  unfold FTerminates microsatFast
  revert hp
  match parse input.nVars input.nClauses input.tokens with
  | none => intro _; exact ⟨trivial, trivial⟩
  | some (L, s, r) =>
    intro hp
    dsimp only
    rcases hp with rfl | ⟨rfl, unsat⟩ | ⟨rfl, hB, fa, sl, inv⟩
    · exact ⟨Or.inl rfl, Or.inl rfl⟩
    · exact ⟨Or.inl rfl, Or.inr (Or.inr ⟨rfl, unsat⟩)⟩
    · obtain ⟨out, hrun, hcor⟩ := frun_correct conflictSpec s s.head ⟨hB, fa, sl, inv⟩
      have hsolve : solve L s = out := hrun.run_eq
      refine ⟨Or.inr ⟨out, hrun⟩, ?_⟩
      rw [if_neg (by decide), hsolve]
      exact hcor

/-- Termination on every valid input. -/
theorem microsatFast_terminates {input : Input} (valid : input.Valid) : FTerminates input :=
  (microsatFast_correct valid).1

/-- Soundness of SAT: the printed model satisfies every input clause. -/
theorem microsatFast_sat_sound {input : Input} (valid : input.Valid) {L : Lay} {s : St}
    (h : microsatFast input = some (L, s, SAT)) : input.Sat (fastModel s) := by
  have := (microsatFast_correct valid).2
  rw [h] at this
  rcases this with h1 | ⟨-, sat⟩ | ⟨h1, -⟩
  · exact absurd h1 (by decide)
  · exact sat
  · exact absurd h1 (by decide)

/-- Soundness of UNSAT: no assignment satisfies the input. -/
theorem microsatFast_unsat_sound {input : Input} (valid : input.Valid) {L : Lay} {s : St}
    (h : microsatFast input = some (L, s, UNSAT)) : input.Unsat := by
  have := (microsatFast_correct valid).2
  rw [h] at this
  rcases this with h1 | ⟨h1, -⟩ | ⟨-, unsat⟩
  · exact absurd h1 (by decide)
  · exact absurd h1 (by decide)
  · exact unsat

/-- Completeness up to memory: on a satisfiable input the answer is SAT or out of memory. -/
theorem microsatFast_complete_sat {input : Input} (valid : input.Valid) (sat : input.Satisfiable)
    {L : Lay} {s : St} {r : UInt8} (h : microsatFast input = some (L, s, r)) : r = SAT ∨ r = OOM := by
  have := (microsatFast_correct valid).2
  rw [h] at this
  rcases this with h1 | ⟨h1, -⟩ | ⟨-, unsat⟩
  · exact Or.inr h1
  · exact Or.inl h1
  · obtain ⟨a, ha⟩ := sat; exact absurd unsat (Input.not_unsat_of_sat ha)

/-- Completeness up to memory: on an unsatisfiable input the answer is UNSAT or out of
memory. -/
theorem microsatFast_complete_unsat {input : Input} (valid : input.Valid) (unsat : input.Unsat)
    {L : Lay} {s : St} {r : UInt8} (h : microsatFast input = some (L, s, r)) : r = UNSAT ∨ r = OOM := by
  have := (microsatFast_correct valid).2
  rw [h] at this
  rcases this with h1 | ⟨-, sat⟩ | ⟨h1, -⟩
  · exact Or.inr h1
  · exact absurd unsat (Input.not_unsat_of_sat sat)
  · exact Or.inl h1

end MicrosatLean.Fast.Verification
