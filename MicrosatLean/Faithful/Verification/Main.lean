import MicrosatLean.Faithful.Verification.Run
import MicrosatLean.Faithful.Verification.Init
import MicrosatLean.Faithful.Verification.Step

/-!
# Main theorems: `microsat` terminates, and is sound and complete

For a valid input (`ASSUMPTIONS.md`, section 1) and enough memory (E3), the C
program's `main` (C:248–249) finishes and answers correctly. The lemmas live in
`Init.lean` (loading the input), `Step.lean` (one loop iteration) and `Run.lean`
(the loop as a whole).
-/

namespace MicrosatLean.Faithful.Verification

/-- C's `main` without printing (C:248–249): `parse`, then `solve` unless `parse`
already found UNSAT. `mem_max` is C's `1 << 30` unless given. -/
def microsat (input : Input) (mem_max : CInt := 1 <<< 30) : solver × CInt :=
  let (S, r) := parse input.nVars input.nClauses input.tokens mem_max
  if r == UNSAT then (S, r) else solve S

/-- `microsat` terminates: `parse` stops with UNSAT, or `solve`'s loop finishes after
finitely many iterations (`RunsTo`). The loops inside `parse` and `step` finish by
the decreasing measures used in their proofs. -/
def Terminates (input : Input) (mem_max : CInt) : Prop :=
  let (S, r) := parse input.nVars input.nClauses input.tokens mem_max
  r = UNSAT ∨ ∃ out, RunsTo { S with res := 0 } S.head out

/-- Termination and correctness together: `microsat` finishes, and answers SAT with a
satisfying model or UNSAT for an unsatisfiable input. The other theorems below are
corollaries. Uses `parse_correct`, `runsTo_of_rank` and the three `step` contracts. -/
theorem microsat_correct {input : Input} {mem_max : CInt} (valid : input.Valid)
    (memory : memoryBound input ≤ mem_max) :
    Terminates input mem_max ∧ CorrectResult input (microsat input mem_max) := by
  unfold Terminates microsat
  match h : parse input.nVars input.nClauses input.tokens mem_max with
  | (S, r) =>
    rcases parse_correct valid memory h with ⟨rfl, unsat⟩ | ⟨rfl, inv⟩
    · exact ⟨Or.inl rfl, Or.inr ⟨rfl, unsat⟩⟩
    · obtain ⟨out, runs, correct⟩ := runsTo_of_rank rankLT_wf (Inv input) (fun S _ => rank S)
        (CorrectResult input) step_preserves step_decreases step_finished _ _ inv
      have solved : solve S = out := runs.run_eq
      have different : (SAT : CInt) ≠ UNSAT := by decide
      refine ⟨Or.inr ⟨out, runs⟩, ?_⟩
      simpa [different, solved] using correct

/-- Termination: `microsat` finishes on every valid input given enough memory. -/
theorem microsat_terminates {input : Input} {mem_max : CInt} (valid : input.Valid)
    (memory : memoryBound input ≤ mem_max) : Terminates input mem_max :=
  (microsat_correct valid memory).1

/-- Soundness of SAT: when `microsat` answers SAT, the model it prints satisfies
every input clause. -/
theorem microsat_sat_sound {input : Input} {mem_max : CInt} (valid : input.Valid)
    (memory : memoryBound input ≤ mem_max) (sat : (microsat input mem_max).2 = SAT) :
    input.Sat (modelOf (microsat input mem_max).1) := by
  rcases (microsat_correct valid memory).2 with ⟨_, model⟩ | ⟨unsat, _⟩
  · exact model
  · rw [sat] at unsat; exact absurd unsat (by decide)

/-- Soundness of UNSAT: when `microsat` answers UNSAT, no assignment satisfies the
input. -/
theorem microsat_unsat_sound {input : Input} {mem_max : CInt} (valid : input.Valid)
    (memory : memoryBound input ≤ mem_max) (unsat : (microsat input mem_max).2 = UNSAT) :
    input.Unsat := by
  rcases (microsat_correct valid memory).2 with ⟨sat, _⟩ | ⟨_, proof⟩
  · rw [unsat] at sat; exact absurd sat (by decide)
  · exact proof

/-- Completeness for SAT: a satisfiable input is answered SAT. -/
theorem microsat_complete_sat {input : Input} {mem_max : CInt} (valid : input.Valid)
    (memory : memoryBound input ≤ mem_max) (satisfiable : input.Satisfiable) :
    (microsat input mem_max).2 = SAT := by
  rcases (microsat_correct valid memory).2 with ⟨sat, _⟩ | ⟨_, unsat⟩
  · exact sat
  · obtain ⟨a, model⟩ := satisfiable
    exact absurd unsat (Input.not_unsat_of_sat model)

/-- Completeness for UNSAT: an unsatisfiable input is answered UNSAT. -/
theorem microsat_complete_unsat {input : Input} {mem_max : CInt} (valid : input.Valid)
    (memory : memoryBound input ≤ mem_max) (unsat : input.Unsat) :
    (microsat input mem_max).2 = UNSAT := by
  rcases (microsat_correct valid memory).2 with ⟨_, model⟩ | ⟨result, _⟩
  · exact absurd unsat (Input.not_unsat_of_sat model)
  · exact result

end MicrosatLean.Faithful.Verification
