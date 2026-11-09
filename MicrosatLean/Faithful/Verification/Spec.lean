import MicrosatLean.Faithful.Microsat
import MicrosatLean.Faithful.Valid

/-!
# What the solver is supposed to compute

Truth of signed DIMACS literals and clauses, and what it means for an `Input`
to be satisfiable or unsatisfiable. The final theorems (`Main.lean`) are stated
with these definitions only.
-/

namespace MicrosatLean.Faithful
namespace Verification

/-- A truth value for every variable. -/
abbrev Assignment := Nat → Bool

/-- The literal `±v` is true under `a` when variable `v` has the literal's sign. -/
def LitTrue (a : Assignment) (lit : CInt) : Prop :=
  a lit.natAbs = decide (0 < lit)

/-- A clause is satisfied when at least one of its literals is true. -/
def ClauseSat (a : Assignment) (clause : List CInt) : Prop :=
  ∃ lit ∈ clause, LitTrue a lit

end Verification

open Verification

/-- `a` satisfies every clause of the input. -/
def Input.Sat (input : Input) (a : Assignment) : Prop :=
  ∀ clause ∈ input.clauses, ClauseSat a clause.toList

/-- Some assignment satisfies the input. -/
def Input.Satisfiable (input : Input) : Prop :=
  ∃ a, input.Sat a

/-- No assignment satisfies the input. -/
def Input.Unsat (input : Input) : Prop :=
  ∀ a, ¬ input.Sat a

/-- A clause is entailed by the input when every satisfying assignment satisfies
it. Learned clauses have this property; used throughout the soundness proofs. -/
def Input.Entails (input : Input) (clause : List CInt) : Prop :=
  ∀ a, input.Sat a → ClauseSat a clause

/-- The two outcomes are exclusive. Used to derive completeness from soundness. -/
theorem Input.not_unsat_of_sat {input : Input} {a : Assignment} (h : input.Sat a) :
    ¬ input.Unsat :=
  fun unsat => unsat a h

/-- The assignment C prints for SAT: variable `v` is true when `model[v]` is
nonzero (C:47, C:176). -/
def modelOf (S : solver) : Verification.Assignment := fun v => S.ld (S.model + v) != 0

/-- A correct answer for `input`: SAT with a satisfying model, or UNSAT for an
unsatisfiable input. -/
def CorrectResult (input : Input) (out : solver × CInt) : Prop :=
  (out.2 = SAT ∧ input.Sat (modelOf out.1)) ∨ (out.2 = UNSAT ∧ input.Unsat)

/-- An entailed clause with no literals means the input is unsatisfiable. Used
for the empty-clause and root-conflict cases of UNSAT soundness. -/
theorem Input.unsat_of_entails_nil {input : Input} (h : input.Entails []) : input.Unsat := by
  intro a sat
  obtain ⟨_, member, _⟩ := h a sat
  simp at member

end MicrosatLean.Faithful
