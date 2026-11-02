import MicrosatLean.Verification.Invariant

namespace MicrosatLean.Verification

/-!
These are admissible logical moves, not a second executable solver. Every
premise about a learned clause or a unit must be derived from the
actual code. Semantic preservation is proved in Implementation/Logic/Moves.
Concrete watch/control preservation is a separate implementation proof.
-/

def appendEntry (a : LogicalState) (lit : Literal) (reason : Option Clause) : LogicalState :=
  { a with trail := a.trail ++ [⟨lit, reason⟩] }

/-- Clause order and duplicates are not used as semantic equality. This
relation specifically records literal permutations in corresponding entries. -/
def ClausePermutations : List Clause → List Clause → Prop
  | [], [] => True
  | left :: rest, right :: remaining =>
      left.literals.Perm right.literals ∧ ClausePermutations rest remaining
  | _, _ => False

inductive LogicalMove (input : CNF) : LogicalState → LogicalState → Prop where
  | decide (a : LogicalState) (lit : Literal)
      (declared : LiteralBound a.numVars lit) (fresh : Unassigned a.trueTrail lit.1)
      (closed : Closed a) : LogicalMove input a (appendEntry a lit none)
  | propagate (a : LogicalState) (clause : Clause) (lit : Literal)
      (stored : clause ∈ a.database) (head : clause.literals.head? = some lit)
      (fresh : Unassigned a.trueTrail lit.1)
      (tails : ∀ other ∈ clause.literals.tail, FalseIn a.trueTrail other) :
      LogicalMove input a (appendEntry a lit (some clause))
  | learn (a : LogicalState) (clause : Clause)
      (entailed : Std.Sat.CNF.EntailsClause input clause)
      (declared : ∀ lit ∈ clause, LiteralBound a.numVars lit)
      (nonempty : clause.literals ≠ []) :
      LogicalMove input a { a with learned := a.learned ++ [clause] }
  | backjump (a : LogicalState) (keep : Nat)
      (roots : a.rootSize ≤ keep) (active : keep ≤ a.trail.length) :
      LogicalMove input a { a with trail := a.trail.take keep }
  | restart (a : LogicalState) :
      LogicalMove input a { a with trail := a.trail.take a.rootSize }
  | forget (a : LogicalState) (retained : List Clause) (subset : retained ⊆ a.learned)
      (reasons : ∀ entry ∈ a.trail, ∀ clause, entry.reason = some clause →
        clause ∈ a.original ++ retained) :
      LogicalMove input a { a with learned := retained }
  | permute (a : LogicalState) (original learned : List Clause)
      (originals : ClausePermutations a.original original)
      (lemmas : ClausePermutations a.learned learned) :
      LogicalMove input a { a with original := original, learned := learned }
  | commitRoots (a : LogicalState) (count : Nat)
      (lower : a.rootSize ≤ count) (upper : count ≤ a.trail.length)
      (sound : ∀ lit ∈ prefixLiterals a count, ∀ valuation,
        Std.Sat.CNF.Sat valuation input → valuation lit.1 = lit.2) :
      LogicalMove input a { a with rootSize := count }

/-- A concrete step can perform zero or several logical moves. Pure watch
bookkeeping may stutter here; the concrete rank must still strictly decrease. -/
inductive LogicalExecution (input : CNF) : LogicalState → LogicalState → Prop where
  | refl (a : LogicalState) : LogicalExecution input a a
  | advance {before middle after : LogicalState} :
      LogicalExecution input before middle → LogicalMove input middle after →
      LogicalExecution input before after

def LogicalSoundness : Prop := ∀ input before after,
  SemanticInv input before → LogicalMove input before after → SemanticInv input after

theorem execution_preserves (sound : LogicalSoundness) {input : CNF}
    {before after : LogicalState} (valid : SemanticInv input before)
    (execution : LogicalExecution input before after) : SemanticInv input after := by
  induction execution with
  | refl => exact valid
  | advance _ move ih => exact sound _ _ _ ih move

/-- The SAT gate includes both completed propagation and complete assignment.
The UNSAT gate uses a genuine false clause on an entirely root trail. -/
def Terminal (formula : Formula) (a : LogicalState) : CDCL.SolveResult → Prop
  | .sat model _ => Covers model formula.numVars ∧ Compatible (assignment model) a.trueTrail ∧
      Complete a ∧ Closed a
  | .unsat _ => a.rootSize = a.trail.length ∧ ∃ clause ∈ a.database, Conflict a clause

def TerminalSoundness : Prop := ∀ formula a result,
  SemanticInv (formulaView formula) a → Terminal formula a result → ValidResult formula result

/-- A semantic rule for forcing the remaining literal of a satisfied clause. -/
theorem forced_head {valuation : Assignment} {clause : Clause} {head : Literal}
    (satisfied : Std.Sat.CNF.Clause.Sat valuation clause)
    (tails : ∀ lit ∈ clause, lit ≠ head → valuation lit.1 ≠ lit.2) :
    valuation head.1 = head.2 := by
  obtain ⟨lit, member, truth⟩ := Std.Sat.CNF.Clause.sat_iff_exists_mem_eq.mp satisfied
  by_cases equal : lit = head
  · simpa only [equal] using truth
  · exact False.elim (tails lit member equal truth)

theorem learning_preserves_models {input : CNF} {clause : Clause}
    (entailed : Std.Sat.CNF.EntailsClause input clause) :
    Std.Sat.CNF.BiEntails input (input.add clause) :=
  ⟨Std.Sat.CNF.entails_add_of_entails_clause _ _ entailed, Std.Sat.CNF.add_entails_left⟩

end MicrosatLean.Verification
