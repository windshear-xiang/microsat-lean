import MicrosatLean.Verification.Implementation.Encoding
import MicrosatLean.Verification.Implementation.Representation.State
import MicrosatLean.Verification.Implementation.Logic.Resolution

namespace MicrosatLean.Verification.Implementation.Representation

open CDCL
open Std.Sat

/-- The trail stores falsified literals, rather than the true signed decisions. -/
def Falsifies (a : Nat → Bool) (lit : Lit) : Prop :=
  a (literalView lit).1 ≠ (literalView lit).2

@[simp] theorem falsifies_negate_iff (a : Nat → Bool) (lit : Lit) :
    Falsifies a lit.negate ↔ a (literalView lit).1 = (literalView lit).2 := by
  simp only [Falsifies, literalView_negate, Literal.negate]
  cases a (literalView lit).1 <;> cases (literalView lit).2 <;> decide

/-- Agreement with a trail prefix records decision assumptions as well as
propagations. It makes no unconditional entailment claim about decisions. -/
def PrefixCompatible (s : State) (a : Nat → Bool) (count : Nat) : Prop :=
  ∀ i, i < count → Falsifies a s.trail[i]!

def TrailCompatible (s : State) (a : Nat → Bool) : Prop :=
  PrefixCompatible s a s.assigned

theorem PrefixCompatible.mono {s : State} {a : Nat → Bool} {short long : Nat}
    (h : PrefixCompatible s a long) (hle : short ≤ long) : PrefixCompatible s a short :=
  fun i hi => h i (Nat.lt_of_lt_of_le hi hle)

/-- Semantic reason dependencies: a propagated entry follows from the input
and the earlier trail assumptions. A decision is identified by reason zero. -/
def ReasonConsequences (formula : Std.Sat.CNF Nat) (s : State) : Prop :=
  ∀ i, i < s.assigned → s.reason s.trail[i]! ≠ 0 →
    ∀ a, CNF.Sat a formula → PrefixCompatible s a i → Falsifies a s.trail[i]!

/-- Every entry in the forced prefix is a propagation, never a decision. -/
def RootReasons (s : State) : Prop :=
  ∀ i, i < s.forced → s.reason s.trail[i]! ≠ 0

/-- Root assignments hold in every model of the input. -/
def RootConsequences (formula : Std.Sat.CNF Nat) (s : State) : Prop :=
  ∀ a, CNF.Sat a formula → PrefixCompatible s a s.forced

end MicrosatLean.Verification.Implementation.Representation
