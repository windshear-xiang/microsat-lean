import MicrosatLean.Verification.Analysis.Freshness

namespace MicrosatLean.Verification.Analysis

open CDCL Representation
open Std.Sat

def VariableAbsentBefore (s : State) (decision var : Nat) : Prop :=
  ∀ i, i < decision → s.trail[i]!.var ≠ var

/-- Preserving variables is enough for the birth-to-prefix migration; it does
not assume that an original asserting head is still active or still true. -/
def PrefixVariablesPreserved (birth current : State) (count : Nat) : Prop :=
  ∀ i, i < count → current.trail[i]!.var = birth.trail[i]!.var

theorem VariableAbsentBefore.not_false {s : State} {decision : Nat} {lit : Lit}
    (absent : VariableAbsentBefore s decision lit.var) : ¬ FalseBefore s decision lit := by
  rintro ⟨i, before, equal⟩
  exact absent i before (congrArg Lit.var equal)

/-- With two distinct literals still unassigned at a prefix, no literal can
be unit there: one of those two would have to be an already-false tail. -/
theorem prefixUnitClosed_of_two_absent {s : State} {decision : Nat} {lits : Array Lit}
    {head tail : Lit} (headMember : head ∈ lits) (tailMember : tail ∈ lits)
    (different : head ≠ tail) (headAbsent : VariableAbsentBefore s decision head.var)
    (tailAbsent : VariableAbsentBefore s decision tail.var) : PrefixUnitClosed s decision lits := by
  intro pivot _ others
  by_cases same : head = pivot
  · exact False.elim (tailAbsent.not_false (others tail tailMember (by
      intro equal
      exact different (same.trans equal.symm))))
  · exact False.elim (headAbsent.not_false (others head headMember same))

theorem trueBefore_not_falseBefore {s : State} {decision : Nat} {lit : Lit}
    (active : ActiveTrail s) (bound : decision ≤ s.assigned) (trueLit : TrueBefore s decision lit) :
    ¬ FalseBefore s decision lit := by
  rintro ⟨falseIndex, falseBefore, falseValue⟩
  obtain ⟨trueIndex, trueBefore, trueValue⟩ := trueLit
  have marked := (active trueIndex (Nat.lt_of_lt_of_le trueBefore bound)).2.1
  have unmarked := (active falseIndex (Nat.lt_of_lt_of_le falseBefore bound)).2.2
  rw [trueValue] at marked
  rw [falseValue] at unmarked
  exact marked unmarked

/-- A surviving true literal already in the prefix also supplies unit
closure. In particular, an asserted unit clause can migrate here once its
head is a retained root assignment. -/
theorem prefixUnitClosed_of_true_literal {s : State} {decision : Nat} {lits : Array Lit} {head : Lit}
    (active : ActiveTrail s) (bound : decision ≤ s.assigned) (member : head ∈ lits)
    (trueHead : TrueBefore s decision head) : PrefixUnitClosed s decision lits := by
  intro pivot _ others
  by_cases same : head = pivot
  · exact same ▸ trueHead
  · exact False.elim (trueBefore_not_falseBefore active bound trueHead (others head member same))

/-- Concrete birth witnesses imply migration to predecision unit closure.
The asserting head was fresh in the birth prefix; a retained tail at or after
the older decision names a different variable. Both remain absent before that
decision whenever that prefix's variables are preserved. Losing the original
asserting head later is allowed. -/
theorem prefixUnitClosed_of_birth {birth current : State} {decision retained tailIndex : Nat}
    {lits : Array Lit} {head tail : Lit}
    (headMember : head ∈ lits) (tailMember : tail ∈ lits)
    (fresh : FreshVariable { birth with assigned := retained } head.var)
    (distinct : DistinctTrailVariables { birth with assigned := retained })
    (tailBefore : tailIndex < retained) (tailValue : birth.trail[tailIndex]! = tail)
    (older : decision ≤ tailIndex) (preserved : PrefixVariablesPreserved birth current decision) :
    PrefixUnitClosed current decision lits := by
  have headAbsent : VariableAbsentBefore current decision head.var := by
    intro i before equal
    apply fresh i (by dsimp; omega)
    exact (preserved i before).symm.trans equal
  have tailAbsent : VariableAbsentBefore current decision tail.var := by
    intro i before equal
    have variables : birth.trail[i]!.var = birth.trail[tailIndex]!.var :=
      (preserved i before).symm.trans (equal.trans (congrArg Lit.var tailValue).symm)
    have same := distinct i tailIndex (by dsimp; omega) tailBefore variables
    omega
  have different : head ≠ tail := by
    intro equal
    apply fresh tailIndex tailBefore
    exact (congrArg Lit.var tailValue).trans (congrArg Lit.var equal.symm)
  exact prefixUnitClosed_of_two_absent headMember tailMember different headAbsent tailAbsent

/-- Actual backward construction and actual backjump supply the fresh head
and retained-tail birth witnesses. The remaining concrete history premise is
that the older decision precedes that retained tail and its prefix survives.
No unconditional persistence of the original asserting head is claimed. -/
theorem buildLearned_origin_migration {formula : CNF Nat} {snapshot source current : State} {count decision : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank)
    (trail : source.trail = snapshot.trail) (candidate : Nat) (candidateBound : candidate < count)
    (lower : source.forced ≤ candidate) (nonempty : 0 < (buildLearned source candidate).2.1.size)
    (head : (buildLearned source candidate).2.1[0]! = source.trail[candidate]!)
    (j : Nat) (positive : 0 < j) (before : j < (buildLearned source candidate).2.1.size)
    (older : decision ≤ rank (buildLearned source candidate).2.1[j]!)
    (preserved : PrefixVariablesPreserved (backjump (buildLearned source candidate).1 candidate) current decision) :
    PrefixUnitClosed current decision (buildLearned source candidate).2.1 := by
  let built := buildLearned source candidate
  let birth := backjump built.1 candidate
  have ranked : ∀ i, i ≤ candidate → rank source.trail[i]! = i := by
    intro i before
    rw [trail]
    exact graph.ranks i (Nat.lt_of_le_of_lt before candidateBound)
  have sourceDistinct : DistinctTrailVariables { source with assigned := candidate + 1 } := by
    intro i k beforeI beforeK equal
    apply graph.distinctVariables i k (by dsimp at beforeI; omega) (by dsimp at beforeK; omega)
    simpa only [trail] using equal
  have cursor := buildLearned_cursor source candidate rank lower ranked
  have fresh := buildLearned_backjump_head_fresh source candidate rank lower ranked sourceDistinct head
  have position := cursor.2.2.1 j before
  have tailBefore : rank built.2.1[j]! < birth.assigned := by
    rw [backjump_assigned]
    exact cursor.2.2.2.1 j positive before
  have birthTrail : birth.trail = source.trail := backjump_trail.trans (buildLearned_frame source candidate).trail
  have cursorBound : birth.assigned ≤ candidate := by
    rw [backjump_assigned]
    exact cursor.2.1
  have birthDistinct : DistinctTrailVariables birth := by
    intro i k beforeI beforeK equal
    change i < birth.assigned at beforeI
    change k < birth.assigned at beforeK
    apply sourceDistinct i k (by dsimp; omega) (by dsimp; omega)
    simpa only [birthTrail] using equal
  have tailValue : birth.trail[rank built.2.1[j]!]! = built.2.1[j]! := by
    rw [birthTrail]
    exact position.2.2
  apply prefixUnitClosed_of_birth (birth := birth) (retained := birth.assigned)
    (head := built.2.1[0]!) (tail := built.2.1[j]!)
  · change (buildLearned source candidate).2.1[0]! ∈ (buildLearned source candidate).2.1
    simpa only [getElem!_pos (buildLearned source candidate).2.1 0 nonempty] using Array.getElem_mem nonempty
  · change (buildLearned source candidate).2.1[j]! ∈ (buildLearned source candidate).2.1
    simpa only [getElem!_pos (buildLearned source candidate).2.1 j before] using Array.getElem_mem before
  · exact fresh
  · exact birthDistinct
  · exact tailBefore
  · exact tailValue
  · exact older
  · exact preserved

end MicrosatLean.Verification.Analysis
