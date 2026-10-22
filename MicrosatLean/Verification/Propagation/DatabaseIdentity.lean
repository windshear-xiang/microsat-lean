import MicrosatLean.Verification.Propagation.Database

namespace MicrosatLean.Verification.Representation

open CDCL

/-- The terminated packed arena determines its entire consecutive ghost
database, so independent operation lemmas cannot choose incompatible entries. -/
theorem DatabaseFrom.unique {s : State} {start : Nat} {left right : List StoredClause}
    (leftLayout : DatabaseFrom s start left) (rightLayout : DatabaseFrom s start right) :
    left = right := by
  induction left generalizing start right with
  | nil =>
    cases right with
    | nil => rfl
    | cons entry rest =>
      have bound := rightLayout.2.1.endBound
      have id := rightLayout.1
      change start = s.arena.size at leftLayout
      omega
  | cons entry rest ih =>
    cases right with
    | nil =>
      have bound := leftLayout.2.1.endBound
      have id := leftLayout.1
      change start = s.arena.size at rightLayout
      omega
    | cons other tail =>
      have id : entry.id = other.id := leftLayout.1.trans rightLayout.1.symm
      have otherPacked : PackedClause s entry.id other.lits := id.symm ▸ rightLayout.2.1
      have lits := leftLayout.2.1.unique otherPacked
      have equal : entry = other := by
        cases entry
        cases other
        simp_all
      subst other
      exact congrArg (entry :: ·) (ih leftLayout.2.2 rightLayout.2.2)

theorem Database.unique {s : State} {original learned otherOriginal otherLearned : List StoredClause}
    (left : Database s original learned) (right : Database s otherOriginal otherLearned) :
    original = otherOriginal ∧ learned = otherLearned :=
  List.append_inj' (left.layout.unique right.layout) (left.learnedCount.symm.trans right.learnedCount)

end MicrosatLean.Verification.Representation
