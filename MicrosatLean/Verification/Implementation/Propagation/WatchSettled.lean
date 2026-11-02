import MicrosatLean.Verification.Implementation.Propagation.WatchInvariant
import MicrosatLean.Verification.Implementation.Propagation.DatabaseClosure
import MicrosatLean.Verification.Implementation.Analysis.OriginMigration

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL Representation Analysis

/-- The watched position opposite the literal whose list is being visited. -/
def otherWatch (lits : Array Lit) (lit : Lit) : Lit :=
  if lits[0]! == lit then lits[1]! else lits[0]!

/-- A visited genuine reference has a true opposite watch in this trail prefix.
The witness is a concrete trail index, rather than a semantic closure field. -/
def SettledWatch (s : State) (entries : List StoredClause) (count : Nat)
    (lit : Lit) (ref : Nat) : Prop :=
  ∀ entry ∈ entries, watchClause ref = entry.id →
    TrueBefore s count (otherWatch entry.lits lit)

/-- Every false literal in the processed prefix has settled all its watches. -/
def SettledWatches (s : State) (entries : List StoredClause)
    (heads : Nat → List Nat) (count : Nat) : Prop :=
  ∀ lit, FalseBefore s count lit → ∀ ref ∈ heads lit,
    SettledWatch s entries count lit ref

theorem clauseWatches_first_ref {heads : Nat → List Nat} {id first second : Nat}
    (covered : ClauseWatches heads id first second) :
    ∃ ref ∈ heads first, watchClause ref = id := by
  rcases covered.2 with forward | backward
  · exact ⟨2 * id, forward.1, by simp only [watchClause]; omega⟩
  · exact ⟨2 * id + 1, backward.2, by simp only [watchClause]; omega⟩

theorem clauseWatches_second_ref {heads : Nat → List Nat} {id first second : Nat}
    (covered : ClauseWatches heads id first second) :
    ∃ ref ∈ heads second, watchClause ref = id := by
  rcases covered.2 with forward | backward
  · exact ⟨2 * id + 1, forward.2, by simp only [watchClause]; omega⟩
  · exact ⟨2 * id, backward.1, by simp only [watchClause]; omega⟩

/-- Two distinct watched positions suffice: if all other literals are false,
the false watch's completed visit supplies the remaining true literal. -/
theorem prefixUnitClosed_of_settled_clause {s : State} {count : Nat}
    {entries : List StoredClause} {heads : Nat → List Nat} {entry : StoredClause}
    (active : ActiveTrail s) (bound : count ≤ s.assigned)
    (member : entry ∈ entries) (wide : 2 ≤ entry.lits.size)
    (covered : ClauseWatches heads entry.id entry.lits[0]! entry.lits[1]!)
    (settled : SettledWatches s entries heads count) :
    PrefixUnitClosed s count entry.lits := by
  have firstMember : entry.lits[0]! ∈ entry.lits := by
    simpa only [getElem!_pos entry.lits 0 (by omega)] using Array.getElem_mem (by omega : 0 < entry.lits.size)
  have secondMember : entry.lits[1]! ∈ entry.lits := by
    simpa only [getElem!_pos entry.lits 1 (by omega)] using Array.getElem_mem (by omega : 1 < entry.lits.size)
  intro head _ tails
  by_cases first : entry.lits[0]! = head
  · have secondFalse := tails entry.lits[1]! secondMember (by
      intro equal
      exact covered.1 (first.trans equal.symm))
    obtain ⟨ref, watched, id⟩ := clauseWatches_second_ref covered
    have truth := settled _ secondFalse ref watched entry member id
    have different : (entry.lits[0]! == entry.lits[1]!) = false := by simp [covered.1]
    have firstTrue : TrueBefore s count entry.lits[0]! := by
      simpa only [otherWatch, different, Bool.false_eq_true, ite_false] using truth
    exact first ▸ firstTrue
  · have firstFalse := tails entry.lits[0]! firstMember first
    obtain ⟨ref, watched, id⟩ := clauseWatches_first_ref covered
    have truth := settled _ firstFalse ref watched entry member id
    have secondTrue : TrueBefore s count entry.lits[1]! := by
      simpa only [otherWatch, beq_self_eq_true, ite_true] using truth
    by_cases second : entry.lits[1]! = head
    · exact second ▸ secondTrue
    · exact False.elim (trueBefore_not_falseBefore active bound secondTrue
        (tails entry.lits[1]! secondMember second))

/-- At a quiescent boundary, genuine watch coverage and completed visits yield
the clause/trail unit-closure predicate used by the decision-history proof. -/
theorem prefixUnitClosed_of_settled {s : State} {count : Nat}
    {entries : List StoredClause} {heads : Nat → List Nat}
    (active : ActiveTrail s) (bound : count ≤ s.assigned)
    (certificate : WatchCertificate s entries heads)
    (nonempty : ∀ entry ∈ entries, 0 < entry.lits.size)
    (units : ∀ entry ∈ entries, entry.lits.size = 1 → TrueBefore s count entry.lits[0]!)
    (settled : SettledWatches s entries heads count) :
    ∀ entry ∈ entries, PrefixUnitClosed s count entry.lits := by
  intro entry member
  by_cases unit : entry.lits.size = 1
  · apply prefixUnitClosed_of_true_literal (head := entry.lits[0]!) active bound
    · simpa only [getElem!_pos entry.lits 0 (by omega)] using Array.getElem_mem (by omega : 0 < entry.lits.size)
    · exact units entry member unit
  · have wide : 2 ≤ entry.lits.size := by have := nonempty entry member; omega
    exact prefixUnitClosed_of_settled_clause active bound member wide
      (certificate.covered entry member wide) settled

/-- Prefix unit closure excludes an all-false genuine clause. This supplies
the concrete nonfalse witness required by the saved-model SAT return rule. -/
theorem databaseNoConflict_of_prefixUnitClosed {s : State} {entries : List StoredClause}
    (active : ActiveTrail s) (marked : MarkedOnTrail s)
    (nonempty : ∀ entry ∈ entries, 0 < entry.lits.size)
    (closed : ∀ entry ∈ entries, PrefixUnitClosed s s.assigned entry.lits) :
    DatabaseNoConflict s entries := by
  intro entry member
  classical
  by_cases witness : ∃ lit ∈ entry.lits, s.mark lit = 0
  · exact witness
  · have allFalse : ∀ lit ∈ entry.lits, FalseBefore s s.assigned lit := by
      intro lit member
      exact marked lit (fun zero => witness ⟨lit, member, zero⟩)
    have first : entry.lits[0]! ∈ entry.lits := by
      simpa only [getElem!_pos entry.lits 0 (nonempty entry member)] using
        Array.getElem_mem (nonempty entry member)
    have truth := closed entry member entry.lits[0]! first (fun tail member _ => allFalse tail member)
    exact False.elim (trueBefore_not_falseBefore active (Nat.le_refl _) truth (allFalse _ first))

end MicrosatLean.Verification.Implementation.Propagation
