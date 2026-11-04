import MicrosatLean.Verification.Implementation.Analysis.WatchHistory
import MicrosatLean.Verification.Implementation.Analysis.AssertionBoundary
import MicrosatLean.Verification.Implementation.Propagation.WatchAllocation

namespace MicrosatLean.Verification.Implementation.Analysis

open CDCL Representation Propagation Std.Sat

/-- Unit clauses in the old database are already true inside the actual
retained birth prefix. This follows from saved closure, even if an unrelated
active-trail truth witness would have been removed by the backjump. -/
theorem DecisionHistory.analyze_old_units {formula : Std.Sat.CNF Nat} {s : State}
    {conflict decision : Nat} {lits : Array Lit} {rank : Lit → Nat} {entries : List StoredClause}
    (history : DecisionHistory s entries)
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    ∀ old ∈ entries, old.lits.size = 1 →
      TrueBefore (CDCL.analyze s conflict).1 (CDCL.analyze s conflict).1.assigned old.lits[0]! := by
  intro old member unit
  have boundary := analyze_decision_boundary entry
  have truth := DecisionHistory.unit_true history _ boundary.1 (analyze_assigned_lt entry) boundary.2.2 member unit
  exact FalseBefore.transfer (fun i _ => congrArg (fun words : Array Lit => words[i]!) (analyze_trail s conflict)) truth

/-- The allocator adds only two genuine refs. Old refs retain their old
prefix witnesses; the new clause is checked at each of its two watched
positions. The callers below discharge those two local obligations from
freshness/absence or the real asserting assignment. -/
theorem settled_allocate {before after : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} {count truthCount : Nat} {lits : Array Lit}
    (database : Database before original learned)
    (certificate : WatchCertificate before (original ++ learned) heads)
    (settled : SettledWatches before (original ++ learned) heads count)
    (equal : PrefixLiterals before after count) (truthBound : count ≤ truthCount)
    (first : 1 < lits.size → FalseBefore after count lits[0]! → TrueBefore after truthCount lits[1]!)
    (second : 1 < lits.size → FalseBefore after count lits[1]! → TrueBefore after truthCount lits[0]!) :
    ∀ lit, FalseBefore after count lit → ∀ ref ∈ allocatedHeads before heads lits lit,
      SettledWatch after ((original ++ learned) ++ [⟨before.arena.size + 2, lits⟩]) truthCount lit ref := by
  intro lit falseLit ref watched target member id
  have oldFalse := FalseBefore.transfer (fun i bound => (equal i bound).symm) falseLit
  have oldId : ∀ old ∈ original ++ learned, old.id ≠ before.arena.size + 2 := by
    intro old stored same
    have bound := (database.layout.packed stored).endBound
    omega
  have oldRef : ref ∈ heads lit → watchClause ref ≠ before.arena.size + 2 := by
    intro old same
    obtain ⟨entry, stored, clause, _⟩ := certificate.references lit ref old
    exact oldId entry stored (clause.symm.trans same)
  have source : ref ∈ heads lit ∨
      (ref = 2 * (before.arena.size + 2) ∧ lit = lits[0]!) ∨
      (ref = 2 * (before.arena.size + 2) + 1 ∧ lit = lits[1]!) := by
    by_cases wide : 1 < lits.size
    · simp only [allocatedHeads, wide, ite_true] at watched
      exact clauseWatchHeads_source_head watched
    · exact Or.inl (by simpa only [allocatedHeads, wide, ite_false] using watched)
  rcases List.mem_append.mp member with stored | new
  · rcases source with old | newFirst | newSecond
    · obtain ⟨i, before, value⟩ := settled lit oldFalse ref old target stored id
      exact ⟨i, Nat.lt_of_lt_of_le before truthBound, (equal i before).trans value⟩
    · have fresh : watchClause ref = before.arena.size + 2 := by rw [newFirst.1]; simp only [watchClause]; omega
      exact False.elim (oldId target stored (id.symm.trans fresh))
    · have fresh : watchClause ref = before.arena.size + 2 := by rw [newSecond.1]; simp only [watchClause]; omega
      exact False.elim (oldId target stored (id.symm.trans fresh))
  · have targetEq : target = ⟨before.arena.size + 2, lits⟩ := List.mem_singleton.mp new
    subst target
    rcases source with old | newFirst | newSecond
    · exact False.elim (oldRef old id)
    · have wide : 1 < lits.size := by
        by_cases wide : 1 < lits.size
        · exact wide
        · have prior : ref ∈ heads lit := by simpa only [allocatedHeads, wide, ite_false] using watched
          exact False.elim (oldRef prior id)
      have falseFirst : FalseBefore after count lits[0]! := by simpa only [newFirst.2] using falseLit
      have trueSecond := first wide falseFirst
      simpa only [newFirst.2, otherWatch, beq_self_eq_true, ite_true] using trueSecond
    · have wide : 1 < lits.size := by
        by_cases wide : 1 < lits.size
        · exact wide
        · have prior : ref ∈ heads lit := by simpa only [allocatedHeads, wide, ite_false] using watched
          exact False.elim (oldRef prior id)
      have falseSecond : FalseBefore after count lits[1]! := by simpa only [newSecond.2] using falseLit
      have trueFirst := second wide falseSecond
      by_cases same : lits[0]! = lits[1]!
      · simpa only [newSecond.2, otherWatch, same, beq_self_eq_true, ite_true] using trueFirst
      · simpa only [newSecond.2, otherWatch, beq_iff_eq, same, ite_false] using trueFirst

end MicrosatLean.Verification.Implementation.Analysis
