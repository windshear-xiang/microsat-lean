import MicrosatLean.Verification.Implementation.Bridge.Semantics
import MicrosatLean.Verification.Implementation.Bridge.TrailData

namespace MicrosatLean.Verification.Implementation.Bridge

private theorem literal_eq_of_same_var {literals : List Literal}
    (noClash : Logic.ClauseSpace.NoClash literals)
    {left right : Literal} (leftMember : left ∈ literals) (rightMember : right ∈ literals)
    (same : left.1 = right.1) : left = right := by
  obtain ⟨var, positive⟩ := left
  obtain ⟨other, negative⟩ := right
  simp only at same
  subst other
  cases positive <;> cases negative
  · rfl
  · exact False.elim (noClash var rightMember leftMember)
  · exact False.elim (noClash var leftMember rightMember)
  · rfl

theorem view_progress {formula : Formula} {m : CDCL.Machine}
    {original learned : List Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank) :
    ProgressInv (logicalView m.solver original learned) := by
  constructor
  · intro clause member
    rw [logicalView_database] at member
    obtain ⟨entry, stored, rfl⟩ := List.mem_map.mp member
    have unique : (Analysis.viewedLiterals entry.lits).Nodup := by
      apply List.Pairwise.map (R := fun left right : Lit => left ≠ right) literalView
        (fun left right different same => different (literalView_injective same))
      exact base.nodup entry stored
    have vars : ((Analysis.viewedLiterals entry.lits).map Prod.fst).Nodup := by
      apply List.pairwise_map.mpr
      apply unique.imp_of_mem
      intro left right leftMember rightMember different same
      exact different (literal_eq_of_same_var (base.noClash entry stored) leftMember rightMember same)
    constructor
    · simpa only [Representation.StoredClause.view, clauseView_literals,
        clauseView_literals, Analysis.viewedLiterals] using unique
    · simpa only [Representation.StoredClause.view, clauseView_literals,
        clauseView_literals, Analysis.viewedLiterals] using vars
  · apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j beforeI beforeJ same
    have activeI : i < learned.length := by simpa [logicalView] using beforeI
    have activeJ : j < learned.length := by simpa [logicalView] using beforeJ
    let left := learned[i]'activeI
    let right := learned[j]'activeJ
    have leftMember : left ∈ original ++ learned := List.mem_append_right _ (List.getElem_mem activeI)
    have rightMember : right ∈ original ++ learned := List.mem_append_right _ (List.getElem_mem activeJ)
    have ownEqual : canonicalKey m.solver.nVars left.view =
        canonicalKey m.solver.nVars right.view := by
      simpa only [logicalView, List.getElem_map, left, right, Representation.StoredClause.view,
        Representation.StoredClause.view, clauseView, clauseView] using same
    have nativeEqual := encodedKey_of_logicalKey
      (left := left) (right := right)
      (base.database.layout.packed leftMember).wellFormed (base.noClash left leftMember)
      (base.database.layout.packed rightMember).wellFormed (base.noClash right rightMember) ownEqual
    apply base.learnedDistinct.eq_of_getElem_eq
      (by simpa using activeI) (by simpa using activeJ)
    simpa only [List.getElem_map] using nativeEqual

end MicrosatLean.Verification.Implementation.Bridge
