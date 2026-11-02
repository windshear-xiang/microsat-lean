import MicrosatLean.Verification.Implementation.Bridge.FromNativeSemantic
import MicrosatLean.Verification.Implementation.Bridge.ToNativeData

namespace MicrosatLean.Verification.Implementation.Bridge

private theorem literal_eq_of_same_var {literals : List Literal}
    (noClash : Native.Logic.ClauseSpace.NoClash literals)
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

theorem native_progress {formula : Formula} {m : CDCL.Machine}
    {original learned : List Native.Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Native.Search.StateCertificate (formulaView formula) m.solver original learned heads rank) :
    ProgressInv (nativeState m.solver original learned) := by
  constructor
  · intro clause member
    rw [nativeState_database] at member
    obtain ⟨entry, stored, rfl⟩ := List.mem_map.mp member
    have unique : (Native.Analysis.viewedLiterals entry.lits).Nodup := by
      apply List.Pairwise.map (R := fun left right : Lit => left ≠ right) Native.literalView
        (fun left right different same => different (Native.literalView_injective same))
      exact base.nodup entry stored
    have vars : ((Native.Analysis.viewedLiterals entry.lits).map Prod.fst).Nodup := by
      apply List.pairwise_map.mpr
      apply unique.imp_of_mem
      intro left right leftMember rightMember different same
      exact different (literal_eq_of_same_var (base.noClash entry stored) leftMember rightMember same)
    constructor
    · simpa only [Native.Representation.StoredClause.view, clauseView_literals,
        Native.clauseView_literals, Native.Analysis.viewedLiterals, native_view_eq] using unique
    · simpa only [Native.Representation.StoredClause.view, clauseView_literals,
        Native.clauseView_literals, Native.Analysis.viewedLiterals, native_view_eq] using vars
  · apply List.nodup_iff_eq_of_getElem_eq.mpr
    intro i j beforeI beforeJ same
    have activeI : i < learned.length := by simpa [nativeState] using beforeI
    have activeJ : j < learned.length := by simpa [nativeState] using beforeJ
    let left := learned[i]'activeI
    let right := learned[j]'activeJ
    have leftMember : left ∈ original ++ learned := List.mem_append_right _ (List.getElem_mem activeI)
    have rightMember : right ∈ original ++ learned := List.mem_append_right _ (List.getElem_mem activeJ)
    have ownEqual : canonicalKey m.solver.nVars (fromNativeEntry left).view =
        canonicalKey m.solver.nVars (fromNativeEntry right).view := by
      simpa only [nativeState, List.getElem_map, left, right, fromNativeEntry, StoredClause.view,
        Native.Representation.StoredClause.view, Native.clauseView, clauseView, native_view_eq] using same
    have nativeEqual := nativeKey_of_ownKey
      (left := fromNativeEntry left) (right := fromNativeEntry right)
      (base.database.layout.packed leftMember).wellFormed (base.noClash left leftMember)
      (base.database.layout.packed rightMember).wellFormed (base.noClash right rightMember) ownEqual
    apply base.learnedDistinct.eq_of_getElem_eq
      (by simpa using activeI) (by simpa using activeJ)
    simpa only [List.getElem_map, fromNativeEntry] using nativeEqual

end MicrosatLean.Verification.Implementation.Bridge
