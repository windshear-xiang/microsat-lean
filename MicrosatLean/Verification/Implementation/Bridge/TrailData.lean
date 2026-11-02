import MicrosatLean.Verification.Implementation.Bridge.Representation

namespace MicrosatLean.Verification.Implementation.Bridge

theorem active_concrete {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Representation.ActiveTrail m.solver := by
  intro i before
  have active : i < a.trail.length := by simpa only [certificate.representation.trailLength] using before
  have member : a.trail[i]!.literal ∈ a.trueTrail := by
    apply List.mem_map.mpr
    exact ⟨a.trail[i], List.getElem_mem active, by simp [getElem!_pos a.trail i active]⟩
  have declared := certificate.semantic.declaredTrail _ member
  unfold LiteralBound at declared
  rw [trail_var certificate.representation before] at declared
  refine ⟨?_, certificate.representation.active i before⟩
  change 1 ≤ m.solver.trail[i]!.var ∧ m.solver.trail[i]!.var ≤ m.solver.nVars
  rw [certificate.representation.variables] at declared
  exact ⟨by omega, declared.2⟩

theorem distinct_concrete {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Representation.DistinctTrailVariables m.solver := by
  intro i j beforeI beforeJ equal
  have activeI : i < a.trail.length := by simpa only [certificate.representation.trailLength] using beforeI
  have activeJ : j < a.trail.length := by simpa only [certificate.representation.trailLength] using beforeJ
  apply certificate.semantic.distinct.eq_of_getElem_eq
    (by simpa only [LogicalState.trueTrail, List.length_map] using activeI)
    (by simpa only [LogicalState.trueTrail, List.length_map] using activeJ)
  simpa only [LogicalState.trueTrail, List.getElem_map, ← getElem!_pos a.trail i activeI,
    ← getElem!_pos a.trail j activeJ, trail_var certificate.representation beforeI,
    trail_var certificate.representation beforeJ] using equal

theorem phases_concrete {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) : Representation.TrailPhases m.solver := by
  intro i before
  have active : i < a.trail.length := by simpa only [represented.trailLength] using before
  have phase := represented.phases i active
  rw [represented.trail i before] at phase
  have parity : (!(m.solver.trail[i]! % 2 == 0)) = (m.solver.trail[i]! % 2 == 1) := by
    rcases Nat.mod_two_eq_zero_or_one m.solver.trail[i]! with parity | parity <;> simp [parity]
  simpa only [literalView, Std.Sat.Literal.negate, parity] using phase

theorem reason_none_iff {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {i : Nat} (before : i < m.solver.assigned) :
    a.trail[i]!.reason = none ↔ m.solver.reason m.solver.trail[i]! = 0 := by
  constructor
  · intro absent
    simpa only [absent] using represented.reasons i before
  · intro zero
    cases reason : a.trail[i]!.reason with
    | none => rfl
    | some clause =>
      have present := represented.reasons i before
      simp only [reason] at present
      obtain ⟨entry, member, id, _⟩ := present
      have stored := (database_concrete represented).layout.packed
        (by simpa only [RepresentationWitness.entries, List.map_append] using
          member)
      have lower : 4 ≤ entry.id := stored.startLower
      rw [zero] at id
      omega

theorem reasonDatabase_concrete {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) : Representation.ReasonDatabase m.solver
      (w.original ++ w.learned) := by
  intro i before nonzero
  cases reason : a.trail[i]!.reason with
  | none => exact False.elim (nonzero ((reason_none_iff represented before).mp reason))
  | some clause =>
    have present := represented.reasons i before
    simp only [reason] at present
    obtain ⟨entry, member, id, _⟩ := present
    exact ⟨entry,
      by simpa only [RepresentationWitness.entries, List.map_append] using
        member, id.symm⟩

theorem normalized_concrete {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w)
    {entry : StoredClause} (member : entry ∈ w.entries) :
    entry.lits.toList.Nodup ∧
      Logic.ClauseSpace.NoClash (Analysis.viewedLiterals entry.lits) := by
  have normalized := certificate.progress.normalized entry.view
    (stored_view_mem certificate.representation member)
  have vars : (Analysis.viewedLiterals entry.lits).map Prod.fst |>.Nodup := by
    simpa only [Representation.StoredClause.view, clauseView_literals, Analysis.viewedLiterals]
      using normalized.2
  constructor
  · apply nodup_of_map literalView
    simpa only [Representation.StoredClause.view, clauseView_literals] using normalized.1
  · exact Logic.ClauseSpace.noClash_of_noDuplicateVariables vars

theorem canonicalKey_congr (n : Nat) {left right : Clause}
    (members : ∀ lit, lit ∈ left ↔ lit ∈ right) : canonicalKey n left = canonicalKey n right := by
  simp only [canonicalKey]
  apply List.map_congr_left
  intro i _
  simp only [members]

theorem logicalKey_of_encodedKey {variables : Nat} {entry : StoredClause}
    (bounded : ∀ lit ∈ entry.lits, Representation.LiteralBound variables lit)
    (normalized : Logic.ClauseSpace.NoClash (Analysis.viewedLiterals entry.lits)) :
    canonicalKey variables (.ofLiterals (Analysis.canonicalKey variables entry.lits)) =
      canonicalKey variables entry.view := by
  apply canonicalKey_congr
  intro lit
  rw [← Std.Sat.CNF.Clause.mem_literals_iff, Std.Sat.CNF.Clause.literals_ofLiterals]
  change lit ∈ Logic.ClauseSpace.canonicalize variables _ ↔ lit ∈ entry.view
  rw [Logic.ClauseSpace.canonicalize_coverage
    (Analysis.viewedLiterals_bounded bounded) normalized]
  simp only [Representation.StoredClause.view, ← Std.Sat.CNF.Clause.mem_literals_iff, clauseView_literals,
    Analysis.viewedLiterals]

theorem learnedDistinct_concrete {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    (w.learned.map fun entry =>
      Analysis.canonicalKey m.solver.nVars entry.lits).Nodup := by
  apply nodup_of_map (fun literals => canonicalKey m.solver.nVars (.ofLiterals literals))
  have keys : (w.learned.map (fun entry =>
      Analysis.canonicalKey m.solver.nVars entry.lits)).map
      (fun literals => canonicalKey m.solver.nVars (.ofLiterals literals)) =
      a.learned.map (canonicalKey a.numVars) := by
    rw [certificate.representation.learned]
    simp only [List.map_map]
    apply List.map_congr_left
    intro entry member
    have allMember : entry ∈ w.entries := List.mem_append_right _ member
    have packed := (database_concrete certificate.representation).layout.packed
      (by simpa only [RepresentationWitness.entries, List.map_append] using
        allMember)
    simpa only [Function.comp_def, certificate.representation.variables] using
      logicalKey_of_encodedKey packed.wellFormed (normalized_concrete certificate allMember).2
  rw [keys]
  exact certificate.progress.distinctLearned

private def polarityChoice (clause : Clause) (var : Nat) : Option Bool :=
  if (var, true) ∈ clause then some true
  else if (var, false) ∈ clause then some false else none

private theorem polarityChoice_eq_some {clause : Clause}
    (noClash : ∀ var, (var, true) ∈ clause → (var, false) ∉ clause)
    (var : Nat) (pol : Bool) : polarityChoice clause var = some pol ↔ (var, pol) ∈ clause := by
  cases pol <;> by_cases positive : (var, true) ∈ clause
  · simp [polarityChoice, positive, noClash var positive]
  · simp [polarityChoice, positive]
  · simp [polarityChoice, positive]
  · simp [polarityChoice, positive]

theorem encodedKey_of_logicalKey {variables : Nat} {left right : StoredClause}
    (leftBound : ∀ lit ∈ left.lits, Representation.LiteralBound variables lit)
    (leftClash : Logic.ClauseSpace.NoClash (Analysis.viewedLiterals left.lits))
    (rightBound : ∀ lit ∈ right.lits, Representation.LiteralBound variables lit)
    (rightClash : Logic.ClauseSpace.NoClash (Analysis.viewedLiterals right.lits))
    (same : canonicalKey variables left.view = canonicalKey variables right.view) :
    Analysis.canonicalKey variables left.lits =
      Analysis.canonicalKey variables right.lits := by
  apply Logic.ClauseSpace.canonicalize_eq_of_relevant_mem_iff
  intro var bounded pol
  have noClashLeft : ∀ var, (var, true) ∈ left.view → (var, false) ∉ left.view := by
    simpa only [Representation.StoredClause.view, ← Std.Sat.CNF.Clause.mem_literals_iff, clauseView_literals,
      Logic.ClauseSpace.NoClash, Analysis.viewedLiterals] using leftClash
  have noClashRight : ∀ var, (var, true) ∈ right.view → (var, false) ∉ right.view := by
    simpa only [Representation.StoredClause.view, ← Std.Sat.CNF.Clause.mem_literals_iff, clauseView_literals,
      Logic.ClauseSpace.NoClash, Analysis.viewedLiterals] using rightClash
  have members : (var, pol) ∈ left.view ↔ (var, pol) ∈ right.view := by
    by_cases positive : 0 < var
    · have index : var - 1 < variables := by omega
      have entryEqual := congrArg (fun key : List (Option Bool) => key[var - 1]?) same
      have choice : polarityChoice left.view var = polarityChoice right.view var := by
        have choices : some (polarityChoice left.view var) = some (polarityChoice right.view var) := by
          simpa [canonicalKey, polarityChoice, List.getElem?_map, List.getElem?_range,
            index, show var - 1 + 1 = var by omega] using entryEqual
        exact Option.some.inj choices
      rw [← polarityChoice_eq_some noClashLeft var pol,
        ← polarityChoice_eq_some noClashRight var pol, choice]
    · have zero : var = 0 := by omega
      have absentLeft : (var, pol) ∉ left.view := by
        intro member
        obtain ⟨lit, contained, value⟩ := clauseView_mem.mp member
        have bound := leftBound lit contained
        have varEq := congrArg Prod.fst value
        change lit.var = var at varEq
        have positive := bound.1
        omega
      have absentRight : (var, pol) ∉ right.view := by
        intro member
        obtain ⟨lit, contained, value⟩ := clauseView_mem.mp member
        have bound := rightBound lit contained
        have varEq := congrArg Prod.fst value
        change lit.var = var at varEq
        have positive := bound.1
        omega
      simp [absentLeft, absentRight]
  simpa only [Representation.StoredClause.view, ← Std.Sat.CNF.Clause.mem_literals_iff, clauseView_literals,
    Analysis.viewedLiterals] using members

end MicrosatLean.Verification.Implementation.Bridge
