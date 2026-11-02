import MicrosatLean.Verification.Implementation.Logic.Trail

namespace MicrosatLean.Verification.Implementation.Logic

private theorem entails_stored {input : CNF} {a : LogicalState}
    (valid : SemanticInv input a) {clause : Clause} (member : clause ∈ a.database) :
    Std.Sat.CNF.EntailsClause input clause := by
  intro valuation model
  rcases List.mem_append.mp member with original | learned
  · exact (databaseView_sat_iff _ _).mp (valid.original.1 _ model) clause original
  · exact (databaseView_sat_iff _ _).mp (valid.learned _ model) clause learned

private theorem replace_database {input : CNF} {a : LogicalState}
    (valid : SemanticInv input a) (original learned : List Clause)
    (originalMeaning : Std.Sat.CNF.BiEntails input (databaseView original))
    (learnedMeaning : Std.Sat.CNF.Entails input (databaseView learned))
    (declared : ∀ clause ∈ original ++ learned, ∀ lit ∈ clause, LiteralBound a.numVars lit)
    (nonempty : ∀ clause ∈ original ++ learned, clause.literals ≠ []) :
    SemanticInv input { a with original := original, learned := learned } :=
  ⟨originalMeaning, learnedMeaning, valid.rootBound, valid.trailBound,
    valid.declaredTrail, valid.distinct, declared, nonempty, valid.reasons, valid.roots⟩

private theorem learn_preserves {input : CNF} {a : LogicalState}
    (valid : SemanticInv input a) (clause : Clause)
    (entailed : Std.Sat.CNF.EntailsClause input clause)
    (declared : ∀ lit ∈ clause, LiteralBound a.numVars lit)
    (nonempty : clause.literals ≠ []) :
    SemanticInv input { a with learned := a.learned ++ [clause] } := by
  apply replace_database valid a.original (a.learned ++ [clause]) valid.original
  · intro valuation model
    apply (databaseView_sat_iff _ _).mpr
    intro next member
    rcases List.mem_append.mp member with old | fresh
    · exact (databaseView_sat_iff _ _).mp (valid.learned _ model) next old
    · have same : next = clause := by simpa using fresh
      exact same ▸ entailed valuation model
  · intro next member lit contained
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | old | rfl
    · exact valid.declaredClauses next (List.mem_append_left _ old) lit contained
    · exact valid.declaredClauses next (List.mem_append_right _ old) lit contained
    · exact declared lit contained
  · intro next member
    simp only [List.mem_append, List.mem_singleton] at member
    rcases member with old | old | rfl
    · exact valid.nonempty next (List.mem_append_left _ old)
    · exact valid.nonempty next (List.mem_append_right _ old)
    · exact nonempty

private theorem forget_preserves {input : CNF} {a : LogicalState}
    (valid : SemanticInv input a) (retained : List Clause) (subset : retained ⊆ a.learned) :
    SemanticInv input { a with learned := retained } := by
  apply replace_database valid a.original retained valid.original
  · intro valuation model
    apply (databaseView_sat_iff _ _).mpr
    intro clause member
    exact (databaseView_sat_iff _ _).mp (valid.learned _ model) clause (subset member)
  · intro clause member
    apply valid.declaredClauses clause
    rcases List.mem_append.mp member with original | learned
    · exact List.mem_append_left _ original
    · exact List.mem_append_right _ (subset learned)
  · intro clause member
    apply valid.nonempty clause
    rcases List.mem_append.mp member with original | learned
    · exact List.mem_append_left _ original
    · exact List.mem_append_right _ (subset learned)

private theorem permutation_source {before after : List Clause}
    (permuted : ClausePermutations before after) {clause : Clause} (member : clause ∈ after) :
    ∃ old ∈ before, old.literals.Perm clause.literals := by
  induction before generalizing after with
  | nil => cases after <;> simp_all [ClausePermutations]
  | cons head rest ih =>
    cases after with
    | nil => simp at member
    | cons next remaining =>
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨head, by simp, permuted.1⟩
      · obtain ⟨old, contained, relation⟩ := ih permuted.2 later
        exact ⟨old, by simp [contained], relation⟩

private theorem permutations_symm {before after : List Clause}
    (permuted : ClausePermutations before after) : ClausePermutations after before := by
  induction before generalizing after with
  | nil => cases after <;> simp_all [ClausePermutations]
  | cons head rest ih =>
    cases after with
    | nil => simp_all [ClausePermutations]
    | cons next remaining => exact ⟨permuted.1.symm, ih permuted.2⟩

private theorem clause_permutation_sat {before after : Clause}
    (permuted : before.literals.Perm after.literals) (valuation : Assignment) :
    Std.Sat.CNF.Clause.Sat valuation before ↔ Std.Sat.CNF.Clause.Sat valuation after := by
  simp only [Std.Sat.CNF.Clause.sat_iff_exists_mem_eq,
    ← Std.Sat.CNF.Clause.mem_literals_iff, permuted.mem_iff]

private theorem permutations_sat {before after : List Clause}
    (permuted : ClausePermutations before after) (valuation : Assignment) :
    Std.Sat.CNF.Sat valuation (databaseView before) ↔
      Std.Sat.CNF.Sat valuation (databaseView after) := by
  simp only [databaseView_sat_iff]
  constructor
  · intro satisfied clause member
    obtain ⟨old, contained, relation⟩ := permutation_source permuted member
    exact (clause_permutation_sat relation valuation).mp (satisfied old contained)
  · intro satisfied clause member
    obtain ⟨old, contained, relation⟩ := permutation_source (permutations_symm permuted) member
    exact (clause_permutation_sat relation valuation).mp (satisfied old contained)

private theorem permute_preserves {input : CNF} {a : LogicalState}
    (valid : SemanticInv input a) (original learned : List Clause)
    (originals : ClausePermutations a.original original)
    (lemmas : ClausePermutations a.learned learned) :
    SemanticInv input { a with original := original, learned := learned } := by
  have source : ∀ clause ∈ original ++ learned, ∃ old ∈ a.database,
      old.literals.Perm clause.literals := by
    intro clause member
    rcases List.mem_append.mp member with fromOriginal | fromLearned
    · obtain ⟨old, contained, relation⟩ := permutation_source originals fromOriginal
      exact ⟨old, List.mem_append_left _ contained, relation⟩
    · obtain ⟨old, contained, relation⟩ := permutation_source lemmas fromLearned
      exact ⟨old, List.mem_append_right _ contained, relation⟩
  apply replace_database valid original learned
  · exact ⟨fun valuation model => (permutations_sat originals valuation).mp (valid.original.1 _ model),
      fun valuation model => valid.original.2 _ ((permutations_sat originals valuation).mpr model)⟩
  · exact fun valuation model => (permutations_sat lemmas valuation).mp (valid.learned _ model)
  · intro clause member lit contained
    obtain ⟨old, oldMember, relation⟩ := source clause member
    apply valid.declaredClauses old oldMember lit
    exact Std.Sat.CNF.Clause.mem_literals_iff.mp
      (relation.mem_iff.mpr (Std.Sat.CNF.Clause.mem_literals_iff.mpr contained))
  · intro clause member empty
    obtain ⟨old, oldMember, relation⟩ := source clause member
    have length := relation.length_eq
    rw [empty, List.length_nil] at length
    exact valid.nonempty old oldMember (List.length_eq_zero_iff.mp length)

/-- Every admissible logical move preserves the semantic invariant.
Concrete state/control preservation remains a separate implementation task. -/
theorem logical_moves : LogicalSoundness := by
  intro input before after valid move
  cases move with
  | decide lit declared fresh closed =>
    exact append_preserves valid ⟨lit, none⟩ declared fresh (by simp)
  | propagate clause lit stored head fresh tails =>
    have member : lit ∈ clause := Std.Sat.CNF.Clause.mem_literals_iff.mp
      (List.mem_of_head? head)
    exact append_preserves valid ⟨lit, some clause⟩ (valid.declaredClauses _ stored _ member)
      fresh (by intro next equal; cases equal; exact ⟨entails_stored valid stored, head, tails⟩)
  | learn clause entailed declared nonempty =>
    exact learn_preserves valid clause entailed declared nonempty
  | backjump keep roots active => exact take_preserves valid roots active
  | restart => exact take_preserves valid (Nat.le_refl _) valid.rootBound
  | forget retained subset reasons => exact forget_preserves valid retained subset
  | permute original learned originals lemmas =>
    exact permute_preserves valid original learned originals lemmas
  | commitRoots count lower upper sound =>
    exact ⟨valid.original, valid.learned, upper, valid.trailBound, valid.declaredTrail,
      valid.distinct, valid.declaredClauses, valid.nonempty, valid.reasons, sound⟩

end MicrosatLean.Verification.Implementation.Logic
