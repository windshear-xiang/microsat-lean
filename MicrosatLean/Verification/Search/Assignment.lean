import MicrosatLean.Verification.Search.StateCertificate
import MicrosatLean.Verification.Search.Decision
import MicrosatLean.Verification.Analysis.ReasonUpdates

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Std.Sat

theorem StateCertificate.learnedCount_bound {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank) :
    s.nLemmas ≤ 3 ^ s.nVars :=
  certificate.database.learnedCount_le certificate.learnedDistinct

/-- The concrete phase-saving decision preserves all base data. The two
unmarked tests supply freshness, trail capacity, and the new reason-free node. -/
theorem StateCertificate.decide {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (var : Nat) (lower : 1 ≤ var) (upper : var ≤ s.nVars)
    (positive : s.mark (2 * var) = 0) (negative : s.mark (2 * var + 1) = 0) :
    StateCertificate formula (s.decide var) original learned heads
      (extendTrailRank rank var s.assigned) := by
  have fresh := freshVariable_of_unmarked certificate.active positive negative
  have room := assigned_lt_of_fresh certificate.active certificate.distinct fresh lower upper
  have space : s.assigned < s.trail.size := by rw [certificate.arrays.trailSize]; omega
  have literal := decisionLiteral_bound lower upper (s := s)
  have unset : s.mark (decisionLiteral s var) = 0 := by
    unfold decisionLiteral
    split <;> simp_all only [Nat.add_zero]
  have prefixMark (i : Nat) (before : i < s.assigned) :
      (s.decide var).mark s.trail[i]! = s.mark s.trail[i]! :=
    decide_mark_other (fresh.ne_literal before (by simp))
  refine ⟨certificate.arrays.decide, certificate.bounds.decide room,
    certificate.active.decide certificate.arrays lower upper space fresh unset,
    certificate.distinct.decide fresh space, certificate.phases.decide space,
    certificate.marked.decide space, certificate.order.decide var,
    certificate.database.frame rfl rfl rfl rfl, certificate.meaning,
    certificate.reasons.decide certificate.arrays certificate.active certificate.distinct
      lower upper positive negative,
    certificate.graph.decide certificate.arrays certificate.active lower upper positive negative,
    WatchCertificate.frameArrays certificate.watches rfl rfl, certificate.nonempty, certificate.nodup,
    certificate.noClash, certificate.learnedDistinct, ?_, ?_, ?_⟩
  · rintro lit ⟨i, before, rfl⟩
    have bound : i < s.assigned + 1 := before
    by_cases last : i = s.assigned
    · subst i
      rw [decide_trail_last space]
      have one : (s.decide var).mark (decisionLiteral s var).negate = 1 :=
        Array.getElem!_set!_self _ _ _ (certificate.arrays.literal_index literal.negate).1
      exact Or.inr (Or.inl one)
    · have earlier : i < s.assigned := by omega
      rw [decide_trail_prefix earlier, prefixMark i earlier]
      exact certificate.tags _ ⟨i, earlier, rfl⟩
  · rintro lit ⟨i, before, rfl⟩ six
    have bound : i < s.assigned + 1 := before
    by_cases last : i = s.assigned
    · subst i
      rw [decide_trail_last space] at six
      have one : (s.decide var).mark (decisionLiteral s var).negate = 1 :=
        Array.getElem!_set!_self _ _ _ (certificate.arrays.literal_index literal.negate).1
      omega
    · have earlier : i < s.assigned := by omega
      rw [decide_trail_prefix earlier, prefixMark i earlier] at six
      rw [decide_trail_prefix earlier]
      exact certificate.roots _ ⟨i, earlier, rfl⟩ six
  · intro i before
    have earlier : i < s.assigned := by
      have := certificate.bounds.forcedProcessed
      have := certificate.bounds.processedAssigned
      change i < s.forced at before
      omega
    rw [decide_trail_prefix earlier, prefixMark i earlier]
    exact certificate.rootPrefix i before

/-- The actual decision scan discharges both freshness tests and declaration
bounds, so selecting a nonzero variable preserves the complete base certificate. -/
theorem StateCertificate.nextDecision {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank) (cursor : Nat)
    (valid : cursor = 0 ∨ (1 ≤ cursor ∧ cursor ≤ s.nVars))
    (nonzero : nextDecision s cursor ≠ 0) :
    StateCertificate formula (s.decide (nextDecision s cursor)) original learned heads
      (extendTrailRank rank (nextDecision s cursor) s.assigned) := by
  obtain ⟨order, ordered⟩ := certificate.order
  have member : cursor ∈ order ∨ cursor = 0 := by
    rcases valid with zero | declared
    · exact Or.inr zero
    · exact Or.inl ((ordered.2.1 cursor).mpr declared)
  have declared := (ordered.2.1 _).mp
    (nextDecisionScan_mem_of_nonzero ordered (s.nVars + 1) cursor member nonzero)
  have unset := nextDecisionScan_nonzero_unassigned (s.nVars + 1) s cursor nonzero
  exact certificate.decide _ declared.1 declared.2 unset.1 unset.2

/-- A real unit append preserves the complete base certificate. The root
flag additionally requires the semantic root consequence supplied by its
propagation phase; ordinary nonroot appends have no such requirement. -/
theorem StateCertificate.assign {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (entry : StoredClause) (member : entry ∈ original ++ learned)
    (nonempty : 0 < entry.lits.size)
    (tails : ∀ j, 0 < j → j < entry.lits.size → TrailMember s s.assigned entry.lits[j]!)
    (head : s.mark (s.db entry.id) = 0) (opposite : s.mark (Lit.negate (s.db entry.id)) = 0)
    (root : Bool)
    (rootSound : root = true → ∀ a, CNF.Sat a formula → Falsifies a (Lit.negate (s.db entry.id))) :
    StateCertificate formula (s.assign entry.id root) original learned heads
      (extendTrailRank rank (Lit.var (s.db entry.id)) s.assigned) := by
  have packed := certificate.database.layout.packed member
  have first : s.db entry.id = entry.lits[0]! := by simpa using packed.literals 0 nonempty
  have headMember : s.db entry.id ∈ entry.lits := by
    rw [first, getElem!_pos entry.lits 0 nonempty]
    exact Array.getElem_mem nonempty
  have literal := packed.wellFormed _ headMember
  have fresh := freshVariable_of_unmarked_literal certificate.active head opposite
  have room := assigned_lt_of_fresh certificate.active certificate.distinct fresh literal.1 literal.2
  have space : s.assigned < s.trail.size := by rw [certificate.arrays.trailSize]; omega
  have prefixMark (i : Nat) (before : i < s.assigned) :
      (s.assign entry.id root).mark s.trail[i]! = s.mark s.trail[i]! :=
    assign_mark_other (fresh.ne_literal before (negate_var _))
  have newMark : (s.assign entry.id root).mark (Lit.negate (s.db entry.id)) = if root then 6 else 1 :=
    Array.getElem!_set!_self _ _ _ (certificate.arrays.literal_index literal.negate).1
  refine ⟨certificate.arrays.assign, certificate.bounds.assign room,
    certificate.active.assign certificate.arrays literal space fresh head,
    certificate.distinct.assign fresh space, certificate.phases.assign certificate.arrays literal space fresh,
    certificate.marked.assign space, certificate.order.assign entry.id root,
    certificate.database.frame rfl rfl rfl rfl, certificate.meaning,
    certificate.reasons.assign member root certificate.arrays certificate.active certificate.distinct
      literal head opposite,
    certificate.graph.assign certificate.arrays certificate.active packed nonempty
      (certificate.meaning.entails_entry member) tails head opposite root,
    WatchCertificate.frameArrays certificate.watches rfl rfl, certificate.nonempty, certificate.nodup,
    certificate.noClash, certificate.learnedDistinct, ?_, ?_, ?_⟩
  · rintro lit ⟨i, before, rfl⟩
    have bound : i < s.assigned + 1 := before
    by_cases last : i = s.assigned
    · subst i
      rw [assign_trail_last space, newMark]
      cases root <;> simp
    · have earlier : i < s.assigned := by omega
      rw [assign_trail_prefix earlier, prefixMark i earlier]
      exact certificate.tags _ ⟨i, earlier, rfl⟩
  · rintro lit ⟨i, before, rfl⟩ six
    have bound : i < s.assigned + 1 := before
    by_cases last : i = s.assigned
    · subst i
      rw [assign_trail_last space, newMark] at six
      have isRoot : root = true := by cases root <;> simp_all
      rw [assign_trail_last space]
      exact rootSound isRoot
    · have earlier : i < s.assigned := by omega
      rw [assign_trail_prefix earlier, prefixMark i earlier] at six
      rw [assign_trail_prefix earlier]
      exact certificate.roots _ ⟨i, earlier, rfl⟩ six
  · intro i before
    have earlier : i < s.assigned := by
      have := certificate.bounds.forcedProcessed
      have := certificate.bounds.processedAssigned
      change i < s.forced at before
      omega
    rw [assign_trail_prefix earlier, prefixMark i earlier]
    exact certificate.rootPrefix i before

end MicrosatLean.Verification.Search
