import MicrosatLean.Verification.Implementation.Search.Concrete.StateCertificate
import MicrosatLean.Verification.Implementation.Analysis.MarkCleanup

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Analysis Propagation Std.Sat

/-- Concrete data carried by a nonroot propagation phase: an actual decision
below each nonroot assignment and six tags confined to the root prefix.
Neither reason-parent dependencies nor conflict/UIP properties are fields. -/
structure NonrootPhase (s : State) : Prop where
  levels : LevelCover s
  caches : SixBefore s
  nonroot : s.forced < s.assigned

/-- The base state, saved closed decision prefixes, and a genuine all-false
clause establish every analyzer entry gate. In particular the nearest
decision, same-level reason parent, and current conflict literal are derived. -/
theorem StateCertificate.analysisTransitionEntry {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned)) (phase : NonrootPhase s)
    {conflict : StoredClause} (member : conflict ∈ original ++ learned)
    (falseClause : ∀ lit ∈ conflict.lits, s.mark lit ≠ 0) :
    ∃ decision, AnalysisTransitionEntry formula s conflict.id conflict.lits rank decision := by
  obtain ⟨decision, lower, block⟩ := phase.levels.currentBlock phase.nonroot
  have covered : ∀ lit ∈ conflict.lits, TrailMember s s.assigned lit :=
    fun lit contains => certificate.marked lit (falseClause lit contains)
  have parents := DecisionHistory.reasonLevelParent history certificate.graph certificate.reasons
    (fun entry member => certificate.database.layout.packed member)
    decision lower block.before block.decisionReason
  have current := DecisionHistory.conflict_in_level history certificate.active decision lower block.before
    block.decisionReason member (certificate.nonempty conflict member) covered
  have earlier : ∀ i, i < s.assigned → s.mark s.trail[i]! = 6 → i < decision := by
    intro i before six
    exact Nat.lt_of_lt_of_le (phase.caches i before six) lower
  refine ⟨decision, ⟨?_, certificate.bounds, certificate.phases, certificate.marked,
    block, parents, lower, earlier, ?_⟩⟩
  · exact ⟨certificate.graph, certificate.arrays, certificate.active, by have := phase.nonroot; omega,
      certificate.database.layout.packed member, covered, certificate.meaning.entails_entry member,
      certificate.tags, certificate.roots, fun i bound _ => certificate.rootPrefix i bound⟩
  · obtain ⟨i, current, before, contains⟩ := current
    refine ⟨i, current, before, contains, ?_⟩
    intro six
    have old := earlier i before six
    omega

theorem NonrootPhase.assign {s : State} (phase : NonrootPhase s) (id : Nat)
    (space : s.assigned < s.trail.size) (markBound : Lit.negate (s.db id) < s.marks.size)
    (fresh : FreshVariable s (Lit.var (s.db id))) : NonrootPhase (s.assign id false) := by
  refine ⟨phase.levels.assign id false phase.nonroot fresh,
    phase.caches.assign_false id space markBound, ?_⟩
  change s.forced < s.assigned + 1
  have := phase.nonroot
  omega

theorem nonrootPhase_decide {s : State} (cover : LevelCover s) (caches : SixBefore s)
    (var : Nat) (root : s.forced ≤ s.assigned) (space : s.assigned < s.trail.size)
    (reasonBound : var < s.reasons.size) (markBound : (decisionLiteral s var).negate < s.marks.size)
    (fresh : FreshVariable s var) : NonrootPhase (s.decide var) := by
  refine ⟨cover.decide var root space reasonBound fresh, caches.decide var space markBound, ?_⟩
  change s.forced < s.assigned + 1
  omega

/-- Actual analysis, backjump, and the subsequent nonroot assertion restore
the concrete phase data; transient minimization caches have been cleaned. -/
theorem NonrootPhase.analyze_assign {formula : Std.Sat.CNF Nat} {s : State} {conflict decision : Nat}
    {lits : Array Lit} {rank : Lit → Nat} (phase : NonrootPhase s)
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision)
    (many : 1 < (analysisLearned s conflict).size) :
    NonrootPhase ((CDCL.analyze s conflict).1.assign (CDCL.analyze s conflict).2 false) := by
  have after : NonrootPhase (CDCL.analyze s conflict).1 :=
    ⟨phase.levels.analyze entry.decisionEntry, SixBefore.analyze entry.decisionEntry,
      analyze_nonroot_prefix entry.decisionEntry many⟩
  have ready := entry.ready
  have fresh := freshVariable_of_unmarked_literal ready.active ready.head ready.opposite
  have first : (CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2 = (analysisLearned s conflict)[0]! := by
    simpa using ready.packed.literals 0 ready.nonempty
  have member : (CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2 ∈ analysisLearned s conflict := by
    rw [first, getElem!_pos _ 0 ready.nonempty]
    exact Array.getElem_mem ready.nonempty
  have literal := ready.packed.wellFormed _ member
  have room := assigned_lt_of_fresh ready.active ready.distinct fresh literal.1 literal.2
  apply after.assign (CDCL.analyze s conflict).2
  · rw [ready.arrays.trailSize]
    omega
  · exact (ready.arrays.literal_index literal.negate).1
  · exact fresh

end MicrosatLean.Verification.Implementation.Search.Concrete
