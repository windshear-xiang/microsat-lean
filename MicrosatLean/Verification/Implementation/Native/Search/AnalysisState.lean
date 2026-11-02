import MicrosatLean.Verification.Implementation.Native.Search.AnalysisEntry
import MicrosatLean.Verification.Implementation.Native.Search.Assignment
import MicrosatLean.Verification.Implementation.Native.Analysis.AnalyzerFacts
import MicrosatLean.Verification.Implementation.Native.Analysis.RootTags
import MicrosatLean.Verification.Implementation.Native.Analysis.Order
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchAllocation
import MicrosatLean.Verification.Implementation.Native.Search.AnalysisProgress

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Initialization Std.Sat

/-- Ghost heads installed by the real analyzer's final allocator. -/
def analysisHeads (s : State) (conflict : Nat) (heads : Nat → List Nat) : Nat → List Nat :=
  allocatedHeads (analysisBeforeStore s conflict) heads (analysisLearned s conflict)

/-- Actual resolution and minimization retain the old watch storage; the
actual final allocation installs both slots of its proved distinct learned
clause. No coverage of the analyzer's output is assumed. -/
theorem StateCertificate.analyze_watches {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (certificate : StateCertificate formula s original learned heads rank)
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    WatchCertificate (CDCL.analyze s conflict).1
      (original ++ (learned ++ [⟨(CDCL.analyze s conflict).2, analysisLearned s conflict⟩]))
      (analysisHeads s conflict heads) := by
  let before := analysisBeforeStore s conflict
  have beforeDatabase : Database before original learned := certificate.database.frame
    (analysisBeforeStore_arena _ _) (analysisBeforeStore_nVars _ _)
    (analysisBeforeStore_fixed _ _) (analysisBeforeStore_nLemmas _ _)
  have beforeWatch : WatchCertificate before (original ++ learned) heads :=
    certificate.watches.frameArrays (analysisBeforeStore_arena _ _) (analysisBeforeStore_first _ _)
  have reserved : 2 ≤ before.arena.size := by
    have := beforeDatabase.layout.size
    omega
  have semantic := entry.semantic.learned_sound
  have bounded : ∀ lit ∈ analysisLearned s conflict, LiteralBound before.nVars lit := by
    simpa only [before, analysisBeforeStore_nVars] using semantic.2
  have noDuplicates := analyze_learned_nodup entry.decisionEntry
  have allocated := WatchCertificate.addClause beforeDatabase beforeWatch (analysisLearned s conflict)
    false (analysisBeforeStore_arrayBounds certificate.arrays conflict) reserved bounded
    (normalized_first_two_ne noDuplicates)
  simpa only [analyze_eq_addClause, analysisHeads, List.append_assoc, before] using allocated

theorem StateCertificate.analyze_reasons {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (certificate : StateCertificate formula s original learned heads rank)
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    ReasonDatabase (CDCL.analyze s conflict).1
      (original ++ (learned ++ [⟨(CDCL.analyze s conflict).2, analysisLearned s conflict⟩])) := by
  have proper := (certificate.reasons.prefix (Nat.le_of_lt (analyze_assigned_lt entry.decisionEntry))).frame
    (analyze_trail s conflict) (Analysis.analyze_reasons s conflict)
  exact proper.mono (by intro old member; exact List.mem_append.mpr (by
    rcases List.mem_append.mp member with original | learned
    · exact Or.inl original
    · exact Or.inr (List.mem_append_left _ learned)))

/-- The runtime's next-cell zero test detects precisely a singleton learned
clause, because every genuine literal cell is a declared nonzero literal. -/
theorem analyze_root_iff_unit {formula : CNF Nat} {s : State}
    {conflict decision : Nat} {lits : Array Lit} {rank : Lit → Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    ((CDCL.analyze s conflict).1.db ((CDCL.analyze s conflict).2 + 1) == 0) = true ↔
      (analysisLearned s conflict).size = 1 := by
  have ready := entry.ready
  constructor
  · intro zero
    have zero' : (CDCL.analyze s conflict).1.db ((CDCL.analyze s conflict).2 + 1) = 0 := by
      simpa only [beq_iff_eq] using zero
    by_cases unit : (analysisLearned s conflict).size = 1
    · exact unit
    · have many : 1 < (analysisLearned s conflict).size := by have := ready.nonempty; omega
      have member : (analysisLearned s conflict)[1]! ∈ analysisLearned s conflict := by
        simpa only [getElem!_pos (analysisLearned s conflict) 1 many] using Array.getElem_mem many
      have nonzero := (ready.packed.wellFormed _ member).nonzero
      exact False.elim (nonzero ((ready.packed.literals 1 many).symm.trans zero'))
  · intro unit
    apply beq_iff_eq.mpr
    simpa only [unit] using ready.packed.terminator

theorem analyze_root_assertion {formula : CNF Nat} {s : State}
    {conflict decision : Nat} {lits : Array Lit} {rank : Lit → Nat}
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision)
    (root : ((CDCL.analyze s conflict).1.db ((CDCL.analyze s conflict).2 + 1) == 0) = true) :
    ∀ a, CNF.Sat a formula →
      Falsifies a (Lit.negate ((CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2)) := by
  have ready := entry.ready
  have unit := (analyze_root_iff_unit entry).mp root
  intro a model
  apply (falsifies_negate_iff a _).mpr
  have head : (CDCL.analyze s conflict).1.db (CDCL.analyze s conflict).2 = (analysisLearned s conflict)[0]! := by
    simpa only [Nat.add_zero] using ready.packed.literals 0 ready.nonempty
  obtain ⟨lit, member, value⟩ := (clauseView_sat_iff _ _).mp (ready.entailed a model)
  obtain ⟨i, bound, equal⟩ := Array.mem_iff_getElem.mp member
  have first : i = 0 := by omega
  subst i
  have same : (analysisLearned s conflict)[0]! = lit := by
    simpa only [getElem!_pos (analysisLearned s conflict) 0 ready.nonempty] using equal
  simpa only [head, same, literalView] using value

/-- Complete base-certificate preservation for the actual analyzer. Saved
decision prefixes prove freshness; cleanup proves output tags; allocation
proves genuine watch and reason ownership. All output fields are conclusions. -/
theorem StateCertificate.analyze {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned))
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    ∃ nextRank, StateCertificate formula (CDCL.analyze s conflict).1 original
      (learned ++ [⟨(CDCL.analyze s conflict).2, analysisLearned s conflict⟩])
      (analysisHeads s conflict heads) nextRank := by
  let added : StoredClause := ⟨(CDCL.analyze s conflict).2, analysisLearned s conflict⟩
  have ready := entry.ready
  have stored := analyze_database_meaning entry.semantic certificate.database certificate.meaning
  have decisionEntry := entry.decisionEntry
  obtain ⟨nextRank, nextGraph⟩ := ready.graph
  refine ⟨nextRank, ready.arrays, ready.bounds, ready.active, ready.distinct, ready.phases,
    ready.marked, entry.semantic.analyze_mtf certificate.order, stored.1, stored.2,
    certificate.analyze_reasons entry, nextGraph, certificate.analyze_watches entry,
    ?_, ?_, ?_, ?_, analyze_validMarkTags decisionEntry,
    analyze_rootTagConsequences decisionEntry, analyze_rootPrefix decisionEntry⟩
  · intro old member
    rw [← List.append_assoc] at member
    rcases List.mem_append.mp member with oldMember | newMember
    · exact certificate.nonempty old oldMember
    · have same : old = added := List.mem_singleton.mp newMember
      simpa only [same, added] using ready.nonempty
  · intro old member
    rw [← List.append_assoc] at member
    rcases List.mem_append.mp member with oldMember | newMember
    · exact certificate.nodup old oldMember
    · have same : old = added := List.mem_singleton.mp newMember
      simpa only [same, added] using analyze_learned_nodup decisionEntry
  · intro old member
    rw [← List.append_assoc] at member
    rcases List.mem_append.mp member with oldMember | newMember
    · exact certificate.noClash old oldMember
    · have same : old = added := List.mem_singleton.mp newMember
      simpa only [same, added] using decisionEntry.learned_shape.noClash
  · have origins := DecisionHistory.origins history decision entry.forcedBefore
      entry.block.before entry.block.decisionReason
    simpa only [analyze_nVars] using analyze_canonical_distinct decisionEntry certificate.database
      origins certificate.noClash certificate.learnedDistinct

/-- The actual analyzer followed by its actual root-flag test and asserting
assignment preserves the complete base certificate. A singleton assertion's
root consequence is derived from the proved learned-clause entailment. -/
theorem StateCertificate.analyze_assign {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned))
    (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    let result := CDCL.analyze s conflict
    let root := result.1.db (result.2 + 1) == 0
    HasStateCertificate formula (result.1.assign result.2 root) := by
  dsimp only
  obtain ⟨nextRank, next⟩ := certificate.analyze history entry
  let added : StoredClause := ⟨(CDCL.analyze s conflict).2, analysisLearned s conflict⟩
  have member : added ∈ original ++ (learned ++ [added]) := by simp
  have ready := entry.ready
  exact ⟨original, learned ++ [added], analysisHeads s conflict heads, _,
    next.assign added member ready.nonempty ready.tails ready.head ready.opposite _
      (analyze_root_assertion entry)⟩

end MicrosatLean.Verification.Implementation.Native.Search
