import MicrosatLean.Verification.Initialization.Watches
import MicrosatLean.Verification.Initialization.Reasons
import MicrosatLean.Verification.Analysis.Freshness
import MicrosatLean.Verification.Propagation.WatchInvariant

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Initialization Std.Sat

/-- The shared structural and semantic data at a public search boundary.
Decision history, propagation closure, and the watch cursor are phase-specific
obligations, rather than assumed consequences of this base certificate. -/
structure StateCertificate (formula : CNF Nat) (s : State)
    (original learned : List StoredClause) (heads : Nat → List Nat) (rank : Lit → Nat) : Prop where
  arrays : ArrayBounds s
  bounds : TrailBounds s
  active : ActiveTrail s
  distinct : DistinctTrailVariables s
  phases : TrailPhases s
  marked : MarkedOnTrail s
  order : MTFCoverage s
  database : Database s original learned
  meaning : DatabaseMeaning formula original learned
  reasons : ReasonDatabase s (original ++ learned)
  graph : ReasonGraph formula s s.assigned rank
  watches : WatchCertificate s (original ++ learned) heads
  nonempty : ∀ entry ∈ original ++ learned, 0 < entry.lits.size
  nodup : ∀ entry ∈ original ++ learned, entry.lits.toList.Nodup
  noClash : ∀ entry ∈ original ++ learned, Logic.ClauseSpace.NoClash (viewedLiterals entry.lits)
  learnedDistinct : (learned.map fun entry => canonicalKey s.nVars entry.lits).Nodup
  tags : ValidMarkTags s s.assigned s
  roots : RootTagConsequences formula s s.assigned s
  rootPrefix : ∀ i, i < s.forced → s.mark s.trail[i]! = 6

def HasStateCertificate (formula : CNF Nat) (s : State) : Prop :=
  ∃ original learned heads rank, StateCertificate formula s original learned heads rank

/-- Cursor bookkeeping retains the shared data; a larger root prefix must
be justified by the propagation phase's concrete root-tag facts. -/
theorem StateCertificate.setCursors {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (processed forced : Nat) (rootBound : forced ≤ processed) (trailBound : processed ≤ s.assigned)
    (rootTags : ∀ i, i < forced → s.mark s.trail[i]! = 6) :
    StateCertificate formula { s with processed := processed, forced := forced }
      original learned heads rank := by
  refine ⟨?_, ⟨rootBound, trailBound, certificate.bounds.assignedVars⟩,
    certificate.active, certificate.distinct, certificate.phases, certificate.marked,
    certificate.order, certificate.database.frame rfl rfl rfl rfl, certificate.meaning,
    certificate.reasons, certificate.graph.frame rfl rfl rfl rfl, ?_, certificate.nonempty,
    certificate.nodup, certificate.noClash, certificate.learnedDistinct, certificate.tags,
    certificate.roots, rootTags⟩
  · exact ⟨certificate.arrays.firstSize, certificate.arrays.marksSize,
      certificate.arrays.reasonsSize, certificate.arrays.phasesSize, certificate.arrays.trailSize,
      certificate.arrays.previousSize, certificate.arrays.nextSize⟩
  · exact ⟨certificate.watches.links, certificate.watches.references,
      certificate.watches.covered, certificate.watches.unique⟩

theorem StateCertificate.processNext {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (pending : s.processed < s.assigned) :
    StateCertificate formula { s with processed := s.processed + 1 }
      original learned heads rank := by
  exact certificate.setCursors (s.processed + 1) s.forced
    (Nat.le_trans certificate.bounds.forcedProcessed (Nat.le_add_right _ _))
    (by omega) certificate.rootPrefix

theorem StateCertificate.finishRootPropagation {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (rootTags : ∀ i, i < s.processed → s.mark s.trail[i]! = 6) :
    StateCertificate formula { s with forced := s.processed } original learned heads rank :=
  certificate.setCursors s.processed s.processed (Nat.le_refl _)
    certificate.bounds.processedAssigned rootTags

theorem initialWatchCertificate {s : State} {original : List StoredClause} {heads : Nat → List Nat}
    (watched : InitialWatchState s original heads) : WatchCertificate s original heads := by
  constructor
  · intro lit
    have list := watched.lists lit
    exact ⟨list.1, list.2.1, fun i before => (list.2.2 i before).2⟩
  · intro lit ref member
    obtain ⟨entry, stored, long, source⟩ := watched.references lit ref member
    refine ⟨entry, stored, ?_, by omega⟩
    unfold watchClause
    rcases source with first | second <;> omega
  · intro entry member wide
    exact watched.covered entry member (by omega)
  · exact watched.unique

/-- A complete base certificate follows from the actual initializer. All
database, watch, and proper-reason facts share the same original-entry witness. -/
theorem initState_some_certificate {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (success : initState formula config = .ok (some s)) :
    HasStateCertificate (formulaView formula) s := by
  obtain ⟨original, heads, database, meaning, watched, proper⟩ := initState_some_watchReasons wellFormed success
  have valid := initState_some_representation wellFormed success
  have data := initState_some_analysisData wellFormed success
  refine ⟨original, [], heads, initialTrailRank s, valid.arrays, valid.bounds, valid.active,
    valid.distinct, valid.phases, valid.marked, valid.order, database, meaning, ?_,
    initState_some_reasonGraph wellFormed success, ?_, ?_, ?_, ?_, by simp, ?_,
    initState_some_rootTagConsequences wellFormed success, ?_⟩
  · simpa only [List.append_nil] using proper
  · simpa only [List.append_nil] using initialWatchCertificate watched
  · simpa only [List.append_nil] using watched.nonempty
  · simpa only [List.append_nil] using watched.nodup
  · simpa only [List.append_nil, viewedLiterals] using watched.noClash
  · intro lit _
    rcases data.tags lit with zero | six
    · exact Or.inl zero
    · exact Or.inr (Or.inr (Or.inr (Or.inr six)))
  · intro i before
    have active : i < s.assigned := by
      have := valid.bounds.forcedProcessed
      have := valid.bounds.processedAssigned
      omega
    rcases data.tags s.trail[i]! with zero | six
    · exact False.elim ((valid.active i active).2.1 zero)
    · exact six

theorem initState_certificate {formula : Formula} (wellFormed : WellFormed formula) (config : Config) :
    ∃ result, initState formula config = .ok result ∧
      match result with
      | none => CNF.Unsat (formulaView formula)
      | some s => HasStateCertificate (formulaView formula) s := by
  obtain ⟨result, initialized, outcome⟩ := initState_outcome wellFormed config
  refine ⟨result, initialized, ?_⟩
  cases result with
  | none => exact outcome
  | some s => exact initState_some_certificate wellFormed initialized

end MicrosatLean.Verification.Search
