import MicrosatLean.Verification.Implementation.Initialization.Watches
import MicrosatLean.Verification.Implementation.Initialization.Reasons
import MicrosatLean.Verification.Implementation.Analysis.Freshness
import MicrosatLean.Verification.Implementation.Propagation.WatchInvariant

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Analysis Initialization Std.Sat

/-- The shared structural and semantic data at a public search boundary.
Decision history, propagation closure, and the watch cursor are phase-specific
obligations, rather than assumed consequences of this base certificate. -/
structure StateCertificate (formula : Std.Sat.CNF Nat) (s : State)
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

def HasStateCertificate (formula : Std.Sat.CNF Nat) (s : State) : Prop :=
  ∃ original learned heads rank, StateCertificate formula s original learned heads rank

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

end MicrosatLean.Verification.Implementation.Search.Concrete
