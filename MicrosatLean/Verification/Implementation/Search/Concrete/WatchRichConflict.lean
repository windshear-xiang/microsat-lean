import MicrosatLean.Verification.Implementation.Search.Concrete.WatchScan
import MicrosatLean.Verification.Implementation.Search.Concrete.PropagationMode
import MicrosatLean.Verification.Implementation.Search.Concrete.WatchConflictState
import MicrosatLean.Verification.Implementation.Propagation.WatchConflict
import MicrosatLean.Verification.Implementation.Search.Concrete.AnalysisSettlement
import MicrosatLean.Verification.Implementation.Propagation.WatchIdentity

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Analysis Std.Sat

theorem WatchScanFacts.skip {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {count : Nat} {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (facts : WatchScanFacts formula s original learned heads rank count lit previous (ref :: rest))
    (falseLit : s.mark lit ≠ 0)
    (truth : s.mark (Lit.negate ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!)) ≠ 0) :
    let after := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    ∃ nextOriginal nextLearned,
      WatchScanFacts formula after nextOriginal nextLearned heads rank count lit ref rest := by
  dsimp only
  obtain ⟨nextOriginal, nextLearned, oriented⟩ := facts.orient falseLit
  obtain ⟨settledOriginal, settledLearned, database, _, _, _, cursor, _, visited⟩ :=
    skip_branch_settlement facts.base.database facts.base.meaning facts.base.watches facts.base.nodup facts.base.marked
      facts.cursor facts.prefixSettled facts.visited truth
  obtain ⟨sameOriginal, sameLearned⟩ := database.unique oriented.base.database
  subst settledOriginal settledLearned
  exact ⟨nextOriginal, nextLearned, oriented.base, oriented.history, oriented.saved, oriented.units,
    oriented.bound, oriented.prefixSettled, visited, cursor⟩

theorem WatchScanFacts.unit {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {count : Nat} {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (facts : WatchScanFacts formula s original learned heads rank count lit previous (ref :: rest))
    (falseLit : s.mark lit ≠ 0) (root : Bool) (rootTrail : RootWatchTrail s root)
    (missing : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = none)
    (head : s.mark ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!) = 0)
    (opposite : s.mark (Lit.negate ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!)) = 0) :
    let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    let after := retained.assign (watchClause ref) root
    ∃ nextOriginal nextLearned nextRank,
      WatchScanFacts formula after nextOriginal nextLearned heads nextRank count lit ref rest := by
  dsimp only
  obtain ⟨nextOriginal, nextLearned, nextRank, nextBase, nextHistory⟩ :=
    facts.base.watchUnit facts.cursor.member falseLit root rootTrail missing head opposite
  obtain ⟨savedOriginal, savedLearned, _, savedBase, nextSaved⟩ :=
    facts.base.watchUnit_saved facts.cursor.member falseLit root rootTrail missing head opposite
  obtain ⟨sameOriginal, sameLearned⟩ := savedBase.database.unique nextBase.database
  subst savedOriginal savedLearned
  have space : s.assigned < s.trail.size := by
    rw [facts.base.arrays.trailSize]
    have assigned := facts.base.bounds.assignedVars
    omega
  obtain ⟨settledOriginal, settledLearned, settledDatabase, _, _, _, cursor, prefixSettled, visited⟩ :=
    unit_branch_settlement facts.base.database facts.base.meaning facts.base.watches facts.base.nodup facts.bound
      facts.cursor facts.prefixSettled facts.visited root space
  obtain ⟨sameOriginal, sameLearned⟩ := settledDatabase.unique nextBase.database
  subst settledOriginal settledLearned
  obtain ⟨retainedOriginal, retainedLearned, oriented⟩ := facts.orient falseLit
  have units := units_assign oriented.units (watchClause ref) root
  obtain ⟨sameOriginal, sameLearned⟩ := (oriented.base.database.assign (watchClause ref) root).unique nextBase.database
  subst retainedOriginal retainedLearned
  refine ⟨nextOriginal, nextLearned, nextRank, nextBase, nextHistory facts.history, nextSaved facts.saved,
    units, ?_, prefixSettled, visited, cursor⟩
  change count ≤ s.assigned + 1
  have := facts.bound
  omega

end MicrosatLean.Verification.Implementation.Search.Concrete

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Analysis Std.Sat

theorem StateCertificate.watchUnit_mode {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (falseLit : s.mark lit ≠ 0)
    (root : Bool) (mode : PropagationMode s root)
    (head : s.mark ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!) = 0)
    (opposite : s.mark (Lit.negate ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!)) = 0) :
    let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    PropagationMode (retained.assign (watchClause ref) root) root := by
  dsimp only
  obtain ⟨_, _, retainedCertificate, _⟩ := certificate.retainWatch current falseLit
  let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
  obtain ⟨entry, member, id, _⟩ := retainedCertificate.watches.references lit ref current
  have packed := retainedCertificate.database.layout.packed member
  have nonempty := retainedCertificate.nonempty entry member
  have first : retained.db entry.id = entry.lits[0]! := by simpa using packed.literals 0 nonempty
  have literal : LiteralBound retained.nVars (retained.db entry.id) := by
    rw [first]
    apply packed.wellFormed
    simpa only [getElem!_pos entry.lits 0 nonempty] using Array.getElem_mem nonempty
  have headZero : retained.mark (retained.db entry.id) = 0 := by
    simpa only [← id, retained, State.mark, State.db] using head
  have oppositeZero : retained.mark (Lit.negate (retained.db entry.id)) = 0 := by
    simpa only [← id, retained, State.mark, State.db] using opposite
  have fresh := freshVariable_of_unmarked_literal retainedCertificate.active headZero oppositeZero
  have space : retained.assigned < retained.trail.size := by
    change s.assigned < s.trail.size
    rw [certificate.arrays.trailSize]
    have assigned := certificate.bounds.assignedVars
    omega
  have retainedMode : PropagationMode retained root := mode.restoreWatchArrays _ s.first
  have result := retainedMode.assign entry.id space fresh (retainedCertificate.arrays.literal_index literal.negate).1
  simpa only [← id, retained] using result

def WatchModeOutcome : Progress → Prop
  | .running after => PropagationMode after.solver after.root
  | .finished _ => True

end MicrosatLean.Verification.Implementation.Search.Concrete

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Analysis Std.Sat

/-- All phase facts share the returned state's genuine database and heads. -/
structure WatchRunningFacts (formula : Std.Sat.CNF Nat) (after : Machine)
    (original learned : List StoredClause) (heads : Nat → List Nat) (rank : Lit → Nat) : Prop where
  base : StateCertificate formula after.solver original learned heads rank
  history : DecisionHistory after.solver (original ++ learned)
  saved : DecisionWatchHistory after.solver (original ++ learned) heads
  units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore after.solver after.solver.assigned entry.lits[0]!
  mode : PropagationMode after.solver after.root
  phase :
    (after.phase = .nextLiteral ∧ after.currentLit = 0 ∧ after.previousWatch = 0 ∧
      SettledPrefix after.solver (original ++ learned) heads after.solver.processed) ∨
    (after.phase = .watch ∧ 0 < after.solver.processed ∧
      after.currentLit = after.solver.trail[after.solver.processed - 1]! ∧
      ∃ remaining, WatchCursor heads after.currentLit after.previousWatch remaining ∧
        SettledCursor after.solver (original ++ learned) heads after.currentLit remaining ∧
        SettledPrefix after.solver (original ++ learned) heads (after.solver.processed - 1))

def WatchRichOutcome (formula : Std.Sat.CNF Nat) : Progress → Prop
  | .running after => ∃ original learned heads rank, WatchRunningFacts formula after original learned heads rank
  | .finished (.unsat _) => CNF.Unsat formula
  | .finished (.sat _ _) => False

/-- Actual conflict learning recovers completed and saved watch prefixes,
unit truth, and the new propagation mode in the same returned ghost package. -/
theorem WatchScanFacts.conflict {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {count : Nat} {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (facts : WatchScanFacts formula s original learned heads rank count lit previous (ref :: rest))
    (mode : PropagationMode s false) (falseLit : s.mark lit ≠ 0)
    (missing : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = none)
    (head : s.mark ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!) ≠ 0)
    (decision oldLemmas : Nat) :
    let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    let result := CDCL.analyze retained (watchClause ref)
    let root := result.1.db (result.2 + 1) == 0
    WatchRichOutcome formula (.running ⟨result.1.assign result.2 root, decision, .nextLiteral, oldLemmas, root, 0, 0⟩) := by
  dsimp only
  obtain ⟨retainedOriginal, retainedLearned, oriented⟩ := facts.orient falseLit
  obtain ⟨conflictOriginal, conflictLearned, conflict, conflictBase, _, member, id, allFalse⟩ :=
    facts.base.retainedConflict facts.cursor.member falseLit missing head
  obtain ⟨sameOriginal, sameLearned⟩ := conflictBase.database.unique oriented.base.database
  subst conflictOriginal conflictLearned
  let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
  have oldPhase := mode.nonroot rfl
  have phase : NonrootPhase retained := ⟨oldPhase.levels, oldPhase.caches, oldPhase.nonroot⟩
  obtain ⟨_, entry⟩ := oriented.base.analysisTransitionEntry oriented.history phase member allFalse
  let result := CDCL.analyze retained conflict.id
  let root := result.1.db (result.2 + 1) == 0
  let added : StoredClause := ⟨result.2, analysisLearned retained conflict.id⟩
  let after : Machine := ⟨result.1.assign result.2 root, decision, .nextLiteral, oldLemmas, root, 0, 0⟩
  obtain ⟨nextOriginal, nextLearned, nextHeads, nextRank, nextBase⟩ := oriented.base.analyze_assign oriented.history entry
  have stored := analyze_database_meaning entry.semantic oriented.base.database oriented.base.meaning
  have expectedDatabase := stored.1.assign result.2 root
  obtain ⟨sameOriginal, sameLearned⟩ := nextBase.database.unique expectedDatabase
  subst nextOriginal nextLearned
  have expectedWatches := (oriented.base.analyze_watches entry).frameArrays (after := after.solver) rfl rfl
  have sameHeads := nextBase.watches.heads_unique expectedDatabase expectedWatches
  subst nextHeads
  have nextHistory := DecisionHistory.analyze_assign oriented.history entry root
  have nextSaved := oriented.base.analyze_saved oriented.saved entry root
  have nextUnits := oriented.base.analyze_units oriented.history entry root
  have nextMode := PropagationMode.analyze_assign phase entry
  have settled := oriented.base.analyze_settled oriented.saved entry root
  have processed : after.solver.processed = result.1.assigned := by
    simp only [after, State.assign, Id.run, pure, result, analyze_eq_addClause, addClause_processed,
      addClause_assigned, analysisBeforeStore, backjump_processed, backjump_assigned]
  have prefixSettled : SettledPrefix after.solver (retainedOriginal ++ (retainedLearned ++ [added]))
      (analysisHeads retained conflict.id heads) after.solver.processed := by
    rw [processed]
    exact settled
  have facts : WatchRunningFacts formula after retainedOriginal (retainedLearned ++ [added])
      (analysisHeads retained conflict.id heads) nextRank := by
    refine ⟨nextBase, ?_, nextSaved, nextUnits, nextMode, Or.inl ⟨rfl, rfl, rfl, prefixSettled⟩⟩
    simpa only [List.append_assoc] using nextHistory
  change ∃ nextOriginal nextLearned nextHeads nextRank, WatchRunningFacts formula _ nextOriginal nextLearned nextHeads nextRank
  exact ⟨retainedOriginal, retainedLearned ++ [added], analysisHeads retained conflict.id heads, nextRank,
    by simpa only [after, result, root, retained, id] using facts⟩

end MicrosatLean.Verification.Implementation.Search.Concrete
