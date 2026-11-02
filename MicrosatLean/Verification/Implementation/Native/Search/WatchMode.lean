import MicrosatLean.Verification.Implementation.Native.Search.PropagationMode
import MicrosatLean.Verification.Implementation.Native.Search.WatchOutcome

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Std.Sat

theorem StateCertificate.watchUnit_mode {formula : CNF Nat} {s : State}
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

theorem StateCertificate.watchConflict_mode {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned)) (mode : PropagationMode s false)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (falseLit : s.mark lit ≠ 0)
    (missing : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = none)
    (head : s.mark ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!) ≠ 0) :
    let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    let result := CDCL.analyze retained (watchClause ref)
    let root := result.1.db (result.2 + 1) == 0
    PropagationMode (result.1.assign result.2 root) root := by
  dsimp only
  obtain ⟨_, _, conflict, retainedCertificate, retainedHistory, member, id, allFalse⟩ :=
    certificate.retainedConflict current falseLit missing head
  have beforePhase := mode.nonroot rfl
  have phase : NonrootPhase { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit } :=
    ⟨beforePhase.levels, beforePhase.caches, beforePhase.nonroot⟩
  obtain ⟨_, entry⟩ := retainedCertificate.analysisTransitionEntry (retainedHistory history) phase member allFalse
  simpa only [id] using PropagationMode.analyze_assign phase entry

def WatchModeOutcome : Progress → Prop
  | .running after => PropagationMode after.solver after.root
  | .finished _ => True

/-- Actual watch traversal preserves root/nonroot propagation mode, including
the analyzer's real singleton root-flag test and asserting assignment. -/
theorem propagateWatches_mode {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit)
    (remaining : List Nat) (fuel : Nat) (arena first : Array Nat) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula (restoreWatchArrays s arena first) original learned heads rank)
    (history : DecisionHistory (restoreWatchArrays s arena first) (original ++ learned))
    (mode : PropagationMode s root) (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (cursor : WatchCursor heads lit previous remaining) (budget : remaining.length < fuel) :
    WatchModeOutcome (propagateWatches fuel s arena first decision oldLemmas root lit previous) := by
  induction remaining generalizing fuel arena first previous original learned heads rank with
  | nil =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have empty : currentWatchRef arena first lit previous = 0 := by
        simpa only [restoreWatchArrays, List.headD_nil] using cursor.current (certificate.watches.links lit)
      simp only [currentWatchRef, beq_iff_eq] at empty
      simp only [propagateWatches, Id.run, pure, beq_iff_eq, empty, ite_true, WatchModeOutcome]
      exact mode.restoreWatchArrays arena first
  | cons ref rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have current : currentWatchRef arena first lit previous = ref := by
        simpa only [restoreWatchArrays, List.headD_cons] using cursor.current (certificate.watches.links lit)
      have nonzero := storedWatchRef_nonzero certificate.database (certificate.watches.references lit ref cursor.member)
      have currentNonzero : currentWatchRef arena first lit previous ≠ 0 := by simpa only [current] using nonzero
      cases found : replacement (orientWatch arena (watchClause ref) lit) s.marks (watchClause ref) with
      | some pos =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = some pos := by simpa only [current] using found
        obtain ⟨_, _, nextCertificate, nextCursor, nextHistory⟩ := certificate.moveWatch cursor literal falseLit found
        have next := ih fuel (movedWatchArrays arena first lit ref previous pos).1
          (movedWatchArrays arena first lit ref previous pos).2 previous nextCertificate (nextHistory history)
          nextCursor (by simp only [List.length_cons] at budget; omega)
        rw [propagateWatches_replacement fuel s arena first decision oldLemmas root lit previous pos currentNonzero foundCurrent]
        simpa only [current] using next
      | none =>
        have foundCurrent : replacement (orientWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)
            s.marks (watchClause (currentWatchRef arena first lit previous)) = none := by simpa only [current] using found
        let retained := Propagation.retainWatch arena (watchClause ref) lit
        let other : Lit := retained[watchClause ref]!
        by_cases satisfied : s.mark other.negate ≠ 0
        · have satisfiedCurrent : s.mark (Lit.negate
              ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) ≠ 0 := by
            simpa only [current] using satisfied
          obtain ⟨_, _, nextCertificate, nextHistory⟩ := certificate.retainWatch cursor.member falseLit
          have next := ih fuel retained first ref nextCertificate (nextHistory history) (cursor.advance nonzero)
            (by simp only [List.length_cons] at budget; omega)
          rw [propagateWatches_skip fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent satisfiedCurrent]
          simpa only [current] using next
        · have opposite : s.mark other.negate = 0 := by simpa using satisfied
          by_cases unmarked : s.mark other = 0
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) = 0 := by simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by simpa only [current] using opposite
            rw [propagateWatches_unit fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent headCurrent oppositeCurrent]
            simp only [current, WatchModeOutcome]
            exact certificate.watchUnit_mode cursor.member falseLit root (mode.restoreWatchArrays arena first) unmarked opposite
          · have headCurrent : s.mark
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!) ≠ 0 := by simpa only [current] using unmarked
            have oppositeCurrent : s.mark (Lit.negate
                ((Propagation.retainWatch arena (watchClause (currentWatchRef arena first lit previous)) lit)[watchClause (currentWatchRef arena first lit previous)]!)) = 0 := by simpa only [current] using opposite
            rw [propagateWatches_conflict fuel s arena first decision oldLemmas root lit previous currentNonzero foundCurrent oppositeCurrent headCurrent]
            simp only [current]
            cases root with
            | false =>
              simp only [Bool.false_eq_true, ite_false, WatchModeOutcome]
              exact certificate.watchConflict_mode history (mode.restoreWatchArrays arena first) cursor.member falseLit found unmarked
            | true => simp only [ite_true, WatchModeOutcome]

theorem step_watch_mode_outcome {formula : CNF Nat} (s : State)
    (decision oldLemmas : Nat) (root : Bool) (lit : Lit) (previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned)) (mode : PropagationMode s root)
    (literal : LiteralBound s.nVars lit) (falseLit : s.mark lit ≠ 0)
    (remaining : List Nat) (cursor : WatchCursor heads lit previous remaining) :
    WatchStateOutcome formula (step ⟨s, decision, .watch, oldLemmas, root, lit, previous⟩) ∧
      WatchModeOutcome (step ⟨s, decision, .watch, oldLemmas, root, lit, previous⟩) := by
  refine ⟨step_watch_outcome s decision oldLemmas root lit previous certificate history mode.roots mode.nonroot
    literal falseLit remaining cursor, ?_⟩
  change WatchModeOutcome (propagateWatches s.arena.size { s with arena := #[], first := #[] }
    s.arena s.first decision oldLemmas root lit previous)
  have detached : PropagationMode { s with arena := #[], first := #[] } root := mode.restoreWatchArrays #[] #[]
  exact propagateWatches_mode { s with arena := #[], first := #[] } decision oldLemmas root lit
    remaining s.arena.size s.arena s.first previous certificate history detached literal falseLit cursor
    (watchCursor_length_lt_arena certificate.database certificate.watches cursor)

end MicrosatLean.Verification.Implementation.Native.Search
