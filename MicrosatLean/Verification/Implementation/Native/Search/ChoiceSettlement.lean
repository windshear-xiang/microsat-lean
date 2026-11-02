import MicrosatLean.Verification.Implementation.Native.Search.ChoiceOutcome
import MicrosatLean.Verification.Implementation.Native.Reduction.Settlement

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation Propagation

/-- The saved actual decision at `forced` supplies root-prefix watch truth.
If no nonroot assignment exists, the current completed prefix is that root
prefix already. No truth witness from a discarded level is reused. -/
theorem DecisionWatchHistory.rootSettled {s : State} {entries : List StoredClause}
    {heads : Nat → List Nat} (history : DecisionWatchHistory s entries heads)
    (levels : LevelCover s) (bounds : TrailBounds s)
    (settled : SettledWatches s entries heads s.assigned) : SettledWatches s entries heads s.forced := by
  by_cases nonroot : s.forced < s.assigned
  · obtain ⟨decision, lower, upper, reason⟩ := levels s.forced (Nat.le_refl _) nonroot
    have equal : decision = s.forced := by omega
    subst decision
    exact history s.forced (Nat.le_refl _) nonroot reason
  · have equal : s.forced = s.assigned := by
      have := bounds.forcedProcessed
      have := bounds.processedAssigned
      omega
    simpa only [equal] using settled

theorem settledWatches_restart {s : State} {entries : List StoredClause} {heads : Nat → List Nat}
    (history : DecisionWatchHistory s entries heads) (levels : LevelCover s) (bounds : TrailBounds s)
    (settled : SettledWatches s entries heads s.assigned) :
    SettledWatches s.restart entries heads s.restart.assigned := by
  rw [restart_assigned bounds]
  exact settledWatches_transfer (history.rootSettled levels bounds settled) (fun _ _ => by rw [restart_trail])

end MicrosatLean.Verification.Implementation.Native.Analysis

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Reduction Std.Sat

private theorem rebuild_saved {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads newHeads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (next : StateCertificate formula s original learned newHeads rank)
    (saved : DecisionWatchHistory s (original ++ learned) heads) :
    DecisionWatchHistory s (original ++ learned) newHeads := by
  intro decision lower before reason
  exact settledWatches_of_sameClauses certificate.watches next.database next.watches
    (fun entry member => ⟨entry, member, rfl⟩) (PrefixLiterals.refl s decision)
    (saved decision lower before reason)

private theorem sameState_settlement {formula : Std.Sat.CNF Nat} {s : State}
    {original learned nextLearned : List StoredClause} {heads newHeads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (next : StateCertificate formula s original nextLearned newHeads rank)
    (saved : DecisionWatchHistory s (original ++ learned) heads)
    (settled : SettledWatches s (original ++ learned) heads s.assigned)
    (units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]!) :
    DecisionWatchHistory s (original ++ nextLearned) newHeads ∧
      SettledWatches s (original ++ nextLearned) newHeads s.assigned ∧
      ∀ entry ∈ original ++ nextLearned, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]! := by
  have same := (next.database.unique certificate.database).2
  subst nextLearned
  exact ⟨rebuild_saved certificate next saved,
    settledWatches_of_sameClauses certificate.watches next.database next.watches
      (fun entry member => ⟨entry, member, rfl⟩) (PrefixLiterals.refl s s.assigned) settled,
    units⟩

private theorem restart_units {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (levels : LevelCover s) (bounds : TrailBounds s)
    (closed : PropagationClosed s entries) :
    ∀ entry ∈ entries, entry.lits.size = 1 → TrueBefore s.restart s.restart.assigned entry.lits[0]! := by
  intro entry member unit
  rw [restart_assigned bounds]
  exact FalseBefore.transfer (fun _ _ => by rw [restart_trail])
    ((DecisionHistory.rootClosed history levels bounds closed entry member).unit_true unit)

private theorem restart_count_same (s : State) : s.restart.nLemmas = s.nLemmas := by
  simpa only using congrArg State.nLemmas (restart_frame s).restore

private theorem restart_limit_same (s : State) : s.restart.maxLemmas = s.maxLemmas := by
  simpa only using congrArg State.maxLemmas (restart_frame s).restore

private theorem restart_config_same (s : State) : s.restart.config = s.config := by
  simpa only using congrArg State.config (restart_frame s).restore

/-- All evidence at the completed prepared choice boundary shares the same
actual original/retained database and rebuilt linked watch heads. -/
structure PreparedChoiceSettlement (formula : Std.Sat.CNF Nat) (s : State)
    (original learned : List StoredClause) (heads : Nat → List Nat) (rank : Lit → Nat) : Prop where
  certificate : StateCertificate formula s original learned heads rank
  history : DecisionHistory s (original ++ learned)
  levels : LevelCover s
  six : SixBefore s
  closed : PropagationClosed s (original ++ learned)
  saved : DecisionWatchHistory s (original ++ learned) heads
  settled : SettledWatches s (original ++ learned) heads s.assigned
  units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]!

theorem StateCertificate.prepareChoice_settlement {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned)) (levels : LevelCover s) (six : SixBefore s)
    (closed : PropagationClosed s (original ++ learned))
    (saved : DecisionWatchHistory s (original ++ learned) heads)
    (settled : SettledWatches s (original ++ learned) heads s.assigned)
    (units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]!)
    (cursor old : Nat) :
    ∃ nextLearned nextHeads, PreparedChoiceSettlement formula (Search.prepareChoice s cursor old).1
      original nextLearned nextHeads rank := by
  obtain ⟨nextLearned, nextHeads, next, nextHistory, nextLevels, nextSix, nextClosed⟩ :=
    certificate.prepareChoice history levels six closed cursor old
  have strong : DecisionWatchHistory (Search.prepareChoice s cursor old).1 (original ++ nextLearned) nextHeads ∧
      SettledWatches (Search.prepareChoice s cursor old).1 (original ++ nextLearned) nextHeads
        (Search.prepareChoice s cursor old).1.assigned ∧
      ∀ entry ∈ original ++ nextLearned, entry.lits.size = 1 →
        TrueBefore (Search.prepareChoice s cursor old).1 (Search.prepareChoice s cursor old).1.assigned entry.lits[0]! := by
    by_cases learning : s.nLemmas > old
    · by_cases restart : s.fast > s.slow / 100 * 125
      · let reset := { s with res := 0, fast := s.slow / 100 * 125 }
        have resetCertificate : StateCertificate formula reset original learned heads rank := certificate.setRestartCounters 0 _
        have resetHistory : DecisionHistory reset (original ++ learned) := history
        have resetSaved : DecisionWatchHistory reset (original ++ learned) heads := saved
        have resetLevels : LevelCover reset := levels
        have resetClosed : PropagationClosed reset (original ++ learned) := closed
        have resetSettled : SettledWatches reset (original ++ learned) heads reset.assigned := settled
        have rootSaved := resetSaved.restart resetCertificate.bounds
        have rootSettled := settledWatches_restart resetSaved resetLevels resetCertificate.bounds resetSettled
        have rootUnits := restart_units resetHistory resetLevels resetCertificate.bounds resetClosed
        by_cases pressure : s.nLemmas > s.maxLemmas
        · simp only [Search.prepareChoice, learning, restart, Id.run, pure, restart_count_same,
            restart_limit_same, restart_config_same, pressure, ↓reduceIte] at next ⊢
          obtain ⟨kept, keptHeads, keptCertificate, matching, _⟩ :=
            resetCertificate.restart.reduceDB_with_relocation (restart_root resetCertificate.bounds) s.config.reductionK
          have same := (next.database.unique keptCertificate.database).2
          subst nextLearned
          exact ⟨DecisionWatchHistory.no_decisions (Nat.le_of_eq
              (reduceDB_root (restart_root resetCertificate.bounds) _)),
            settledWatches_reduceDB resetCertificate.restart.watches next.database next.watches matching rootSettled,
            activeUnits_reduceDB matching rootUnits⟩
        · simp only [Search.prepareChoice, learning, restart, Id.run, pure, restart_count_same,
            restart_limit_same, pressure, ↓reduceIte] at next ⊢
          exact sameState_settlement resetCertificate.restart next rootSaved rootSettled rootUnits
      · simp only [Search.prepareChoice, learning, restart, Id.run, pure, ↓reduceIte] at next ⊢
        exact sameState_settlement certificate next saved settled units
    · rw [prepareChoice_no_learning s cursor old learning] at next ⊢
      exact sameState_settlement certificate next saved settled units
  exact ⟨nextLearned, nextHeads, next, nextHistory, nextLevels, nextSix, nextClosed,
    strong.1, strong.2.1, strong.2.2⟩

/-- The running decision return carries one shared ghost witness for base
validity, both histories, active unit truth, and its completed processed prefix. -/
structure ChoiceSettlementRunning (formula : Formula) (after : Machine) : Prop where
  choice : ChoiceRunning formula after
  data : ∃ original learned heads rank,
    StateCertificate (formulaView formula) after.solver original learned heads rank ∧
      DecisionHistory after.solver (original ++ learned) ∧
      DecisionWatchHistory after.solver (original ++ learned) heads ∧
      (∀ entry ∈ original ++ learned, entry.lits.size = 1 →
        TrueBefore after.solver after.solver.assigned entry.lits[0]!) ∧
      SettledPrefix after.solver (original ++ learned) heads after.solver.processed

def ChoiceSettlementOutcome (formula : Formula) : Progress → Prop
  | .running after => ChoiceSettlementRunning formula after
  | .finished result => ValidResult formula result

/-- Full actual choice preservation, with closure derived from completed
watch visits and true units. A new decision saves exactly that completed
watch boundary and leaves the old processed prefix settled on its new trail. -/
theorem step_choose_settlement_outcome {formula : Formula} (s : State) (cursor old : Nat)
    (root : Bool) (lit previous : Nat)
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate (formulaView formula) s original learned heads rank)
    (variables : formula.numVars ≤ s.nVars) (history : DecisionHistory s (original ++ learned))
    (levels : LevelCover s) (six : SixBefore s)
    (saved : DecisionWatchHistory s (original ++ learned) heads)
    (settled : SettledWatches s (original ++ learned) heads s.assigned)
    (units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]!)
    (covered : ¬s.nLemmas > old → DecisionCursor s cursor) (quiet : s.processed = s.assigned) :
    ChoiceSettlementOutcome formula (step ⟨s, cursor, .choose, old, root, lit, previous⟩) := by
  have closed : PropagationClosed s (original ++ learned) :=
    prefixUnitClosed_of_settled certificate.active (Nat.le_refl _) certificate.watches certificate.nonempty units settled
  have core := step_choose_outcome s cursor old root lit previous certificate variables history levels six closed covered quiet
  obtain ⟨nextLearned, nextHeads, preparedData⟩ :=
    certificate.prepareChoice_settlement history levels six closed saved settled units cursor old
  let prepared := Search.prepareChoice s cursor old
  have nextCursor : DecisionCursor prepared.1 prepared.2 :=
    prepareChoice_decisionCursor cursor old certificate.order covered
  have nextQuiet : prepared.1.processed = prepared.1.assigned :=
    prepareChoice_quiescent certificate.bounds quiet cursor old
  rw [step_choose_eq] at core ⊢
  change ChoiceOutcome formula (if nextDecision prepared.1 prepared.2 == 0 then
    .finished (.sat prepared.1.phases prepared.1.stats) else
    .running ⟨prepared.1.decide (nextDecision prepared.1 prepared.2), nextDecision prepared.1 prepared.2,
      .beginPropagation, 0, false, 0, 0⟩) at core
  change ChoiceSettlementOutcome formula (if nextDecision prepared.1 prepared.2 == 0 then
    .finished (.sat prepared.1.phases prepared.1.stats) else
    .running ⟨prepared.1.decide (nextDecision prepared.1 prepared.2), nextDecision prepared.1 prepared.2,
      .beginPropagation, 0, false, 0, 0⟩)
  by_cases zero : nextDecision prepared.1 prepared.2 = 0
  · simpa only [zero, beq_self_eq_true, ite_true, ChoiceOutcome, ChoiceSettlementOutcome] using core
  · simp only [beq_iff_eq, zero, ite_false, ChoiceOutcome] at core
    simp only [beq_iff_eq, zero, ite_false, ChoiceSettlementOutcome]
    let selected := nextDecision prepared.1 prepared.2
    have unset : UnassignedVariable prepared.1 selected :=
      nextDecisionScan_nonzero_unassigned (prepared.1.nVars + 1) prepared.1 prepared.2 zero
    have fresh := freshVariable_of_unmarked preparedData.certificate.active unset.1 unset.2
    have nextCertificate := preparedData.certificate.nextDecision prepared.2 nextCursor.declared_or_zero zero
    have nextHistory := preparedData.history.decide preparedData.closed selected fresh
    have nextSaved := preparedData.saved.decide preparedData.settled selected fresh
    refine ⟨core, original, nextLearned, nextHeads, extendTrailRank rank selected prepared.1.assigned,
      nextCertificate, nextHistory, nextSaved, ?_, ?_⟩
    · intro entry member unit
      obtain ⟨i, before, value⟩ := preparedData.units entry member unit
      exact ⟨i, Nat.lt_succ_of_lt before, (decide_trail_prefix before).trans value⟩
    · intro falseLit falseBefore ref watched entry member id
      obtain ⟨falseIndex, beforeProcessed, falseValue⟩ := falseBefore
      have old : falseIndex < prepared.1.assigned := by
        change falseIndex < prepared.1.processed at beforeProcessed
        simpa only [nextQuiet] using beforeProcessed
      have priorFalse : FalseBefore prepared.1 prepared.1.assigned falseLit :=
        ⟨falseIndex, old, (decide_trail_prefix old).symm.trans falseValue⟩
      obtain ⟨i, before, value⟩ := preparedData.settled falseLit priorFalse ref watched entry member id
      exact ⟨i, Nat.lt_succ_of_lt before, (decide_trail_prefix before).trans value⟩

end MicrosatLean.Verification.Implementation.Native.Search
