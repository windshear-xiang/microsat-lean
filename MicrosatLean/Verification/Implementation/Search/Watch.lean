import MicrosatLean.Verification.Implementation.Search.Concrete.MachineWatch
import MicrosatLean.Verification.Contracts
import MicrosatLean.Verification.Implementation.Search.WatchTrace
import MicrosatLean.Verification.Implementation.Bridge.Analysis
import MicrosatLean.Verification.Implementation.Bridge.ToConcrete
import MicrosatLean.Verification.Implementation.Search.Concrete.Termination

namespace MicrosatLean.Verification.Implementation.Search

open CDCL Bridge

theorem analyze_watch_trace {formula : Formula} {s : State}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) s original learned heads rank)
    (history : Analysis.DecisionHistory s (original ++ learned))
    (phase : Search.Concrete.NonrootPhase s) {conflict : StoredClause}
    (member : conflict ∈ original ++ learned)
    (falseClause : ∀ lit ∈ conflict.lits, s.mark lit ≠ 0) (decision oldLemmas : Nat) :
    let result := analyze s conflict.id
    let root := result.1.db (result.2 + 1) == 0
    WatchTrace formula (logicalView s original learned)
      (.running ⟨result.1.assign result.2 root, decision, .nextLiteral, oldLemmas, root, 0, 0⟩) := by
  dsimp only
  obtain ⟨_, entry⟩ := base.analysisTransitionEntry history phase member falseClause
  obtain ⟨nextOriginal, nextLearned, nextHeads, nextRank, nextBase⟩ := base.analyze_assign history entry
  have stored := Analysis.analyze_database_meaning entry.semantic base.database base.meaning
  have expected := stored.1.assign (analyze s conflict.id).2
    ((analyze s conflict.id).1.db ((analyze s conflict.id).2 + 1) == 0)
  obtain ⟨sameOriginal, sameLearned⟩ := nextBase.database.unique expected
  rw [sameOriginal, sameLearned] at nextBase
  exact ⟨_, _, nextHeads, nextRank, nextBase, view_analyze_assign_trace base entry _⟩

/-- The actual watch phase supplies a proper finite list and an arena-sized
budget. The trace induction therefore reaches an implemented source exit. -/
theorem step_watch_trace {formula : Formula} {machine : Machine}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (certificate : Search.Concrete.MachineCertificate formula machine original learned heads rank)
    (phase : machine.phase = .watch) :
    WatchTrace formula (logicalView machine.solver original learned) (step machine) := by
  rcases machine with ⟨s, decision, current, old, root, lit, previous⟩
  dsimp only at phase
  subst current
  have concrete := certificate.phase
  change Search.Concrete.WatchPhase s (original ++ learned) heads root lit previous at concrete
  obtain ⟨remaining, cursor, visited, settled⟩ := concrete.cursor
  have facts : Search.Concrete.WatchScanFacts (formulaView formula) s original learned heads rank
      (s.processed - 1) lit previous remaining :=
    ⟨certificate.base, certificate.history, certificate.saved, certificate.units,
      Nat.le_trans (Nat.sub_le _ _) certificate.base.bounds.processedAssigned, settled, visited, cursor⟩
  have processed : s.processed = s.processed - 1 + 1 := by have := concrete.positive; omega
  change WatchTrace formula (logicalView s original learned)
    (propagateWatches s.arena.size { s with arena := #[], first := #[] }
      s.arena s.first decision old root lit previous)
  apply propagateWatches_trace { s with arena := #[], first := #[] } decision old root lit
    remaining s.arena.size s.arena s.first previous facts
    (concrete.mode.restoreWatchArrays #[] #[]) processed concrete.literal.symm
    (Propagation.watchCursor_length_lt_arena facts.base.database facts.base.watches facts.cursor)
  intro state original learned heads rank base history phase entry member falseClause
  exact analyze_watch_trace base history phase member falseClause decision old

/-- Watch scans refine literal permutations, propagation and checked
learning/backjumping. Concrete invariant preservation supplies the separate
concrete control facts; representation uniqueness aligns the two endpoints. -/
theorem watch : PhaseCorrect .watch := by
  intro formula machine a w certificate phase
  have concrete := machineCertificate_concrete certificate
  have trace := step_watch_trace concrete phase
  obtain ⟨order, ordered⟩ := concrete.base.order
  have initial : a = logicalView machine.solver
      w.original w.learned :=
    rep_unique certificate.representation (view_rep concrete.base ordered)
  cases result : step machine with
  | running after =>
    have endpoint : WatchTrace formula (logicalView machine.solver
        w.original w.learned) (.running after) := by
      rw [← result]
      exact trace
    obtain ⟨original, learned, heads, rank, base, execution⟩ := endpoint
    have concrete := Search.Concrete.step_watch_invariant (concrete_of_certificate certificate) phase
    rw [result] at concrete
    have variables : after.solver.nVars = max 1 formula.numVars := by
      rw [Search.Concrete.step_nVars result, ← certificate.representation.variables]
      exact certificate.variables
    obtain ⟨next, witness, valid⟩ := of_concrete certificate.input concrete variables
    obtain ⟨nextOrder, nextOrdered⟩ := base.order
    have equal : logicalView after.solver original learned = next :=
      rep_unique (view_rep base nextOrdered) valid.representation
    change RunningPost formula a after
    refine ⟨next, witness, valid.representation, valid.variables, ?_, valid.control, valid.progress⟩
    rw [initial, ← equal]
    exact execution
  | finished answer =>
    have endpoint : WatchTrace formula (logicalView machine.solver
        w.original w.learned) (.finished answer) := by
      rw [← result]
      exact trace
    change FinishedPost formula a answer
    rw [initial]
    exact endpoint

end MicrosatLean.Verification.Implementation.Search
