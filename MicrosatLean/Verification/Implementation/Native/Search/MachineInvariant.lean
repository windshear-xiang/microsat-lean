import MicrosatLean.Verification.Implementation.Native.Search.InitialState
import MicrosatLean.Verification.Implementation.Native.Search.PropagationMode
import MicrosatLean.Verification.Implementation.Native.Analysis.WatchHistory

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Initialization Std.Sat

def UnitTruth (s : State) (entries : List StoredClause) : Prop :=
  ∀ entry ∈ entries, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]!

/-- An empty/root-only invocation can finish with a false root flag. Pending
nonroot work instead carries the concrete decision-level and cache facts. -/
structure NextMode (s : State) (root : Bool) : Prop where
  roots : RootWatchTrail s root
  nonroot : root = false → s.assigned = s.forced ∨ NonrootPhase s

theorem NextMode.ofPropagationMode {s : State} {root : Bool} (mode : PropagationMode s root) :
    NextMode s root := ⟨mode.roots, fun nonroot => Or.inr (mode.nonroot nonroot)⟩

theorem NextMode.pending {s : State} {root : Bool} (mode : NextMode s root) (bounds : TrailBounds s)
    (pending : s.processed < s.assigned) : PropagationMode s root := by
  refine ⟨mode.roots, ?_⟩
  intro nonroot
  rcases mode.nonroot nonroot with empty | phase
  · have lower := bounds.forcedProcessed
    omega
  · exact phase

/-- The only two actual entrances to `beginPropagation`: initial root units,
or one freshly appended pending decision. The later guard is derived from
these concrete reason/cursor facts. -/
def BeginEvidence (s : State) : Prop :=
  (s.processed = 0 ∧ s.forced = 0 ∧
    (∀ i, i < s.assigned → s.mark s.trail[i]! = 6) ∧
    (∀ i, i < s.assigned → s.reason s.trail[i]! ≠ 0)) ∨
  (NonrootPhase s ∧ s.processed + 1 = s.assigned ∧ s.reason s.trail[s.processed]! = 0)

theorem BeginEvidence.mode {s : State} (evidence : BeginEvidence s) :
    NextMode s (s.processed < s.assigned && s.reason s.trail[s.processed]! != 0) := by
  rcases evidence with ⟨processed, forced, roots, reasons⟩ | ⟨phase, _, zero⟩
  · refine ⟨fun _ => roots, ?_⟩
    intro falseGuard
    apply Or.inl
    by_cases empty : s.assigned = 0
    · omega
    · have positive : 0 < s.assigned := by omega
      have reason := reasons 0 positive
      simp [processed, positive, reason] at falseGuard
  · have falseGuard : (s.processed < s.assigned && s.reason s.trail[s.processed]! != 0) = false := by simp [zero]
    refine ⟨?_, fun _ => Or.inr phase⟩
    intro trueGuard
    rw [falseGuard] at trueGuard
    cases trueGuard

/-- Exact watch position plus the completed prefix and visited list segment.
Truth witnesses may be pending assignments on the current active trail. -/
structure WatchPhase (s : State) (entries : List StoredClause) (heads : Nat → List Nat)
    (root : Bool) (lit : Lit) (previous : Nat) : Prop where
  mode : PropagationMode s root
  positive : 0 < s.processed
  literal : lit = s.trail[s.processed - 1]!
  cursor : ∃ remaining, WatchCursor heads lit previous remaining ∧
    SettledCursor s entries heads lit remaining ∧ SettledPrefix s entries heads (s.processed - 1)

/-- Phase bookkeeping contains only concrete cursor, trail and watch facts.
The begin-phase cursor is unconditional because that phase resets the old
learned counter; it comes from initial head coverage or actual choice. -/
def PhaseInvariant (machine : Machine) (entries : List StoredClause) (heads : Nat → List Nat) : Prop :=
  match machine.phase with
  | .beginPropagation =>
    BeginEvidence machine.solver ∧ DecisionCursor machine.solver machine.decision ∧
      machine.oldLemmas = 0 ∧ machine.root = false ∧ machine.currentLit = 0 ∧ machine.previousWatch = 0 ∧
      SettledPrefix machine.solver entries heads machine.solver.processed
  | .nextLiteral =>
    NextMode machine.solver machine.root ∧ machine.currentLit = 0 ∧ machine.previousWatch = 0 ∧
      SettledPrefix machine.solver entries heads machine.solver.processed
  | .watch => WatchPhase machine.solver entries heads machine.root machine.currentLit machine.previousWatch
  | .choose =>
    machine.solver.processed = machine.solver.assigned ∧ machine.currentLit = 0 ∧ machine.previousWatch = 0 ∧
      LevelCover machine.solver ∧ SixBefore machine.solver ∧
      SettledPrefix machine.solver entries heads machine.solver.processed

/-- Shared concrete solver and ghost state. There is no field asserting
future preservation, result validity, progress, or eventual termination. -/
structure MachineCertificate (formula : Formula) (machine : Machine)
    (original learned : List StoredClause) (heads : Nat → List Nat) (rank : Lit → Nat) : Prop where
  base : StateCertificate (formulaView formula) machine.solver original learned heads rank
  variables : formula.numVars ≤ machine.solver.nVars
  history : DecisionHistory machine.solver (original ++ learned)
  saved : DecisionWatchHistory machine.solver (original ++ learned) heads
  units : UnitTruth machine.solver (original ++ learned)
  cursor : machine.solver.nLemmas ≤ machine.oldLemmas → DecisionCursor machine.solver machine.decision
  phase : PhaseInvariant machine (original ++ learned) heads
  oldCount : machine.oldLemmas ≤ machine.solver.nLemmas

def MachineInvariant (formula : Formula) (machine : Machine) : Prop :=
  ∃ original learned heads rank, MachineCertificate formula machine original learned heads rank

def InvariantProgress (formula : Formula) : Progress → Prop
  | .running machine => MachineInvariant formula machine
  | .finished result => ValidResult formula result

/-- Successful execution of the real initializer establishes the global
invariant at the exact machine passed to the existing search driver. -/
theorem initState_some_machineInvariant {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (success : initState formula config = .ok (some s)) :
    MachineInvariant formula { solver := s, decision := s.head } := by
  obtain ⟨original, learned, heads, rank, base⟩ := initState_some_certificate wellFormed success
  have cursors := initState_some_cursors wellFormed success
  have nondecision := initState_some_nondecision wellFormed success
  have saved : DecisionWatchHistory s (original ++ learned) heads := by
    intro decision _ before zero
    exact False.elim (nondecision decision before zero)
  have settled : SettledPrefix s (original ++ learned) heads s.processed := by
    intro lit falseLit
    obtain ⟨i, before, _⟩ := falseLit
    rw [cursors.1] at before
    omega
  have begin : BeginEvidence s := Or.inl ⟨cursors.1, cursors.2,
    initState_some_rootTrail wellFormed success true rfl, nondecision⟩
  refine ⟨original, learned, heads, rank, base, ?_, initState_some_history wellFormed success _, saved,
    initState_some_unitTruth wellFormed success base, fun _ => DecisionCursor.head base.order, ?_, ?_⟩
  · rw [initState_some_variables wellFormed success]
    omega
  · exact ⟨begin, DecisionCursor.head base.order, rfl, rfl, rfl, rfl, settled⟩
  · exact Nat.zero_le _

/-- The actual begin-propagation guard and old-counter reset preserve the
concrete invariant, including the previously unconditional real scan cursor. -/
theorem MachineCertificate.beginPropagation {formula : Formula} {s : State} {decision old : Nat}
    {root : Bool} {lit previous : Nat} {original learned : List StoredClause}
    {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : MachineCertificate formula ⟨s, decision, .beginPropagation, old, root, lit, previous⟩
      original learned heads rank) :
    MachineCertificate formula
      ⟨s, decision, .nextLiteral, s.nLemmas,
        s.processed < s.assigned && s.reason s.trail[s.processed]! != 0, 0, 0⟩ original learned heads rank := by
  have phase := certificate.phase
  change BeginEvidence s ∧ DecisionCursor s decision ∧ _ at phase
  refine ⟨certificate.base, certificate.variables, certificate.history, certificate.saved,
    certificate.units, fun _ => phase.2.1, ?_, Nat.le_refl _⟩
  exact ⟨phase.1.mode, rfl, rfl, phase.2.2.2.2.2.2⟩

theorem step_beginPropagation_invariant {formula : Formula} {machine : Machine}
    (invariant : MachineInvariant formula machine) (phase : machine.phase = .beginPropagation) :
    InvariantProgress formula (step machine) := by
  obtain ⟨original, learned, heads, rank, certificate⟩ := invariant
  rcases machine with ⟨s, decision, current, old, root, lit, previous⟩
  dsimp only at phase
  subst current
  change InvariantProgress formula
    (.running ⟨s, decision, .nextLiteral, s.nLemmas,
      s.processed < s.assigned && s.reason s.trail[s.processed]! != 0, 0, 0⟩)
  exact ⟨original, learned, heads, rank, certificate.beginPropagation⟩

end MicrosatLean.Verification.Implementation.Native.Search
