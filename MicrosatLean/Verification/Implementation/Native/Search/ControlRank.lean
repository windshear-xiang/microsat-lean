import MicrosatLean.Verification.Implementation.Native.Search.StateCertificate
import MicrosatLean.Verification.Implementation.Native.Search.Decision
import MicrosatLean.Verification.Implementation.Native.Reduction.Frame

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Reduction

abbrev ControlRank := Nat × Nat × Nat × Nat

def ControlRankLT : ControlRank → ControlRank → Prop :=
  Prod.Lex Nat.lt (Prod.Lex Nat.lt (Prod.Lex Nat.lt Nat.lt))

theorem controlRank_wellFounded : WellFounded ControlRankLT :=
  (inferInstance : WellFoundedRelation ControlRank).wf

/-- A learning event grants one pending opportunity to restart at `choose`.
The credit is consumed before the next propagation invocation begins. -/
def learningCredit (machine : Machine) : Nat :=
  match machine.phase with
  | .beginPropagation => 0
  | _ => if machine.oldLemmas < machine.solver.nLemmas then 1 else 0

def phaseRank : Phase → Nat
  | .beginPropagation => 2
  | .watch => 2
  | .nextLiteral => 1
  | .choose => 0

/-- Numeric clause progress dominates restart credit, which dominates trail
progress and phase bookkeeping. Watch fuel is not part of this global rank. -/
def controlRank (bound variables : Nat) (machine : Machine) : ControlRank :=
  (clauseProgress bound machine.solver, learningCredit machine,
    2 * variables - machine.solver.assigned - machine.solver.processed, phaseRank machine.phase)

/-- A proof-only name for the real `choose` phase before its decision scan. -/
def prepareChoice (s : State) (cursor oldLemmas : Nat) : State × Nat := Id.run do
  let mut s := s
  let mut cursor := cursor
  if s.nLemmas > oldLemmas then
    cursor := s.head
    let threshold := (s.slow / 100) * 125
    if s.fast > threshold then
      s := ({ s with res := 0, fast := threshold }).restart
      if s.nLemmas > s.maxLemmas then s := s.reduceDB s.config.reductionK
  return (s, cursor)

theorem step_choose_eq (s : State) (cursor old : Nat) (root : Bool) (lit previous : Nat) :
    step ⟨s, cursor, .choose, old, root, lit, previous⟩ =
      let prepared := prepareChoice s cursor old
      let chosen := nextDecision prepared.1 prepared.2
      if chosen == 0 then .finished (.sat prepared.1.phases prepared.1.stats)
      else .running ⟨prepared.1.decide chosen, chosen, .beginPropagation, 0, false, 0, 0⟩ := by
  by_cases learned : s.nLemmas > old
  · by_cases restart : s.fast > s.slow / 100 * 125
    · simp only [step, prepareChoice, Id.run, pure, learned, restart, ↓reduceIte]
      split <;> rfl
    · simp only [step, prepareChoice, Id.run, pure, learned, restart, ↓reduceIte]
  · simp only [step, prepareChoice, Id.run, pure, learned, ↓reduceIte]

private theorem restart_nLemmas (s : State) : s.restart.nLemmas = s.nLemmas := by
  simpa only using congrArg State.nLemmas (restart_frame s).restore

private theorem restart_maxLemmas (s : State) : s.restart.maxLemmas = s.maxLemmas := by
  simpa only using congrArg State.maxLemmas (restart_frame s).restore

private theorem clauseProgress_restart (bound : Nat) (s : State) :
    clauseProgress bound s.restart = clauseProgress bound s := by
  simp only [clauseProgress, restart_nLemmas, restart_maxLemmas]

private theorem clauseProgress_decide (bound : Nat) (s : State) (var : Nat) :
    clauseProgress bound (s.decide var) = clauseProgress bound s := rfl

theorem prepareChoice_no_learning (s : State) (cursor old : Nat) (none : ¬ s.nLemmas > old) :
    prepareChoice s cursor old = (s, cursor) := by
  simp only [prepareChoice, Id.run, pure, none, ↓reduceIte]

/-- All counter changes in actual choice preparation are nonincreasing. The
strict reduction rule uses the old finite bound, not a post-reduction premise. -/
theorem prepareChoice_progress (bound : Nat) (s : State) (cursor old : Nat)
    (bounded : s.nLemmas ≤ bound) :
    clauseProgress bound (prepareChoice s cursor old).1 ≤ clauseProgress bound s := by
  by_cases learned : s.nLemmas > old
  · by_cases restart : s.fast > (s.slow / 100) * 125
    · by_cases pressure : s.nLemmas > s.maxLemmas
      · simp only [prepareChoice, Id.run, pure, learned, restart, restart_nLemmas,
          restart_maxLemmas, pressure, ↓reduceIte]
        have before : clauseProgress bound ({ s with
            res := 0,
            fast := s.slow / 100 * 125 }.restart) = clauseProgress bound s := by
          rw [clauseProgress_restart]
          rfl
        rw [← before]
        apply Nat.le_of_lt
        apply reduceDB_clauseProgress
        · simpa only [restart_nLemmas] using bounded
        · simpa only [restart_nLemmas, restart_maxLemmas] using pressure
      · simp only [prepareChoice, Id.run, pure, learned, restart, restart_nLemmas,
          restart_maxLemmas, pressure, ↓reduceIte, clauseProgress_restart]
        exact Nat.le_refl _
    · simp only [prepareChoice, Id.run, pure, learned, restart, ↓reduceIte]
      exact Nat.le_refl _
  · rw [prepareChoice_no_learning s cursor old learned]
    exact Nat.le_refl _

theorem step_beginPropagation_rank (bound variables : Nat) {before after : Machine}
    (phase : before.phase = .beginPropagation) (running : step before = .running after) :
    ControlRankLT (controlRank bound variables after) (controlRank bound variables before) := by
  rcases before with ⟨s, cursor, phase, old, root, lit, previous⟩
  simp only at phase
  subst phase
  simp only [step, Id.run, pure] at running
  have equal := Progress.running.inj running
  subst after
  simp only [controlRank, learningCredit, phaseRank, Nat.lt_irrefl, ↓reduceIte]
  exact .right _ (.right _ (.right _ (Nat.lt_succ_self 1)))

theorem step_nextLiteral_rank (bound variables : Nat) {before after : Machine}
    (phase : before.phase = .nextLiteral) (running : step before = .running after)
    (bounds : TrailBounds before.solver) (variablesEq : before.solver.nVars = variables) :
    ControlRankLT (controlRank bound variables after) (controlRank bound variables before) := by
  rcases before with ⟨s, cursor, phase, old, root, lit, previous⟩
  simp only at phase variablesEq bounds
  subst phase
  by_cases pending : s.processed < s.assigned
  · simp only [step, Id.run, pure, pending, ↓reduceIte] at running
    have equal := Progress.running.inj running
    subst after
    have assignedBound : s.assigned ≤ variables := by simpa only [variablesEq] using bounds.assignedVars
    have debt : 2 * variables - s.assigned - (s.processed + 1) <
        2 * variables - s.assigned - s.processed := by omega
    simp only [controlRank, learningCredit, phaseRank, clauseProgress]
    exact .right _ (.right _ (.left _ _ debt))
  · cases root <;> simp only [step, Id.run, pure, pending, ↓reduceIte, Bool.false_eq_true] at running
    all_goals
      have equal := Progress.running.inj running
      subst after
      simp only [controlRank, learningCredit, phaseRank, clauseProgress]
      exact .right _ (.right _ (.right _ (Nat.lt_succ_self 0)))

theorem step_choose_rank {formula : Std.Sat.CNF Nat} (bound variables : Nat)
    {before after : Machine} {original learned : List StoredClause}
    {heads : Nat → List Nat} {rank : Lit → Nat}
    (phase : before.phase = .choose) (running : step before = .running after)
    (certificate : StateCertificate formula before.solver original learned heads rank)
    (bounded : before.solver.nLemmas ≤ bound) (variablesEq : before.solver.nVars = variables)
    (cursorValid : ¬ before.solver.nLemmas > before.oldLemmas →
      before.decision = 0 ∨ (1 ≤ before.decision ∧ before.decision ≤ before.solver.nVars)) :
    ControlRankLT (controlRank bound variables after) (controlRank bound variables before) := by
  rcases before with ⟨s, cursor, phase, old, root, lit, previous⟩
  simp only at phase bounded variablesEq certificate cursorValid
  subst phase
  rw [step_choose_eq] at running
  by_cases newLearning : s.nLemmas > old
  · let prepared := prepareChoice s cursor old
    by_cases zero : nextDecision prepared.1 prepared.2 = 0
    · dsimp only [prepared] at zero
      simp only [beq_iff_eq, zero, ↓reduceIte] at running
      cases running
    · dsimp only [prepared] at zero
      simp only [beq_iff_eq, zero, ↓reduceIte] at running
      have equal := Progress.running.inj running
      subst after
      have progress := prepareChoice_progress bound s cursor old bounded
      simp only [controlRank, learningCredit, phaseRank, newLearning, ↓reduceIte,
        clauseProgress_decide]
      rcases Nat.lt_or_eq_of_le progress with less | same
      · exact .left _ _ less
      · rw [same]
        exact .right _ (.left _ _ (Nat.lt_succ_self 0))
  · rw [prepareChoice_no_learning s cursor old newLearning] at running
    dsimp only at running
    by_cases zero : nextDecision s cursor = 0
    · simp only [zero, beq_self_eq_true, ↓reduceIte] at running
      cases running
    · simp only [beq_iff_eq, zero, ↓reduceIte] at running
      have equal := Progress.running.inj running
      subst after
      obtain ⟨order, ordered⟩ := certificate.order
      have cursorMember : cursor ∈ order ∨ cursor = 0 := by
        rcases cursorValid newLearning with none | declared
        · exact Or.inr none
        · exact Or.inl ((ordered.2.1 cursor).mpr declared)
      have chosenMember := nextDecisionScan_mem_of_nonzero ordered (s.nVars + 1) cursor cursorMember zero
      have declared := (ordered.2.1 _).mp chosenMember
      have unset := nextDecisionScan_nonzero_unassigned (s.nVars + 1) s cursor zero
      have fresh := freshVariable_of_unmarked certificate.active unset.1 unset.2
      have room := assigned_lt_of_fresh certificate.active certificate.distinct fresh declared.1 declared.2
      have processedBound := certificate.bounds.processedAssigned
      have debt : 2 * variables - (s.assigned + 1) - s.processed <
          2 * variables - s.assigned - s.processed := by omega
      simp only [controlRank, learningCredit, phaseRank, newLearning, ↓reduceIte,
        clauseProgress_decide]
      exact .right _ (.right _ (.left _ _ debt))

end MicrosatLean.Verification.Implementation.Native.Search
