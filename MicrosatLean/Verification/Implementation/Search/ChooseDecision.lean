import MicrosatLean.Verification.Implementation.Bridge.Trail
import MicrosatLean.Verification.Implementation.Bridge.FromConcreteControl
import MicrosatLean.Verification.Implementation.Logic.Execution
import MicrosatLean.Verification.Implementation.Search.Concrete.ChoiceOutcome

namespace MicrosatLean.Verification.Implementation.Search

open Bridge

theorem trailView_decide {s : CDCL.State} {entries : List StoredClause} {var : Nat}
    (space : s.assigned < s.trail.size) (fresh : Representation.FreshVariable s var) :
    trailView (s.decide var) entries =
      trailView s entries ++ [⟨literalView (Representation.decisionLiteral s var), none⟩] := by
  apply trailView_append_of_get _ rfl
  · intro i before
    constructor
    · rw [Representation.decide_trail_prefix before]
    · apply reasonView_eq_of_code
      rw [Representation.decide_trail_prefix before]
      exact Analysis.decide_reason_prefix fresh before
  · rw [Representation.decide_trail_last space]
    change (literalView (Representation.decisionLiteral s var).negate).negate =
      literalView (Representation.decisionLiteral s var)
    rw [literalView_negate]
    simp only [Std.Sat.Literal.negate, Bool.not_not]
  · simp only [reasonView, Representation.decide_trail_last space,
      Search.Concrete.decide_reason_at_decision, ↓reduceIte]

theorem logicalView_decide {s : CDCL.State} {original learned : List StoredClause} {var : Nat}
    (space : s.assigned < s.trail.size) (fresh : Representation.FreshVariable s var) :
    logicalView (s.decide var) original learned =
      appendEntry (logicalView s original learned)
        (literalView (Representation.decisionLiteral s var)) none := by
  have trail := trailView_decide (entries := original ++ learned) space fresh
  change LogicalState.mk _ _ _ _ _ = LogicalState.mk _ _ _ _ _
  rw [trail]
  rfl

theorem closed_of_concrete {formula : Formula} {m : CDCL.Machine}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    (closed : Analysis.PropagationClosed m.solver (original ++ learned)) :
    Closed (logicalView m.solver original learned) := by
  obtain ⟨order, ordered⟩ := base.order
  have represented := view_rep base ordered
  intro clause member
  rw [logicalView_database] at member
  obtain ⟨entry, contained, rfl⟩ := List.mem_map.mp member
  have result := unitClosed_of_concrete represented (Nat.le_refl _) (closed entry contained)
  rw [← represented.trailLength] at result
  simpa only [prefixLiterals, List.take_length, LogicalState.trueTrail,
    Representation.StoredClause.view] using result

/-- The phase-saving decision appends one fresh assumption, after completed
propagation of every stored clause. -/
theorem decision_execution {formula : Formula} {m : CDCL.Machine}
    {original learned : List StoredClause} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    (closed : Analysis.PropagationClosed m.solver (original ++ learned))
    {var : Nat} (lower : 1 ≤ var) (upper : var ≤ m.solver.nVars)
    (unset : Search.Concrete.UnassignedVariable m.solver var) :
    LogicalExecution (formulaView formula) (logicalView m.solver original learned)
      (logicalView (m.solver.decide var) original learned) := by
  let s := m.solver
  have fresh := Representation.freshVariable_of_unmarked base.active unset.1 unset.2
  have room := Representation.assigned_lt_of_fresh base.active base.distinct fresh lower upper
  have space : s.assigned < s.trail.size := by
    dsimp only [s]
    rw [base.arrays.trailSize]
    omega
  rw [logicalView_decide space fresh]
  apply Logic.single_move
  apply LogicalMove.decide
  · simp only [LiteralBound, logicalView, literalView, Representation.decisionLiteral_var]
    exact ⟨lower, upper⟩
  · intro lit member
    obtain ⟨entry, contained, equal⟩ := List.mem_map.mp member
    obtain ⟨i, before, value⟩ := List.mem_iff_getElem.mp contained
    have active : i < s.assigned := by simpa only [logicalView, trailView_length] using before
    have get : (logicalView s original learned).trail[i]! = entry := by
      rw [getElem!_pos _ i before]
      exact value
    rw [logicalView, trailView_get _ _ active] at get
    have entryVar : entry.literal.1 = s.trail[i]!.var := by rw [← get]; rfl
    rw [← equal, entryVar]
    simpa only [literalView, Representation.decisionLiteral_var] using fresh i active
  · exact closed_of_concrete base closed

end MicrosatLean.Verification.Implementation.Search
