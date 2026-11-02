import MicrosatLean.Verification.Implementation.Bridge.Trail
import MicrosatLean.Verification.Implementation.Bridge.FromNativeControl
import MicrosatLean.Verification.Implementation.Logic.Execution
import MicrosatLean.Verification.Implementation.Native.Search.ChoiceOutcome

namespace MicrosatLean.Verification.Implementation.Search

open Bridge
private abbrev NEntry := Native.Representation.StoredClause

theorem nativeTrail_decide {s : CDCL.State} {entries : List NEntry} {var : Nat}
    (space : s.assigned < s.trail.size) (fresh : Native.Representation.FreshVariable s var) :
    nativeTrail (s.decide var) entries =
      nativeTrail s entries ++ [⟨literalView (Native.Representation.decisionLiteral s var), none⟩] := by
  apply nativeTrail_append_of_get _ rfl
  · intro i before
    constructor
    · rw [Native.Representation.decide_trail_prefix before]
    · apply nativeReason_eq_of_code
      rw [Native.Representation.decide_trail_prefix before]
      exact Native.Analysis.decide_reason_prefix fresh before
  · rw [Native.Representation.decide_trail_last space]
    change (Native.literalView (Native.Representation.decisionLiteral s var).negate).negate =
      Native.literalView (Native.Representation.decisionLiteral s var)
    rw [Native.literalView_negate]
    simp only [Std.Sat.Literal.negate, Bool.not_not]
  · simp only [nativeReason, Native.Representation.decide_trail_last space,
      Native.Search.decide_reason_at_decision, ↓reduceIte]

theorem nativeState_decide {s : CDCL.State} {original learned : List NEntry} {var : Nat}
    (space : s.assigned < s.trail.size) (fresh : Native.Representation.FreshVariable s var) :
    nativeState (s.decide var) original learned =
      appendEntry (nativeState s original learned)
        (literalView (Native.Representation.decisionLiteral s var)) none := by
  have trail := nativeTrail_decide (entries := original ++ learned) space fresh
  change LogicalState.mk _ _ _ _ _ = LogicalState.mk _ _ _ _ _
  rw [trail]
  rfl

theorem closed_from_native {formula : Formula} {m : CDCL.Machine}
    {original learned : List NEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate (formulaView formula) m.solver original learned heads rank)
    (closed : Native.Analysis.PropagationClosed m.solver (original ++ learned)) :
    Closed (nativeState m.solver original learned) := by
  obtain ⟨order, ordered⟩ := base.order
  have represented := native_rep base ordered
  intro clause member
  rw [nativeState_database] at member
  obtain ⟨entry, contained, rfl⟩ := List.mem_map.mp member
  have result := unitClosed_fromNative represented (Nat.le_refl _) (closed entry contained)
  rw [← represented.trailLength] at result
  simpa only [prefixLiterals, List.take_length, LogicalState.trueTrail,
    Native.Representation.StoredClause.view, native_clauseView_eq] using result

/-- The phase-saving decision appends one fresh assumption, after completed
propagation of every stored clause. -/
theorem decision_execution {formula : Formula} {m : CDCL.Machine}
    {original learned : List NEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate (formulaView formula) m.solver original learned heads rank)
    (closed : Native.Analysis.PropagationClosed m.solver (original ++ learned))
    {var : Nat} (lower : 1 ≤ var) (upper : var ≤ m.solver.nVars)
    (unset : Native.Search.UnassignedVariable m.solver var) :
    LogicalExecution (formulaView formula) (nativeState m.solver original learned)
      (nativeState (m.solver.decide var) original learned) := by
  let s := m.solver
  have fresh := Native.Representation.freshVariable_of_unmarked base.active unset.1 unset.2
  have room := Native.Representation.assigned_lt_of_fresh base.active base.distinct fresh lower upper
  have space : s.assigned < s.trail.size := by
    dsimp only [s]
    rw [base.arrays.trailSize]
    omega
  rw [nativeState_decide space fresh]
  apply Logic.single_move
  apply LogicalMove.decide
  · simp only [LiteralBound, nativeState, literalView, Native.Representation.decisionLiteral_var]
    exact ⟨lower, upper⟩
  · intro lit member
    obtain ⟨entry, contained, equal⟩ := List.mem_map.mp member
    obtain ⟨i, before, value⟩ := List.mem_iff_getElem.mp contained
    have active : i < s.assigned := by simpa only [nativeState, nativeTrail_length] using before
    have get : (nativeState s original learned).trail[i]! = entry := by
      rw [getElem!_pos _ i before]
      exact value
    rw [nativeState, nativeTrail_get _ _ active] at get
    have entryVar : entry.literal.1 = s.trail[i]!.var := by rw [← get]; rfl
    rw [← equal, entryVar]
    simpa only [literalView, Native.Representation.decisionLiteral_var] using fresh i active
  · exact closed_from_native base closed

end MicrosatLean.Verification.Implementation.Search
