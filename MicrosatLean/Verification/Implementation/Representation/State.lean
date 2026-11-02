import MicrosatLean.Verification.Implementation.Representation.Types

namespace MicrosatLean.Verification.Implementation.Representation

open CDCL

variable {s : State} {lit other : Lit} {value clauseId var i n : Nat} {root : Bool}

@[simp] theorem negate_var (lit : Lit) : lit.negate.var = lit.var := by
  simp [Lit.negate, Lit.var, Nat.xor_div_two]

@[simp] theorem negate_negate (lit : Lit) : lit.negate.negate = lit := by
  simp [Lit.negate, Nat.xor_assoc]

theorem negate_mod_two (lit : Lit) : lit.negate % 2 = 1 - lit % 2 := by
  have modXor : (lit ^^^ 1) % 2 = lit % 2 ^^^ (1 % 2) := by
    simpa using (Nat.xor_mod_two_pow (a := lit) (b := 1) (n := 1))
  unfold Lit.negate
  rw [modXor]
  rcases Nat.mod_two_eq_zero_or_one lit with h | h <;> simp [h]

theorem negate_ne (lit : Lit) : lit.negate ≠ lit := by
  intro equal
  have h := congrArg (· % 2) equal
  rw [negate_mod_two] at h
  rcases Nat.mod_two_eq_zero_or_one lit with parity | parity <;> simp [parity] at h

/-- Each encoded literal is one of its variable's two polarities. -/
theorem literal_encoding (lit : Lit) : lit = 2 * lit.var ∨ lit = 2 * lit.var + 1 := by
  have value := Nat.mod_add_div lit 2
  rcases Nat.mod_two_eq_zero_or_one lit with parity | parity
  · left
    rw [parity, Nat.zero_add] at value
    exact value.symm
  · right
    rw [parity] at value
    simpa only [Lit.var, Nat.add_comm] using value.symm

theorem LiteralBound.index (h : LiteralBound n lit) : lit < 2 * (n + 1) := by
  have quotient : lit / 2 < n + 1 := Nat.lt_succ_of_le h.2
  simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul (by decide : 0 < 2)).mp quotient

theorem LiteralBound.nonzero (h : LiteralBound n lit) : lit ≠ 0 := by
  intro zero
  simp [LiteralBound, Lit.var, zero] at h

theorem LiteralBound.negate (h : LiteralBound n lit) : LiteralBound n lit.negate := by
  simpa [LiteralBound] using h

theorem ArrayBounds.literal_index (h : ArrayBounds s) (hlit : LiteralBound s.nVars lit) :
    lit < s.marks.size ∧ lit < s.first.size := by
  rw [h.marksSize, h.firstSize]
  exact ⟨hlit.index, hlit.index⟩

theorem ArrayBounds.variable_index (h : ArrayBounds s) (hvar : var ≤ s.nVars) :
    var < s.reasons.size ∧ var < s.phases.size ∧ var < s.previous.size ∧ var < s.next.size := by
  rw [h.reasonsSize, h.phasesSize, h.previousSize, h.nextSize]
  omega

theorem ArrayBounds.setMark (h : ArrayBounds s) : ArrayBounds (s.setMark lit value) := by
  rcases h with ⟨hf, hm, hr, hp, ht, hprev, hn⟩
  constructor <;> simp_all [State.setMark]

theorem ArrayBounds.unassign (h : ArrayBounds s) : ArrayBounds (s.unassign lit) :=
  h.setMark

theorem TrailBounds.setMark (h : TrailBounds s) : TrailBounds (s.setMark lit value) :=
  ⟨h.forcedProcessed, h.processedAssigned, h.assignedVars⟩

theorem TrailBounds.unassign (h : TrailBounds s) : TrailBounds (s.unassign lit) := h.setMark

@[simp] theorem setMark_mark_same (h : lit < s.marks.size) :
    (s.setMark lit value).mark lit = value := by
  simpa [State.setMark, State.mark] using Array.getElem!_set!_self s.marks lit value h

theorem setMark_mark_other (different : lit ≠ other) :
    (s.setMark lit value).mark other = s.mark other := by
  simpa [State.setMark, State.mark] using Array.getElem!_set!_ne s.marks lit other value different

@[simp] theorem unassign_mark_same (h : lit < s.marks.size) :
    (s.unassign lit).mark lit = 0 := setMark_mark_same h

theorem unassign_mark_other (different : lit ≠ other) :
    (s.unassign lit).mark other = s.mark other := setMark_mark_other different

theorem setMark_falseAssignment (bounds : lit < s.marks.size) (nonzero : value ≠ 0)
    (opposite : s.mark lit.negate = 0) : FalseAssignment (s.setMark lit value) lit := by
  constructor
  · simpa only [setMark_mark_same bounds] using nonzero
  · simpa only [setMark_mark_other (Ne.symm (negate_ne lit))] using opposite

theorem ArrayBounds.assign (h : ArrayBounds s) : ArrayBounds (s.assign clauseId root) := by
  rcases h with ⟨hf, hm, hr, hp, ht, hprev, hn⟩
  constructor <;> simp_all [State.assign]

theorem ArrayBounds.decide (h : ArrayBounds s) : ArrayBounds (s.decide var) := by
  rcases h with ⟨hf, hm, hr, hp, ht, hprev, hn⟩
  constructor <;> simp_all [State.decide]

theorem TrailBounds.assign (h : TrailBounds s) (space : s.assigned < s.nVars) :
    TrailBounds (s.assign clauseId root) := by
  rcases h with ⟨hfp, hpa, han⟩
  constructor <;> simp_all [State.assign] <;> omega

theorem TrailBounds.decide (h : TrailBounds s) (space : s.assigned < s.nVars) :
    TrailBounds (s.decide var) := by
  rcases h with ⟨hfp, hpa, han⟩
  constructor <;> simp_all [State.decide] <;> omega

theorem assign_trail_last (space : s.assigned < s.trail.size) :
    (s.assign clauseId root).trail[s.assigned]! = Lit.negate (s.db clauseId) := by
  exact Array.getElem!_set!_self s.trail s.assigned _ space

theorem assign_trail_prefix (before : i < s.assigned) :
    (s.assign clauseId root).trail[i]! = s.trail[i]! := by
  exact Array.getElem!_set!_ne s.trail s.assigned i _ (by omega)

theorem assign_reason (bound : Lit.var (s.db clauseId) < s.reasons.size) :
    (s.assign clauseId root).reason (s.db clauseId) = clauseId := by
  exact Array.getElem!_set!_self s.reasons _ _ bound

theorem assign_phase (bound : Lit.var (s.db clauseId) < s.phases.size) :
    (s.assign clauseId root).phases[Lit.var (s.db clauseId)]! = ((s.db clauseId) % 2 == 0) := by
  exact Array.getElem!_set!_self s.phases _ _ bound

theorem decide_trail_prefix (before : i < s.assigned) :
    (s.decide var).trail[i]! = s.trail[i]! := by
  exact Array.getElem!_set!_ne s.trail s.assigned i _ (by omega)

theorem decide_reason (bound : var < s.reasons.size) :
    (s.decide var).reasons[var]! = 0 := by
  exact Array.getElem!_set!_self s.reasons _ _ bound

@[simp] theorem decide_phases : (s.decide var).phases = s.phases := rfl

end MicrosatLean.Verification.Implementation.Representation
