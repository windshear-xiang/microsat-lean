import MicrosatLean.CDCL.State

namespace MicrosatLean.Verification.Implementation.Native.Representation

open CDCL

/-- A runtime literal names a declared, nonzero variable. -/
def LiteralBound (n : Nat) (lit : Lit) : Prop :=
  1 ≤ lit.var ∧ lit.var ≤ n

/-- Exact dimensions of the fixed-size indexed arrays. Arena allocation and
trail cursor ordering are separate invariants. -/
structure ArrayBounds (s : State) : Prop where
  firstSize : s.first.size = 2 * (s.nVars + 1)
  marksSize : s.marks.size = 2 * (s.nVars + 1)
  reasonsSize : s.reasons.size = s.nVars + 1
  phasesSize : s.phases.size = s.nVars + 1
  trailSize : s.trail.size = s.nVars + 1
  previousSize : s.previous.size = s.nVars + 1
  nextSize : s.next.size = s.nVars + 1

structure ArenaBounds (s : State) : Prop where
  reserved : 2 ≤ s.arena.size
  fixedLower : 2 ≤ s.fixed
  fixedUpper : s.fixed ≤ s.arena.size

structure TrailBounds (s : State) : Prop where
  forcedProcessed : s.forced ≤ s.processed
  processedAssigned : s.processed ≤ s.assigned
  assignedVars : s.assigned ≤ s.nVars

/-- A clause occupies its exact literal slice followed by a zero terminator.
The two preceding watch-link cells are in bounds because `clauseId ≥ 4`. -/
structure PackedClause (s : State) (clauseId : Nat) (lits : Array Lit) : Prop where
  startLower : 4 ≤ clauseId
  endBound : clauseId + lits.size < s.arena.size
  literals : ∀ i, i < lits.size → s.db (clauseId + i) = lits[i]!
  terminator : s.db (clauseId + lits.size) = 0
  wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit

/-- Marks may temporarily carry analysis tags, all of which still denote a
false literal. The complementary literal must remain unmarked. -/
def FalseAssignment (s : State) (lit : Lit) : Prop :=
  s.mark lit ≠ 0 ∧ s.mark lit.negate = 0

def ActiveTrail (s : State) : Prop :=
  ∀ i, i < s.assigned → LiteralBound s.nVars s.trail[i]! ∧
    FalseAssignment s s.trail[i]!

def DistinctTrailVariables (s : State) : Prop :=
  ∀ i j, i < s.assigned → j < s.assigned →
    s.trail[i]!.var = s.trail[j]!.var → i = j

def TrailPhases (s : State) : Prop :=
  ∀ i, i < s.assigned →
    s.phases[s.trail[i]!.var]! = (s.trail[i]! % 2 == 1)

/-- Reasons of assigned variables are decisions or valid clauses containing
the true literal. This does not require a reason to retain its watch order. -/
def ReasonClauses (s : State) : Prop :=
  ∀ i, i < s.assigned → s.reason s.trail[i]! = 0 ∨
    ∃ lits, PackedClause s (s.reason s.trail[i]!) lits ∧ s.trail[i]!.negate ∈ lits

/-- A concrete ordering of all variables. The head follows `previous` towards
zero; `next` is constrained only away from the head, whose unused slot can be
stale after a move-to-front update in the runtime implementation. -/
def MTFOrder (s : State) (order : List Nat) : Prop :=
  order.Nodup ∧ (∀ var, var ∈ order ↔ 1 ≤ var ∧ var ≤ s.nVars) ∧
  s.head = order.headD 0 ∧
  ∀ i, i < order.length →
    s.previous[order.getD i 0]! = order.getD (i + 1) 0 ∧
    (0 < i → s.next[order.getD i 0]! = order.getD (i - 1) 0)

def MTFCoverage (s : State) : Prop := ∃ order, MTFOrder s order

/-- A watch reference addresses one of the two link cells of a clause and
appears on a list for one of that clause's current watched literals. -/
def WatchEntry (s : State) (lit ref : Nat) : Prop :=
  4 ≤ watchClause ref ∧ watchClause ref + 1 < s.arena.size ∧
  watchLinkPos ref < s.arena.size ∧
  (s.db (watchClause ref) = lit ∨ s.db (watchClause ref + 1) = lit)

def WatchList (s : State) (lit : Lit) (refs : List Nat) : Prop :=
  refs.Nodup ∧ s.first[lit]! = refs.headD 0 ∧
  ∀ i, i < refs.length → WatchEntry s lit (refs.getD i 0) ∧
    s.db (watchLinkPos (refs.getD i 0)) = refs.getD (i + 1) 0

/-- The two fixed link cells occur at distinct watched heads. Their order may
swap, so this relation intentionally allows either permutation. -/
def ClauseWatches (heads : Nat → List Nat) (clauseId first second : Nat) : Prop :=
  first ≠ second ∧
    ((2 * clauseId ∈ heads first ∧ 2 * clauseId + 1 ∈ heads second) ∨
     (2 * clauseId ∈ heads second ∧ 2 * clauseId + 1 ∈ heads first))

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

end MicrosatLean.Verification.Implementation.Native.Representation
