import MicrosatLean.Verification.Implementation.Native.Analysis.Implied
import MicrosatLean.Verification.Implementation.Native.Representation.Semantics

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation
open Std.Sat

/-- Membership in the fixed original trail, including entries subsequently
popped during conflict analysis. The active `assigned` cursor is not used. -/
def TrailMember (snapshot : State) (count : Nat) (lit : Lit) : Prop :=
  ∃ i, i < count ∧ snapshot.trail[i]! = lit

/-- Concrete reason clauses form a DAG in the original trail order. Their
head is the assigned true literal; every tail literal is an earlier false one.
Entailment concerns the original input, not the current MARK assumptions. -/
structure ReasonGraph (formula : Std.Sat.CNF Nat) (snapshot : State) (count : Nat)
    (rank : Lit → Nat) : Prop where
  countBound : count ≤ snapshot.trail.size
  ranks : ∀ i, i < count → rank snapshot.trail[i]! = i
  distinctVariables : ∀ i j, i < count → j < count →
    snapshot.trail[i]!.var = snapshot.trail[j]!.var → i = j
  clauses : ∀ i, i < count → snapshot.reason snapshot.trail[i]! ≠ 0 →
    ∃ lits, PackedClause snapshot (snapshot.reason snapshot.trail[i]!) lits ∧
      0 < lits.size ∧ lits[0]! = snapshot.trail[i]!.negate ∧
      CNF.EntailsClause formula (clauseView lits) ∧
      ∀ j, 0 < j → j < lits.size →
        ∃ k, k < i ∧ snapshot.trail[k]! = lits[j]!

/-- Only the immutable reason data are shared with the snapshot. Analysis may
change cursors and heuristics independently of this semantic graph. -/
structure ReasonStorage (snapshot current : State) : Prop where
  arena : current.arena = snapshot.arena
  reasons : current.reasons = snapshot.reasons

theorem ReasonStorage.refl (s : State) : ReasonStorage s s := ⟨rfl, rfl⟩

theorem ReasonStorage.markFrame {snapshot before after : State}
    (storage : ReasonStorage snapshot before) (frame : MarkFrame before after) :
    ReasonStorage snapshot after :=
  ⟨frame.arena.trans storage.arena, frame.reasons.trans storage.reasons⟩

theorem ReasonStorage.db {snapshot current : State} (storage : ReasonStorage snapshot current)
    (i : Nat) : current.db i = snapshot.db i := by
  simp only [State.db, storage.arena]

theorem ReasonStorage.reason {snapshot current : State} (storage : ReasonStorage snapshot current)
    (lit : Lit) : current.reason lit = snapshot.reason lit := by
  simp only [State.reason, storage.reasons]

theorem ReasonGraph.clause_of_member {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank) {lit : Lit}
    (member : TrailMember snapshot count lit) (nondecision : snapshot.reason lit ≠ 0) :
    ∃ lits, PackedClause snapshot (snapshot.reason lit) lits ∧
      0 < lits.size ∧ lits[0]! = lit.negate ∧
      CNF.EntailsClause formula (clauseView lits) ∧
      ∀ j, 0 < j → j < lits.size →
        TrailMember snapshot count lits[j]! ∧ rank lits[j]! < rank lit := by
  obtain ⟨i, before, rfl⟩ := member
  obtain ⟨lits, packed, nonempty, head, entailed, earlier⟩ := graph.clauses i before nondecision
  refine ⟨lits, packed, nonempty, head, entailed, ?_⟩
  intro j positive bound
  obtain ⟨k, earlierIndex, equal⟩ := earlier j positive bound
  have beforeK := Nat.lt_trans earlierIndex before
  refine ⟨⟨k, beforeK, equal⟩, ?_⟩
  rw [← equal, graph.ranks k beforeK, graph.ranks i before]
  exact earlierIndex

theorem ReasonGraph.member_eq_of_rank {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} (graph : ReasonGraph formula snapshot count rank) {lit : Lit}
    (member : TrailMember snapshot count lit) {i : Nat}
    (position : rank lit = i) : lit = snapshot.trail[i]! := by
  obtain ⟨j, beforeJ, equal⟩ := member
  have rankJ := graph.ranks j beforeJ
  rw [equal, position] at rankJ
  have same : j = i := rankJ.symm
  simpa only [same] using equal.symm

/-- A bound excludes the candidate itself and every later original MARK leaf. -/
def EarlierLeavesFalse (rank : Lit → Nat) (leaves : Lit → Prop)
    (a : Nat → Bool) (bound : Nat) : Prop :=
  ∀ lit, leaves lit → rank lit < bound → Falsifies a lit

def LeafConsequence (formula : Std.Sat.CNF Nat) (rank : Lit → Nat) (leaves : Lit → Prop)
    (bound : Nat) (lit : Lit) : Prop :=
  ∀ a, CNF.Sat a formula → EarlierLeavesFalse rank leaves a bound → Falsifies a lit

abbrev DerivedLiteral (formula : Std.Sat.CNF Nat) (rank : Lit → Nat) (leaves : Lit → Prop)
    (lit : Lit) : Prop := LeafConsequence formula rank leaves (rank lit) lit

theorem leafConsequence_of_leaf {formula : Std.Sat.CNF Nat} {rank : Lit → Nat} {leaves : Lit → Prop}
    {bound : Nat} {lit : Lit} (leaf : leaves lit) (earlier : rank lit < bound) :
    LeafConsequence formula rank leaves bound lit :=
  fun _ _ assumptions => assumptions lit leaf earlier

theorem LeafConsequence.mono {formula : Std.Sat.CNF Nat} {rank : Lit → Nat} {leaves : Lit → Prop}
    {small large : Nat} {lit : Lit} (h : LeafConsequence formula rank leaves small lit)
    (bound : small ≤ large) : LeafConsequence formula rank leaves large lit := by
  intro a model assumptions
  apply h a model
  intro leaf marked earlier
  exact assumptions leaf marked (Nat.lt_of_lt_of_le earlier bound)

/-- Soundness of expanding one actual reason after its tails have been
derived. The tail consequences will come from the concrete recursive scan. -/
theorem derived_of_reason {formula : Std.Sat.CNF Nat} {rank : Lit → Nat} {leaves : Lit → Prop}
    {lit : Lit} {lits : Array Lit} (_nonempty : 0 < lits.size)
    (head : lits[0]! = lit.negate) (entailed : CNF.EntailsClause formula (clauseView lits))
    (tails : ∀ j, 0 < j → j < lits.size →
      LeafConsequence formula rank leaves (rank lit) lits[j]!) :
    DerivedLiteral formula rank leaves lit := by
  intro a model assumptions
  have trueHead : a (literalView lit.negate).1 = (literalView lit.negate).2 := by
    apply Logic.forced_of_sat (entailed a model)
    intro viewed member different
    obtain ⟨encoded, encodedMember, equal⟩ := clauseView_mem.mp member
    obtain ⟨j, before, value⟩ := Array.mem_iff_getElem.mp encodedMember
    have value' : lits[j]! = encoded := by simpa only [getElem!_pos lits j before] using value
    by_cases first : j = 0
    · subst j
      exact False.elim (different (equal.symm.trans (congrArg literalView (value'.symm.trans head))))
    · have hf := tails j (by omega) before a model assumptions
      simpa only [Falsifies, value', equal] using hf
  have falseLit := (falsifies_negate_iff a lit.negate).mpr trueHead
  simpa only [negate_negate] using falseLit

/-- Tag 5 records only conservative failure. Tag 6 records an independently
justified consequence of strictly earlier original leaves. -/
structure ImpliedCache (formula : Std.Sat.CNF Nat) (snapshot : State) (count : Nat)
    (rank : Lit → Nat) (leaves : Lit → Prop) (s : State) : Prop where
  tags : ∀ lit, TrailMember snapshot count lit →
    s.mark lit = 0 ∨ s.mark lit = 1 ∨ s.mark lit = 2 ∨ s.mark lit = 5 ∨ s.mark lit = 6
  marked : ∀ lit, TrailMember snapshot count lit → s.mark lit = 2 → leaves lit
  cached : ∀ lit, TrailMember snapshot count lit → s.mark lit = 6 →
    DerivedLiteral formula rank leaves lit

private theorem cache_setMark {formula : Std.Sat.CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (cache : ImpliedCache formula snapshot count rank leaves s) (target value : Nat)
    (valueTag : value = 1 ∨ value = 5 ∨ value = 6)
    (sound : value = 6 → DerivedLiteral formula rank leaves target) :
    ImpliedCache formula snapshot count rank leaves (s.setMark target value) := by
  by_cases inBounds : target < s.marks.size
  · constructor
    · intro lit member
      by_cases same : target = lit
      · subst lit
        rw [setMark_mark_same inBounds]
        rcases valueTag with rfl | rfl | rfl <;> simp
      · rw [setMark_mark_other same]
        exact cache.tags lit member
    · intro lit member tag
      by_cases same : target = lit
      · subst lit
        rw [setMark_mark_same inBounds] at tag
        rcases valueTag with rfl | rfl | rfl <;> contradiction
      · rw [setMark_mark_other same] at tag
        exact cache.marked lit member tag
    · intro lit member tag
      by_cases same : target = lit
      · subst lit
        rw [setMark_mark_same inBounds] at tag
        exact sound tag
      · rw [setMark_mark_other same] at tag
        exact cache.cached lit member tag
  · simpa [State.setMark, Array.setIfInBounds, inBounds] using cache

theorem ImpliedCache.setMark_failed {formula : Std.Sat.CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (cache : ImpliedCache formula snapshot count rank leaves s) (lit : Lit) :
    ImpliedCache formula snapshot count rank leaves (s.setMark lit 5) :=
  cache_setMark cache lit 5 (Or.inr (Or.inl rfl)) (by intro impossible; contradiction)

theorem ImpliedCache.setMark_one {formula : Std.Sat.CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (cache : ImpliedCache formula snapshot count rank leaves s) (lit : Lit) :
    ImpliedCache formula snapshot count rank leaves (s.setMark lit 1) :=
  cache_setMark cache lit 1 (Or.inl rfl) (by intro impossible; contradiction)

theorem ImpliedCache.setMark_implied {formula : Std.Sat.CNF Nat} {snapshot s : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (cache : ImpliedCache formula snapshot count rank leaves s) {lit : Lit}
    (sound : DerivedLiteral formula rank leaves lit) :
    ImpliedCache formula snapshot count rank leaves (s.setMark lit 6) :=
  cache_setMark cache lit 6 (Or.inr (Or.inr rfl)) (fun _ => sound)

end MicrosatLean.Verification.Implementation.Native.Analysis
