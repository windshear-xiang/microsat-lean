import MicrosatLean.Faithful.Verification.Regions

/-!
# Changes above the trail arrays

Clause visits and `addClause` write only into the records and the watch heads, which lie
above the trail's arrays (`false` ends at `8n + 5`). Then every trail notion is unchanged.
-/

namespace MicrosatLean.Faithful.Verification

/-- `T` has `S`'s pointers, trail fields and every cell below the `first` array. -/
structure LowSame (S T : solver) : Prop where
  shape : SameShape S T
  forced : T.forced = S.forced
  processed : T.processed = S.processed
  assigned : T.assigned = S.assigned
  low : ∀ q, 0 ≤ q → q < 8 * S.nVars + 6 → T.ld q = S.ld q

set_option linter.unusedSectionVars false

section
variable {S T : solver} (h : LowSame S T) (ht : Trail S) (hl : Layout S)
include h ht hl

theorem LowSame.trailLen : trailLen T = trailLen S := by
  simp only [Verification.trailLen, h.assigned, h.shape.falseStack]

theorem LowSame.forcedPos : forcedPos T = forcedPos S := by
  simp only [Verification.forcedPos, h.forced, h.shape.falseStack]

theorem LowSame.processedPos : processedPos T = processedPos S := by
  simp only [Verification.processedPos, h.processed, h.shape.falseStack]

theorem LowSame.trailAt {i : Nat} (hi : i < Verification.trailLen S) : Verification.trailAt T i = Verification.trailAt S i := by
  have hn := hl.num; have hn1 := hl.nVars_pos
  have h1 := ht.len_le; have := ht.forced_le; have := ht.processed_le; have := ht.assigned_le
  simp only [Verification.trailLen] at hi h1
  simp only [Verification.trailAt, h.shape.falseStack]; exact h.low _ (by omega) (by omega)

theorem LowSame.flag {lit : CInt} (h1 : -S.nVars ≤ lit) (h2 : lit ≤ S.nVars) : Verification.flag T lit = Verification.flag S lit := by
  have hn := hl.num
  simp only [Verification.flag, h.shape.false]; exact h.low _ (by omega) (by omega)

theorem LowSame.reasonOf {lit : CInt} (h1 : -S.nVars ≤ lit) (h2 : lit ≤ S.nVars) : Verification.reasonOf T lit = Verification.reasonOf S lit := by
  have hn := hl.num; have := hl.nVars_pos
  simp only [Verification.reasonOf, h.shape.reason]
  exact h.low _ (by rcases abs_cases lit with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
    (by rcases abs_cases lit with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)

theorem LowSame.isDecision {i : Nat} (hi : i < Verification.trailLen S) : IsDecision T i ↔ IsDecision S i := by
  have := inRange_iff.mp (ht.lit i hi)
  simp only [IsDecision]; rw [h.trailAt ht hl hi, h.reasonOf ht hl this.2.1 this.2.2]

theorem LowSame.rootLevel {i : Nat} (hi : i < Verification.trailLen S) : RootLevel T i ↔ RootLevel S i :=
  ⟨fun h' k hk => (not_congr (h.isDecision ht hl (by omega))).mp (h' k hk),
   fun h' k hk => (not_congr (h.isDecision ht hl (by omega))).mpr (h' k hk)⟩

theorem LowSame.falseAt {lit : CInt} {j : Nat} : FalseAt T lit j ↔ FalseAt S lit j := by
  constructor
  · rintro ⟨hj, he⟩; rw [h.trailLen ht hl] at hj; exact ⟨hj, by rw [← h.trailAt ht hl hj]; exact he⟩
  · rintro ⟨hj, he⟩; exact ⟨by rw [h.trailLen ht hl]; exact hj, by rw [h.trailAt ht hl hj]; exact he⟩

theorem LowSame.sameLevel {p q : Nat} (hq : q < Verification.trailLen S) :
    SameOrLowerLevel T p q ↔ SameOrLowerLevel S p q :=
  ⟨fun h' k h1 h2 => (not_congr (h.isDecision ht hl (by omega))).mp (h' k h1 h2),
   fun h' k h1 h2 => (not_congr (h.isDecision ht hl (by omega))).mpr (h' k h1 h2)⟩

/-- The trail facts carry over. -/
theorem LowSame.trail : Trail T := by
  have hn := hl.num; have hn1 := hl.nVars_pos
  have hlitS : ∀ i < Verification.trailLen S, -S.nVars ≤ Verification.trailAt S i ∧ Verification.trailAt S i ≤ S.nVars := fun i hi => by
    have := inRange_iff.mp (ht.lit i hi); omega
  refine ⟨by rw [h.forced, h.shape.falseStack]; exact ht.forced_le, by rw [h.forced, h.processed]; exact ht.processed_le,
    by rw [h.processed, h.assigned]; exact ht.assigned_le, by rw [h.trailLen ht hl, h.shape.nVars]; exact ht.len_le,
    fun i hi => ?_, fun i hi j hj he => ?_, fun i hi hr => ?_, fun i hi hr => ?_, fun lit hl' hoff => ?_,
    fun i hi => ?_, ?_, fun i hi => ?_⟩
  · rw [h.trailLen ht hl] at hi; rw [h.trailAt ht hl hi, h.shape.nVars]; exact ht.lit i hi
  · rw [h.trailLen ht hl] at hi hj; rw [h.trailAt ht hl hi, h.trailAt ht hl hj] at he
    exact ht.distinct i hi j hj he
  · rw [h.trailLen ht hl] at hi
    rw [h.trailAt ht hl hi, h.flag ht hl (hlitS i hi).1 (hlitS i hi).2]
    exact ht.flag_root i hi ((h.rootLevel ht hl hi).mp hr)
  · rw [h.trailLen ht hl] at hi
    rw [h.trailAt ht hl hi, h.flag ht hl (hlitS i hi).1 (hlitS i hi).2]
    exact ht.flag_level i hi fun h' => hr ((h.rootLevel ht hl hi).mpr h')
  · rw [h.shape.nVars] at hl'
    have := inRange_iff.mp hl'
    rw [h.flag ht hl this.2.1 this.2.2]
    exact ht.flag_off lit hl' fun i hi he => hoff i (by rw [h.trailLen ht hl]; exact hi) (by rw [h.trailAt ht hl hi]; exact he)
  · rw [h.trailLen ht hl] at hi
    have := hlitS i hi
    rw [h.trailAt ht hl hi, h.shape.model, h.low _ (by rcases abs_cases (Verification.trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
      (by rcases abs_cases (Verification.trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)]
    exact ht.model i hi
  · rw [h.flag ht hl (by omega) (by omega)]; exact ht.flag_zero
  · rw [h.forcedPos ht hl] at hi
    have : Verification.forcedPos S ≤ Verification.trailLen S := by
      simp only [Verification.forcedPos, Verification.trailLen]; have := ht.processed_le; have := ht.assigned_le; omega
    exact (h.rootLevel ht hl (by omega)).mpr (ht.forced_root i hi)

/-- Root entailment carries over. -/
theorem LowSame.root {input : Input} (hr : RootEntailed input S) : RootEntailed input T := by
  intro i hi hroot
  rw [h.trailLen ht hl] at hi
  rw [h.trailAt ht hl hi]; exact hr i hi ((h.rootLevel ht hl hi).mp hroot)

/-- The decision order carries over. -/
theorem LowSame.order {vs : List CInt} (ho : OrderList S vs) (hH : T.head = S.head) : OrderList T vs := by
  have hn := hl.num; have := hl.nVars_pos
  exact ho.frame hl h.shape hH fun q h1 h2 => h.low q (by omega) (by omega)

end

end MicrosatLean.Faithful.Verification
