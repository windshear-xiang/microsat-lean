import MicrosatLean.Faithful.Verification.Regions
import MicrosatLean.Faithful.Verification.Counting
import MicrosatLean.Faithful.Verification.Assign

/-!
# Pushing a literal on the trail

`assign` (C:42–47) and the decision (C:177–179) both push one false literal `x` on the
trail: `falseStack[assigned] = x` and `assigned` moves up, `false[x]` gets a tag,
`reason[abs x]` a reason, and `model[abs x]` agrees with `x`. `Push` describes this
change; the lemmas here rebuild the invariant parts that read the trail.
-/

namespace MicrosatLean.Faithful.Verification

/-- `T` is `S` with the false literal `x` pushed on the trail, tagged `tag`, with reason
value `rv`. No other cell or field changes. -/
structure Push (S T : solver) (x tag rv : CInt) : Prop where
  fields : ∃ DB, T = { S with DB := DB, assigned := S.assigned + 1 }
  top : T.ld S.assigned = x
  tag_eq : T.ld (S.false + x) = tag
  reason_eq : T.ld (S.reason + abs x) = rv
  model_iff : T.ld (S.model + abs x) ≠ 0 ↔ x < 0
  same : ∀ q, 0 ≤ q → q ≠ S.assigned → q ≠ S.false + x → q ≠ S.reason + abs x →
    q ≠ S.model + abs x → T.ld q = S.ld q

/-- `x` can be pushed on `S`'s trail: a literal of the problem whose variable is
unassigned. -/
structure Fresh (S : solver) (x : CInt) : Prop where
  layout : Layout S
  trail : Trail S
  lit : InRange S.nVars x
  free : ∀ i < trailLen S, abs (trailAt S i) ≠ abs x

section
variable {S T : solver} {x tag rv : CInt}

theorem Push.shape (hp : Push S T x tag rv) : SameShape S T := by
  obtain ⟨DB, rfl⟩ := hp.fields; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The fields a push keeps. -/
theorem Push.keeps (hp : Push S T x tag rv) :
    T.assigned = S.assigned + 1 ∧ T.forced = S.forced ∧ T.processed = S.processed ∧
    T.head = S.head ∧ T.mem_used = S.mem_used ∧ T.mem_fixed = S.mem_fixed ∧
    T.nLemmas = S.nLemmas ∧ T.maxLemmas = S.maxLemmas ∧ T.mem_max = S.mem_max := by
  obtain ⟨DB, rfl⟩ := hp.fields; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The numbers `omega` needs about a push. -/
theorem Fresh.num (hf : Fresh S x) :
    S.falseStack ≤ S.assigned ∧ S.assigned ≤ S.falseStack + S.nVars ∧ 1 ≤ S.nVars ∧
    x ≠ 0 ∧ -S.nVars ≤ x ∧ x ≤ S.nVars ∧ 1 ≤ abs x ∧ abs x ≤ S.nVars := by
  have t := hf.trail
  have h1 := t.forced_le; have h2 := t.processed_le; have h3 := t.assigned_le; have h4 := t.len_le
  have hx := inRange_iff.mp hf.lit
  have hn := hf.layout.nVars_pos
  simp only [trailLen] at h4
  refine ⟨by omega, by omega, hn, hx.1, hx.2.1, hx.2.2, ?_, ?_⟩ <;>
    rcases abs_cases x with ⟨_, e⟩ | ⟨_, e⟩ <;> omega

theorem Push.trailLen_eq (hp : Push S T x tag rv) (hf : Fresh S x) :
    trailLen T = trailLen S + 1 := by
  have := hf.num
  obtain ⟨DB, rfl⟩ := hp.fields
  simp only [trailLen]; omega

/-- Cells below the top of the trail are unchanged. -/
theorem Push.trailAt_lt (hp : Push S T x tag rv) (hf : Fresh S x) {i : Nat} (hi : i < trailLen S) :
    trailAt T i = trailAt S i := by
  have := hf.num; have hn := hf.layout.num
  simp only [trailAt, hp.shape.falseStack]
  simp only [trailLen] at hi
  exact hp.same _ (by omega) (by omega) (by omega) (by omega) (by omega)

theorem Push.trailAt_top (hp : Push S T x tag rv) (hf : Fresh S x) : trailAt T (trailLen S) = x := by
  have := hf.num
  simp only [trailAt, hp.shape.falseStack]
  rw [show S.falseStack + (trailLen S : CInt) = S.assigned by simp only [trailLen]; omega]
  exact hp.top

/-- The literals below the top are those of `S`'s trail. -/
theorem Fresh.trail_lit (hf : Fresh S x) {i : Nat} (hi : i < trailLen S) :
    trailAt S i ≠ 0 ∧ -S.nVars ≤ trailAt S i ∧ trailAt S i ≤ S.nVars ∧
    abs (trailAt S i) ≠ abs x ∧ trailAt S i ≠ x ∧ trailAt S i ≠ -x := by
  have hl := inRange_iff.mp (hf.trail.lit i hi)
  have hfr := hf.free i hi
  refine ⟨hl.1, hl.2.1, hl.2.2, hfr, fun he => hfr (by rw [he]), fun he => hfr (by rw [he, abs_neg'])⟩

/-- `false` flags of other literals are unchanged. -/
theorem Push.flag_ne (hp : Push S T x tag rv) (hf : Fresh S x) {lit : CInt}
    (hl : InRange S.nVars lit) (hne : lit ≠ x) : flag T lit = flag S lit := by
  have := hf.num; have hn := hf.layout.num; have hl' := inRange_iff.mp hl
  simp only [flag, hp.shape.false]
  apply hp.same _ (by omega) (by omega) (by omega) (by omega) (by omega)

theorem Push.flag_top (hp : Push S T x tag rv) : flag T x = tag := by
  simp only [flag, hp.shape.false]; exact hp.tag_eq

/-- Reasons of the old trail literals are unchanged. -/
theorem Push.reasonOf_lt (hp : Push S T x tag rv) (hf : Fresh S x) {i : Nat} (hi : i < trailLen S) :
    reasonOf T (trailAt T i) = reasonOf S (trailAt S i) := by
  have := hf.num; have hn := hf.layout.num; have ht := hf.trail_lit hi
  rw [hp.trailAt_lt hf hi]
  simp only [reasonOf, hp.shape.reason]
  have ha : 1 ≤ abs (trailAt S i) ∧ abs (trailAt S i) ≤ S.nVars := by
    rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  apply hp.same _ (by omega) (by omega) (by omega) (by omega) (by omega)

theorem Push.reasonOf_top (hp : Push S T x tag rv) (hf : Fresh S x) :
    reasonOf T (trailAt T (trailLen S)) = rv := by
  rw [hp.trailAt_top hf]; simp only [reasonOf, hp.shape.reason]; exact hp.reason_eq

theorem Push.isDecision_lt (hp : Push S T x tag rv) (hf : Fresh S x) {i : Nat} (hi : i < trailLen S) :
    IsDecision T i ↔ IsDecision S i := by
  simp only [IsDecision, hp.reasonOf_lt hf hi]

theorem Push.isDecision_top (hp : Push S T x tag rv) (hf : Fresh S x) :
    IsDecision T (trailLen S) ↔ rv = 0 := by
  simp only [IsDecision, hp.reasonOf_top hf]

theorem Push.rootLevel_lt (hp : Push S T x tag rv) (hf : Fresh S x) {i : Nat} (hi : i < trailLen S) :
    RootLevel T i ↔ RootLevel S i :=
  ⟨fun h k hk => (not_congr (hp.isDecision_lt hf (by omega))).mp (h k hk),
   fun h k hk => (not_congr (hp.isDecision_lt hf (by omega))).mpr (h k hk)⟩

theorem Push.rootLevel_top (hp : Push S T x tag rv) (hf : Fresh S x) :
    RootLevel T (trailLen S) ↔ (∀ k < trailLen S, ¬ IsDecision S k) ∧ rv ≠ 0 := by
  constructor
  · intro h
    refine ⟨fun k hk => (not_congr (hp.isDecision_lt hf hk)).mp (h k (by omega)), fun h0 =>
      h (trailLen S) (Nat.le_refl _) ((hp.isDecision_top hf).mpr h0)⟩
  · rintro ⟨h1, h2⟩ k hk
    rcases Nat.lt_or_ge k (trailLen S) with hk' | hk'
    · exact (not_congr (hp.isDecision_lt hf hk')).mpr (h1 k hk')
    · have : k = trailLen S := by omega
      subst this; exact (not_congr (hp.isDecision_top hf)).mpr h2

theorem Push.falseAt_lt (hp : Push S T x tag rv) (hf : Fresh S x) {lit : CInt} {j : Nat}
    (h : FalseAt S lit j) : FalseAt T lit j :=
  ⟨by rw [hp.trailLen_eq hf]; exact Nat.lt_succ_of_lt h.1, by rw [hp.trailAt_lt hf h.1]; exact h.2⟩

theorem Push.sameLevel_lt (hp : Push S T x tag rv) (hf : Fresh S x) {p q : Nat} (hq : q < trailLen S)
    (h : SameOrLowerLevel S p q) : SameOrLowerLevel T p q :=
  fun k h1 h2 => (not_congr (hp.isDecision_lt hf (by omega))).mpr (h k h1 h2)

/-- The trail after a push, given that the tag is `IMPLIED` exactly at the root (C:44). -/
theorem Push.trail (hp : Push S T x tag rv) (hf : Fresh S x)
    (htag : (RootLevel T (trailLen S) → tag = IMPLIED) ∧ (¬ RootLevel T (trailLen S) → tag = 1)) :
    Trail T := by
  have hn := hf.num
  have ht := hf.trail
  have hlen := hp.trailLen_eq hf
  obtain ⟨hA, hF, hP, -⟩ := hp.keeps
  have split : ∀ i < trailLen T, i < trailLen S ∨ i = trailLen S := fun i hi => by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF, hp.shape.falseStack]; exact ht.forced_le
  · rw [hF, hP]; exact ht.processed_le
  · rw [hP, hA]; have := ht.assigned_le; omega
  · rw [hlen, hp.shape.nVars]
    have := card_lt_of_distinct (N := S.nVars.toNat) (m := trailLen S)
      (fun i => (abs (trailAt S i)).toNat)
      (fun i hi => by have := hf.trail_lit hi; rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
      (fun i hi j hj he => ht.distinct i hi j hj (by
        have := hf.trail_lit hi; have := hf.trail_lit hj
        rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;>
          rcases abs_cases (trailAt S j) with ⟨_, e'⟩ | ⟨_, e'⟩ <;> omega))
      (v := (abs x).toNat) (by omega)
      (fun i hi he => hf.free i hi (by
        have := hf.trail_lit hi; rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega))
    omega
  · intro i hi
    rw [hp.shape.nVars]
    rcases split i hi with hi | rfl
    · rw [hp.trailAt_lt hf hi]; exact ht.lit i hi
    · rw [hp.trailAt_top hf]; exact hf.lit
  · intro i hi j hj he
    rcases split i hi with hi | rfl <;> rcases split j hj with hj | rfl
    · rw [hp.trailAt_lt hf hi, hp.trailAt_lt hf hj] at he; exact ht.distinct i hi j hj he
    · rw [hp.trailAt_lt hf hi, hp.trailAt_top hf] at he; exact absurd he (hf.free i hi)
    · rw [hp.trailAt_lt hf hj, hp.trailAt_top hf] at he; exact absurd he.symm (hf.free j hj)
    · rfl
  · intro i hi hr
    rcases split i hi with hi | rfl
    · rw [hp.trailAt_lt hf hi, hp.flag_ne hf (ht.lit i hi) (hf.trail_lit hi).2.2.2.2.1]
      exact ht.flag_root i hi ((hp.rootLevel_lt hf hi).mp hr)
    · rw [hp.trailAt_top hf, hp.flag_top]; exact htag.1 hr
  · intro i hi hr
    rcases split i hi with hi | rfl
    · rw [hp.trailAt_lt hf hi, hp.flag_ne hf (ht.lit i hi) (hf.trail_lit hi).2.2.2.2.1]
      exact ht.flag_level i hi (fun h => hr ((hp.rootLevel_lt hf hi).mpr h))
    · rw [hp.trailAt_top hf, hp.flag_top]; exact htag.2 hr
  · intro lit hl hoff
    rw [hp.shape.nVars] at hl
    have hne : lit ≠ x := fun he => hoff (trailLen S) (by omega) (by rw [hp.trailAt_top hf, he])
    rw [hp.flag_ne hf hl hne]
    exact ht.flag_off lit hl fun i hi he => hoff i (by omega) (by rw [hp.trailAt_lt hf hi]; exact he)
  · intro i hi
    rcases split i hi with hi | rfl
    · have hm := hf.layout.num; have hl := hf.trail_lit hi
      have ha : 1 ≤ abs (trailAt S i) ∧ abs (trailAt S i) ≤ S.nVars := by
        rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
      rw [hp.trailAt_lt hf hi, hp.shape.model,
        hp.same _ (by omega) (by omega) (by omega) (by omega) (by omega)]
      exact ht.model i hi
    · rw [hp.trailAt_top hf, hp.shape.model]; exact hp.model_iff
  · have hm := hf.layout.num
    simp only [flag, hp.shape.false]
    rw [hp.same (S.false + 0) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact ht.flag_zero
  · intro i hi
    have hi' : i < forcedPos S := by simp only [forcedPos, hF, hp.shape.falseStack] at hi ⊢; exact hi
    have hfl : forcedPos S ≤ trailLen S := by
      simp only [forcedPos, trailLen]; have := ht.processed_le; have := ht.assigned_le; omega
    exact (hp.rootLevel_lt hf (by omega)).mpr (ht.forced_root i hi')

/-- A push keeps the layout, the database, the watch lists and the order: it writes
only into the trail's arrays. -/
theorem Push.frames {input : Input} {db : Records} {vs : List CInt} (hp : Push S T x tag rv)
    (hf : Fresh S x) (hd : Database input S db) (hw : WatchLists S db) (ho : OrderList S vs) :
    Layout T ∧ Database input T db ∧ WatchLists T db ∧ OrderList T vs := by
  have hn := hf.num; have hm := hf.layout.num
  obtain ⟨-, -, -, hH, hU, hFx, hN, -⟩ := hp.keeps
  have high : ∀ q, 8 * S.nVars + 6 ≤ q → T.ld q = S.ld q := fun q hq =>
    hp.same q (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨hf.layout.frame hp.shape (high _ (by simp only [clausesAt]; omega)),
    hd.frame hp.shape hU hFx hN fun q hq => high q (by simp only [clausesAt] at hq; omega),
    hw.frame hf.layout hd hp.shape high, ho.frame hf.layout hp.shape hH fun q h1 h2 =>
      hp.same q (by omega) (by omega) (by omega) (by omega) (by omega)⟩

/-- Root literals stay entailed; the new one must be, if it is at the root. -/
theorem Push.rootEntailed {input : Input} (hp : Push S T x tag rv) (hf : Fresh S x)
    (h : RootEntailed input S) (hnew : RootLevel T (trailLen S) → input.Entails [-x]) :
    RootEntailed input T := by
  intro i hi hr
  rw [hp.trailLen_eq hf] at hi
  rcases Nat.lt_or_ge i (trailLen S) with hi' | hi'
  · rw [hp.trailAt_lt hf hi']; exact h i hi' ((hp.rootLevel_lt hf hi').mp hr)
  · have : i = trailLen S := by omega
    subst this; rw [hp.trailAt_top hf]; exact hnew hr

/-- True units stay true. -/
theorem Push.units {db : Records} (hp : Push S T x tag rv) (hf : Fresh S x) (h : UnitsTrue S db) :
    UnitsTrue T db := by
  intro r hr h1
  obtain ⟨i, hi, hroot, he⟩ := h r hr h1
  exact ⟨i, by rw [hp.trailLen_eq hf]; omega, (hp.rootLevel_lt hf hi).mpr hroot,
    by rw [hp.trailAt_lt hf hi]; exact he⟩

/-- Reasons stay; the new literal needs one unless it is a decision (`rv = 0`) or below
`forced`. -/
theorem Push.reasons {db : Records} (hp : Push S T x tag rv) (hf : Fresh S x) (h : Reasons S db)
    (hnew : rv ≠ 0 → forcedPos S ≤ trailLen S →
      ∃ r ∈ db.all, rv = 1 + r.1 ∧ r.2[0]? = some (-x) ∧
        (∀ lit ∈ r.2.drop 1, ∃ j < trailLen S, FalseAt S lit j) ∧
        (¬ RootLevel T (trailLen S) → ∃ lit ∈ r.2.drop 1, ∃ j < trailLen S, FalseAt S lit j ∧
          ∀ k, j < k → k < trailLen S → ¬ IsDecision S k)) :
    Reasons T db := by
  have hfp : forcedPos T = forcedPos S := by
    simp only [forcedPos, hp.keeps.2.1, hp.shape.falseStack]
  intro i hi hfi hrn
  rw [hp.trailLen_eq hf] at hi
  rw [hfp] at hfi
  rcases Nat.lt_or_ge i (trailLen S) with hi' | hi'
  · rw [hp.reasonOf_lt hf hi'] at hrn ⊢
    obtain ⟨r, hr, e1, e2, e3, e4⟩ := h i hi' hfi hrn
    refine ⟨r, hr, e1, by rw [hp.trailAt_lt hf hi']; exact e2, fun lit hl => ?_, fun hnr => ?_⟩
    · obtain ⟨j, hj, hfa⟩ := e3 lit hl; exact ⟨j, hj, hp.falseAt_lt hf hfa⟩
    · obtain ⟨lit, hl, j, hj, hfa, hsl⟩ := e4 (fun h' => hnr ((hp.rootLevel_lt hf hi').mpr h'))
      exact ⟨lit, hl, j, hj, hp.falseAt_lt hf hfa, hp.sameLevel_lt hf hi' hsl⟩
  · have : i = trailLen S := by omega
    subst this
    rw [hp.reasonOf_top hf] at hrn ⊢
    obtain ⟨r, hr, e1, e2, e3, e4⟩ := hnew hrn hfi
    refine ⟨r, hr, e1, by rw [hp.trailAt_top hf]; exact e2, fun lit hl => ?_,
      fun hnr => ?_⟩
    · obtain ⟨j, hj, hfa⟩ := e3 lit hl; exact ⟨j, hj, hp.falseAt_lt hf hfa⟩
    · obtain ⟨lit, hl, j, hj, hfa, hsl⟩ := e4 hnr
      refine ⟨lit, hl, j, hj, hp.falseAt_lt hf hfa, fun k h1 h2 => ?_⟩
      rcases Nat.lt_or_ge k (trailLen S) with hk | hk
      · exact (not_congr (hp.isDecision_lt hf hk)).mpr (hsl k h1 hk)
      · have : k = trailLen S := by omega
        subst this; exact (not_congr (hp.isDecision_top hf)).mpr hrn

/-- The watched-literal invariant only looks below `processed`, which a push keeps. -/
theorem Push.watched {db : Records} (hp : Push S T x tag rv) (hf : Fresh S x) (h : WatchedTrue S db) :
    WatchedTrue T db := by
  have hpp : processedPos T = processedPos S := by
    simp only [processedPos, hp.keeps.2.2.1, hp.shape.falseStack]
  have hle : processedPos S ≤ trailLen S := by
    simp only [processedPos, trailLen]; have := hf.trail.assigned_le; omega
  intro r hr h2 w o hwo p hpl hfa
  rw [hpp] at hpl
  have hfa' : FalseAt S r.2[w]! p := ⟨by omega, by rw [← hp.trailAt_lt hf (by omega)]; exact hfa.2⟩
  obtain ⟨q, hq, hsl⟩ := h r hr h2 w o hwo p hpl hfa'
  exact ⟨q, hp.falseAt_lt hf hq, hp.sameLevel_lt hf hq.1 hsl⟩

/-- Assigned variables stay assigned. -/
theorem Push.assigned {v : CInt} (hp : Push S T x tag rv) (hf : Fresh S x) (h : Assigned S v) :
    Assigned T v := by
  obtain ⟨i, hi, he⟩ := h
  exact ⟨i, by rw [hp.trailLen_eq hf]; omega, by rw [hp.trailAt_lt hf hi]; exact he⟩

end

/-- `assign` (C:42–47) pushes the negation of the clause's first literal, tagged `IMPLIED`
when `forced` is set, with the clause as its reason. Used by `propagate` and `analyze`. -/
theorem assign_push {S : solver} (hl : Layout S) (ht : Trail S) {c f : CInt} (hc : 0 ≤ c)
    (hlit : InRange S.nVars (S.ld c)) :
    Push S (assign S c f) (-(S.ld c)) (if f != 0 then IMPLIED else 1) (1 + c) := by
  have hn := hl.num; have hn1 := hl.nVars_pos
  have hl' := inRange_iff.mp hlit
  have ha : 1 ≤ abs (S.ld c) ∧ abs (S.ld c) ≤ S.nVars := by
    rcases abs_cases (S.ld c) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hA : S.falseStack ≤ S.assigned ∧ S.assigned ≤ S.falseStack + S.nVars := by
    have := ht.forced_le; have := ht.processed_le; have := ht.assigned_le; have := ht.len_le
    simp only [trailLen] at this; omega
  have hld := fun q (hq : 0 ≤ q) => assign_ld S c f hq (by omega) (by omega) (by omega) (by omega)
  obtain ⟨DB, hD⟩ := assign_fields S c f
  refine ⟨⟨DB, hD⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hld _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  · rw [hld _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
  · rw [abs_neg', hld _ (by omega), if_neg (by omega), if_pos rfl]
  · rw [abs_neg', hld _ (by omega), if_pos rfl]
    by_cases hp : S.ld c > 0
    · rw [if_pos hp]; exact ⟨fun _ => by omega, fun _ => by decide⟩
    · rw [if_neg hp]; exact ⟨fun h => absurd rfl h, fun h => by omega⟩
  · intro q hq h1 h2 h3 h4
    rw [abs_neg'] at h3 h4
    rw [hld q hq, if_neg h4, if_neg h3, if_neg h1, if_neg h2]

end MicrosatLean.Faithful.Verification
