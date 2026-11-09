import MicrosatLean.Faithful.Verification.Push
import MicrosatLean.Faithful.Verification.Assign
import Std.Tactic.Do

/-!
# `restart` (C:38–40)

`restart` unassigns every literal above `forced` and resets `processed`. What is
left is the root, so every part of `Settled` still holds.
-/

namespace MicrosatLean.Faithful.Verification

open Std.Do
set_option mvcgen.warning false

/-- `restart`'s loop after popping down to `S'.assigned`: only `DB` and `assigned`
changed, the popped literals' flags are 0, and no other cell changed. -/
def Popped (S S' : solver) : Prop :=
  (∃ DB, S' = { S with DB := DB, assigned := S'.assigned }) ∧
  S.forced ≤ S'.assigned ∧ S'.assigned ≤ S.assigned ∧
  (∀ q, 0 ≤ q → (∀ i, (S'.assigned - S.falseStack).toNat ≤ i → i < trailLen S →
    q ≠ S.false + trailAt S i) → S'.ld q = S.ld q) ∧
  (∀ i, (S'.assigned - S.falseStack).toNat ≤ i → i < trailLen S → S'.ld (S.false + trailAt S i) = 0)

/-- One iteration of `restart`'s loop (C:39): pop the top literal and clear its flag. -/
theorem popped_step {S S' : solver} (ht : Trail S) (hl : Layout S) (hp : Popped S S')
    (hc : S.forced < S'.assigned) :
    Popped S (unassign ({ S' with assigned := S'.assigned - 1 } : solver) (S'.ld (S'.assigned - 1))) := by
  obtain ⟨⟨DB, hS'⟩, h1, h2, hsame, hzero⟩ := hp
  have hn := hl.num
  have hF := ht.forced_le; have hP := ht.processed_le; have hA := ht.assigned_le
  have hlen := ht.len_le; simp only [trailLen] at hlen
  have hn1 := hl.nVars_pos
  generalize ha : S'.assigned = a at hS' h1 h2 hsame hzero hc ⊢
  subst hS'
  -- the popped literal is trail entry `pos`
  have hpos : ((a - 1 - S.falseStack).toNat : CInt) = a - 1 - S.falseStack := by omega
  have hposl : (a - 1 - S.falseStack).toNat < trailLen S := by simp only [trailLen]; omega
  have hlv := inRange_iff.mp (ht.lit _ hposl)
  have hlit : ({ S with DB := DB, assigned := a } : solver).ld (a - 1) =
      trailAt S (a - 1 - S.falseStack).toNat := by
    simp only [trailAt]
    rw [hpos, show S.falseStack + (a - 1 - S.falseStack) = a - 1 by omega]
    apply hsame _ (by omega)
    intro i _ h2' he
    have := inRange_iff.mp (ht.lit i h2')
    omega
  rw [hlit, unassign_eq]
  generalize hY : ({ ({ S with DB := DB, assigned := a } : solver) with assigned := a - 1 } : solver) = Y
  have hYa : Y.assigned = a - 1 := by rw [← hY]
  have hYf : Y.false = S.false := by rw [← hY]
  have hYld : ∀ q, Y.ld q = ({ S with DB := DB, assigned := a } : solver).ld q := by intro q; rw [← hY]; rfl
  rw [hYf]
  have hp0 : 0 ≤ S.false + trailAt S (a - 1 - S.falseStack).toNat := by omega
  refine ⟨?_, by simp only [st_assigned, hYa]; omega, by simp only [st_assigned, hYa]; omega, ?_, ?_⟩
  · obtain ⟨DB', hD⟩ := st_eq Y (S.false + trailAt S (a - 1 - S.falseStack).toNat) 0
    refine ⟨DB', ?_⟩
    rw [hD, ← hY]
  · intro q hq hne
    simp only [st_assigned, hYa] at hne
    rw [ld_st _ _ hp0 hq]
    split
    · rename_i he
      exact absurd he (hne _ (by omega) hposl)
    · rw [hYld]; exact hsame q hq fun i h1' h2' => hne i (by omega) h2'
  · intro i h1' h2'
    simp only [st_assigned, hYa] at h1'
    have hl' := inRange_iff.mp (ht.lit i h2')
    rw [ld_st _ _ hp0 (by omega)]
    split
    · rfl
    · rename_i hne
      rcases Nat.lt_or_ge i ((a - S.falseStack).toNat) with hi | hi
      · exfalso
        have : i = (a - 1 - S.falseStack).toNat := by omega
        subst this; exact hne rfl
      · rw [hYld]; exact hzero i hi h2'

/-- `restart`'s result: the trail cut at `forced`, with the flags above it cleared. -/
theorem restart_cells {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Settled input S db vs) :
    (∃ DB, restart S = { S with DB := DB, assigned := S.forced, processed := S.forced }) ∧
    (∀ q, 0 ≤ q → (∀ i, forcedPos S ≤ i → i < trailLen S → q ≠ S.false + trailAt S i) →
      (restart S).ld q = S.ld q) ∧
    (∀ i, forcedPos S ≤ i → i < trailLen S → (restart S).ld (S.false + trailAt S i) = 0) := by
  have ht := h.core.trail
  have hn := h.core.layout.num
  have hF := ht.forced_le; have hP := ht.processed_le; have hA := ht.assigned_le
  have hlen := ht.len_le
  generalize hR : restart S = R
  apply Id.of_wp_run_eq hR
  mvcgen [restart] invariants
  · fun S' => ULift.up (S'.assigned - S.forced).toNat
  · ⇓ c => match c with
      | .inl S' => ⌜Popped S S'⌝
      | .inr S' => ⌜Popped S S' ∧ S'.assigned ≤ S.forced⌝
  case vc1.step.isTrue =>
    rename_i S' m hc S1 S2 hinv
    obtain ⟨hvar, hpop⟩ := hinv
    have hc' : S.forced < S'.assigned := by
      obtain ⟨⟨DB, hS'⟩, -⟩ := hpop; rw [hS'] at hc; exact hc
    have hfin := popped_step ht h.core.layout hpop hc'
    simp [WhileVariant.eval, SVal.evalsTo] at hvar ⊢
    refine ⟨?_, hfin⟩
    simp only [S2, S1, unassign_eq, st_assigned]
    omega
  case vc2.step.isFalse =>
    rename_i S' m hc hinv
    obtain ⟨hvar, hpop⟩ := hinv
    refine ⟨hpop, ?_⟩
    obtain ⟨⟨DB, hS'⟩, -⟩ := hpop
    rw [hS'] at hc; simpa using hc
  case vc3 =>
    have hlen' := hlen
    simp only [trailLen] at hlen'
    refine ⟨⟨S.DB, by simp⟩, by omega, Int.le_refl _, fun q _ _ => rfl, fun i h1 h2 => ?_⟩
    simp only [trailLen] at h2; omega
  case vc4 =>
    rename_i r S' hinv
    obtain ⟨⟨⟨DB, hS'⟩, h1, h2, hsame, hzero⟩, h3⟩ := hinv
    have ha : r.assigned = S.forced := by omega
    have hrf : r.forced = S.forced := by rw [hS']
    refine ⟨⟨DB, ?_⟩, fun q hq hne => ?_, fun i h1' h2' => ?_⟩
    · show ({ r with processed := r.forced } : solver) = _
      rw [hrf]
      generalize hra : r.assigned = a at hS' ha
      rw [hS', ha]
    · show r.ld q = S.ld q
      exact hsame q hq fun i h1' h2' => hne i (by simp only [forcedPos]; omega) h2'
    · show r.ld _ = 0
      exact hzero i (by simp only [forcedPos] at h1'; omega) h2'

/-- After `propagate`, the position `forced` (if on the trail) is a decision: the root is
exactly the part below it. -/
theorem Settled.decision_at_forced {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Settled input S db vs) (hlt : forcedPos S < trailLen S) : IsDecision S (forcedPos S) := by
  have hnr : ¬ RootLevel S (forcedPos S) := fun hr => by
    have := h.root_below _ hlt hr; omega
  refine Classical.byContradiction fun hnd => hnr fun k hk hd => ?_
  rcases Nat.lt_or_ge k (forcedPos S) with hk' | hk'
  · exact h.core.trail.forced_root k hk' k (Nat.le_refl _) hd
  · have : k = forcedPos S := by omega
    subst this; exact hnd hd

/-- `restart` keeps `Settled` and leaves only the root on the trail. Only `DB` (the
`false` flags), `assigned` and `processed` change. Used by `afterConflict_spec`. -/
theorem restart_spec {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Settled input S db vs) :
    Settled input (restart S) db vs ∧ trailLen (restart S) = forcedPos (restart S) ∧
      ∃ DB, restart S = { S with DB := DB, assigned := S.forced, processed := S.forced } := by
  obtain ⟨⟨DB, hR⟩, hsame, hzero⟩ := restart_cells h
  have core := h.core; have hl := core.layout; have hn := hl.num; have ht := core.trail
  have hn1 := hl.nVars_pos
  have hF := ht.forced_le; have hP := ht.processed_le; have hA := ht.assigned_le
  have hlen := ht.len_le
  refine ⟨?_, ?_, DB, hR⟩
  rotate_left
  · rw [hR]; rfl
  generalize hRdef : restart S = R at hR hsame hzero
  have hfl : forcedPos S ≤ trailLen S := by simp only [forcedPos, trailLen]; omega
  have hshape : SameShape S R := by rw [hR]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hfp : forcedPos R = forcedPos S := by rw [hR]; rfl
  have hpp : processedPos R = forcedPos S := by rw [hR]; simp [processedPos, forcedPos]
  have htl : trailLen R = forcedPos S := by rw [hR]; simp [trailLen, forcedPos]
  have hlen' := hlen; simp only [trailLen] at hlen'
  -- cells outside `false` are unchanged
  have low : ∀ q, 0 ≤ q → q < 6 * S.nVars + 5 → R.ld q = S.ld q := fun q h0 h1 =>
    hsame q h0 fun i _ hi => by have := inRange_iff.mp (ht.lit i hi); omega
  have high : ∀ q, 8 * S.nVars + 6 ≤ q → R.ld q = S.ld q := fun q h1 =>
    hsame q (by omega) fun i _ hi => by have := inRange_iff.mp (ht.lit i hi); omega
  have htr : ∀ i < forcedPos S, trailAt R i = trailAt S i := fun i hi => by
    simp only [trailAt, hshape.falseStack]; simp only [forcedPos] at hi
    exact low _ (by omega) (by omega)
  have hlitS : ∀ i < trailLen S, InRange S.nVars (trailAt S i) := ht.lit
  have hrs : ∀ i < forcedPos S, reasonOf R (trailAt R i) = reasonOf S (trailAt S i) := fun i hi => by
    have := inRange_iff.mp (hlitS i (by omega))
    rw [htr i hi]; simp only [reasonOf, hshape.reason]
    exact low _ (by rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
      (by rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
  have hdec : ∀ i < forcedPos S, (IsDecision R i ↔ IsDecision S i) := fun i hi => by
    simp only [IsDecision, hrs i hi]
  have hroot : ∀ i < forcedPos S, (RootLevel R i ↔ RootLevel S i) := fun i hi =>
    ⟨fun h' k hk => (not_congr (hdec k (by omega))).mp (h' k hk),
     fun h' k hk => (not_congr (hdec k (by omega))).mpr (h' k hk)⟩
  -- flags: the popped literals are cleared, the others kept
  have hflag : ∀ lit, InRange S.nVars lit → (∀ i, forcedPos S ≤ i → i < trailLen S → trailAt S i ≠ lit) →
      flag R lit = flag S lit := fun lit hl' hne => by
    have := inRange_iff.mp hl'
    simp only [flag, hshape.false]
    exact hsame _ (by omega) fun i h1 h2 he => hne i h1 h2 (by omega)
  have hflag0 : ∀ i, forcedPos S ≤ i → i < trailLen S → flag R (trailAt S i) = 0 := fun i h1 h2 => by
    simp only [flag, hshape.false]; exact hzero i h1 h2
  have hfalse : ∀ {lit : CInt} {j : Nat}, FalseAt R lit j → FalseAt S lit j ∧ j < forcedPos S := by
    intro lit j ⟨hj, he⟩
    rw [htl] at hj; exact ⟨⟨by omega, by rw [← htr j hj]; exact he⟩, hj⟩
  have hfalse' : ∀ {lit : CInt} {j : Nat}, FalseAt S lit j → j < forcedPos S → FalseAt R lit j := by
    intro lit j ⟨_, he⟩ hj
    exact ⟨by rw [htl]; exact hj, by rw [htr j hj]; exact he⟩
  have htrail : Trail R := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hR]; exact hF
    · rw [hR]; exact Int.le_refl _
    · rw [hR]; exact Int.le_refl _
    · rw [htl, hshape.nVars]; omega
    · intro i hi; rw [htl] at hi; rw [htr i hi, hshape.nVars]; exact hlitS i (by omega)
    · intro i hi j hj he; rw [htl] at hi hj; rw [htr i hi, htr j hj] at he
      exact ht.distinct i (by omega) j (by omega) he
    · intro i hi hr; rw [htl] at hi
      rw [htr i hi, hflag _ (hlitS i (by omega)) fun j h1 h2 he =>
        absurd (ht.distinct j h2 i (by omega) (by rw [he])) (by omega)]
      exact ht.flag_root i (by omega) ((hroot i hi).mp hr)
    · intro i hi hr; rw [htl] at hi
      exact absurd ((hroot i hi).mpr (ht.forced_root i hi)) hr
    · intro lit hl' hoff
      rw [hshape.nVars] at hl'
      by_cases hp : ∃ i, forcedPos S ≤ i ∧ i < trailLen S ∧ trailAt S i = lit
      · obtain ⟨i, h1, h2, he⟩ := hp; rw [← he]; exact hflag0 i h1 h2
      · have hp' : ∀ i, forcedPos S ≤ i → i < trailLen S → trailAt S i ≠ lit :=
          fun i h1 h2 he => hp ⟨i, h1, h2, he⟩
        rw [hflag lit hl' hp']
        refine ht.flag_off lit hl' fun i hi he => ?_
        rcases Nat.lt_or_ge i (forcedPos S) with hi' | hi'
        · exact hoff i (by rw [htl]; exact hi') (by rw [htr i hi']; exact he)
        · exact hp' i hi' hi he
    · intro i hi; rw [htl] at hi
      have := inRange_iff.mp (hlitS i (by omega))
      rw [htr i hi, hshape.model, low _ (by rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
        (by rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)]
      exact ht.model i (by omega)
    · simp only [flag, hshape.false]
      rw [hsame _ (by omega) fun i _ hi he => (inRange_iff.mp (hlitS i hi)).1 (by omega)]
      exact ht.flag_zero
    · intro i hi; rw [hfp] at hi; exact (hroot i hi).mpr (ht.forced_root i hi)
  have hdb := core.database.frame hshape (by rw [hR]) (by rw [hR]) (by rw [hR])
    fun q hq => high q (by simp only [clausesAt] at hq; omega)
  refine ⟨⟨core.valid, by rw [hshape.nVars]; exact core.nVars, by rw [hR]; exact core.memory,
    by rw [hR]; exact core.maxLemmas, hl.frame hshape (high _ (by simp only [clausesAt]; omega)), htrail,
    ?_, hdb, core.watches.frame hl core.database hshape high, ?_, ?_,
    core.order.frame hl hshape (by rw [hR]) fun q h1 h2 => low q (by omega) (by omega)⟩, ?_,
    by rw [hR], ?_⟩
  · intro i hi hr; rw [htl] at hi
    rw [htr i hi]; exact core.root i (by omega) ((hroot i hi).mp hr)
  · intro i hi hfi; rw [htl] at hi; rw [hfp] at hfi; omega
  · intro r hr h1
    obtain ⟨i, hi, hrt, he⟩ := core.units r hr h1
    have := h.root_below i hi hrt
    exact ⟨i, by rw [htl]; exact this, (hroot i this).mpr hrt, by rw [htr i this]; exact he⟩
  · -- a watched literal's true partner is below `forced`: the position `forced` is a decision
    intro r hr h2 w o hwo p hp hfa
    rw [hpp] at hp
    obtain ⟨hfaS, -⟩ := hfalse hfa
    have hpS : p < processedPos S := by simp only [processedPos, forcedPos] at hp ⊢; omega
    obtain ⟨q, hq, hsl⟩ := h.watched r hr h2 w o hwo p hpS hfaS
    have hqf : q < forcedPos S := by
      refine Classical.byContradiction fun hge => ?_
      have hd := h.decision_at_forced (by have := hq.1; omega)
      exact hsl (forcedPos S) (by omega) (by omega) hd
    exact ⟨q, hfalse' hq hqf, fun k h1 h2 => (not_congr (hdec k (by omega))).mpr (hsl k h1 h2)⟩
  · intro i hi hr; rw [htl] at hi; rw [hfp]; exact hi

end MicrosatLean.Faithful.Verification
