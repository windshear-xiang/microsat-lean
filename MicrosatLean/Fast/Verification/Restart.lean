import MicrosatLean.Fast.Verification.Sim
import MicrosatLean.Faithful.Verification.Restart

/-!
# `restart` of the fast port (C:38–40)

The faithful `restart_spec` derives `Settled` from three facts about `restart S`
(`restart_cells`): the fields, the unchanged cells, and the cleared flags.
`restart_settled` is that derivation for any state with these facts. `restartLoop_cells`
proves them for the fast loop.
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- `restart_spec` for any state `R` with `restart_cells`' facts: same fields as `S` but
`assigned = processed = forced`, the flags of the popped literals 0, every other cell
unchanged. -/
theorem restart_settled {input : Input} {S : solver} {db : Records} {vs : List Int}
    (h : Settled input S db vs) {R : solver} {DB : Array Int}
    (hR : R = { S with DB := DB, assigned := S.forced, processed := S.forced })
    (hsame : ∀ q, 0 ≤ q → (∀ i, forcedPos S ≤ i → i < trailLen S → q ≠ S.false + trailAt S i) → R.ld q = S.ld q)
    (hzero : ∀ i, forcedPos S ≤ i → i < trailLen S → R.ld (S.false + trailAt S i) = 0) :
    Settled input R db vs ∧ trailLen R = forcedPos R := by
  have core := h.core; have hl := core.layout; have hn := hl.num; have ht := core.trail
  have hn1 := hl.nVars_pos
  have hF := ht.forced_le; have hP := ht.processed_le; have hA := ht.assigned_le
  have hlen := ht.len_le
  refine ⟨?_, ?_⟩
  rotate_left
  · rw [hR]; rfl
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

/-- `restartLoop` (C:39) from `a` down to `forced` clears the flags of the trail literals at
the positions in between and changes no other cell. `S` is the faithful state before the
loop, related to `db` and `L`; the invariant at `a`: the flags of the positions from `a` on
(up to `trailLen S`) are 0, every other cell is `S`'s. -/
theorem restartLoop_cells {S : solver} {L : Lay} (ht : Trail S) (hl : Layout S)
    (hfls : S.false = L.fls.toInt) (hn : 10 * S.nVars + 7 ≤ 2 ^ 30)
    {forced : Cell} (hforced : forced.toInt = S.forced) (hfs : 0 ≤ S.falseStack) :
    ∀ (k : Nat) (db : Array Cell) (a : Cell), (a.toInt - forced.toInt).toNat = k →
      db.size ≤ 2 ^ 31 → S.forced ≤ a.toInt → a.toInt ≤ S.assigned →
      (∀ q, 0 ≤ q → (∀ i, (a.toInt - S.falseStack).toNat ≤ i → i < trailLen S → q ≠ S.false + trailAt S i) →
        ldA (toDB db) q = S.ld q) →
      (∀ i, (a.toInt - S.falseStack).toNat ≤ i → i < trailLen S → ldA (toDB db) (S.false + trailAt S i) = 0) →
      (restartLoop L db a forced).2.toInt = S.forced ∧ (restartLoop L db a forced).1.size ≤ 2 ^ 31 ∧
      (∀ q, 0 ≤ q → (∀ i, forcedPos S ≤ i → i < trailLen S → q ≠ S.false + trailAt S i) →
        ldA (toDB (restartLoop L db a forced).1) q = S.ld q) ∧
      (∀ i, forcedPos S ≤ i → i < trailLen S → ldA (toDB (restartLoop L db a forced).1) (S.false + trailAt S i) = 0) := by
  have hnum := hl.num
  have hn1 := hl.nVars_pos
  have hF := ht.forced_le; have hP := ht.processed_le; have hA := ht.assigned_le; have hlen := ht.len_le
  have htl : (trailLen S : Int) = S.assigned - S.falseStack := by simp only [trailLen]; omega
  have hfp : (forcedPos S : Int) = S.forced - S.falseStack := by simp only [forcedPos]; omega
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro db a hk hsz ha1 ha2 h1 h2
  rw [restartLoop.eq_1]
  by_cases hgt : a > forced
  · rw [if_pos hgt]
    have hgt' : forced.toInt < a.toInt := Int32.lt_iff_toInt_lt.mp hgt
    have hone : ((1 : Cell)).toInt = 1 := rfl
    have ha1' : (a - 1).toInt = a.toInt - 1 := by rw [toInt_sub (by rw [hone]; omega) (by rw [hone]; omega), hone]
    -- the position `i0` popped now and its literal
    have hi0 : (a.toInt - 1 - S.falseStack).toNat < trailLen S := by omega
    generalize hi0d : (a.toInt - 1 - S.falseStack).toNat = i0 at hi0
    have hlit := inRange_iff.mp (ht.lit i0 hi0)
    have hstack : ldA (toDB db) (a.toInt - 1) = trailAt S i0 := by
      rw [h1 _ (by omega) (fun i hi1 hi2 => by have := inRange_iff.mp (ht.lit i hi2); omega)]
      simp only [trailAt]; congr 1; omega
    have hx : (ld db (a - 1)).toInt = trailAt S i0 := by
      rw [ld_sim ({ (default : solver) with DB := toDB db } : solver) rfl hsz, ha1']; exact hstack
    have hfx : (L.fls + ld db (a - 1)).toInt = S.false + trailAt S i0 := by
      rw [toInt_add (by rw [hx]; omega) (by rw [hx]; omega), hx, hfls]
    obtain ⟨e, hsz'⟩ := st_sim ({ (default : solver) with DB := toDB db } : solver) rfl hsz (L.fls + ld db (a - 1)) 0
    rw [hfx] at e
    have hw : ∀ q, 0 ≤ q → ldA (toDB (st db (L.fls + ld db (a - 1)) 0)) q =
        if q = S.false + trailAt S i0 then 0 else ldA (toDB db) q := fun q hq => by
      rw [← e]; exact ld_st _ _ (by omega) hq
    have hd : ∀ i < trailLen S, i ≠ i0 → trailAt S i ≠ trailAt S i0 := fun i hi hne he =>
      hne (ht.distinct i hi i0 hi0 (by rw [he]))
    have hk' : ((a - 1).toInt - forced.toInt).toNat < k := by rw [ha1']; omega
    obtain ⟨r1, r2, r3, r4⟩ := ih _ hk' _ (a - 1) rfl hsz' (by rw [ha1']; omega) (by rw [ha1']; omega)
      (fun q hq hne => by
        rw [hw q hq, if_neg (hne i0 (by rw [ha1']; omega) hi0)]
        exact h1 q hq fun i hi1 hi2 => hne i (by rw [ha1']; omega) hi2)
      (fun i hi1 hi2 => by
        have hlit' := inRange_iff.mp (ht.lit i hi2)
        rw [hw _ (by omega)]
        by_cases hii : i = i0
        · subst hii; rw [if_pos rfl]
        · rw [if_neg (fun he => hd i hi2 hii (by omega))]
          exact h2 i (by rw [ha1'] at hi1; omega) hi2)
    exact ⟨r1, r2, r3, r4⟩
  · rw [if_neg hgt]
    have hle : a.toInt ≤ forced.toInt := Int.not_lt.mp (fun h => hgt (Int32.lt_iff_toInt_lt.mpr h))
    have haf : a.toInt = S.forced := by omega
    refine ⟨haf, hsz, fun q hq hne => h1 q hq fun i hi1 hi2 => hne i (by omega) hi2,
      fun i hi1 hi2 => h2 i (by omega) hi2⟩

/-- The fast `restart` (C:38–40) keeps `Settled`, for the abstracted states: the faithful
`restart_spec`, for the fast port. Only `db`, `assigned` and `processed` change. -/
theorem restart_fast {input : Input} {L : Lay} {s : St} {M fa sl : Int} {db : Records} {vs : List Int}
    (h : Settled input (abs L s M fa sl) db vs) (hn : 10 * L.nVars.toInt + 7 ≤ 2 ^ 30)
    (hsz : s.db.size ≤ 2 ^ 31) :
    Settled input (abs L (restart L s) M fa sl) db vs ∧
      trailLen (abs L (restart L s) M fa sl) = forcedPos (abs L (restart L s) M fa sl) ∧
      (restart L s).db.size ≤ 2 ^ 31 ∧
      ∃ d, restart L s = { s with db := d, assigned := s.forced, processed := s.forced } := by
  have ht := h.core.trail
  have hl := h.core.layout
  have hfs : 0 ≤ (abs L s M fa sl).falseStack := by have := hl.num; have := hl.nVars_pos; omega
  have hA : (abs L s M fa sl).assigned = s.assigned.toInt := rfl
  have hFA : (abs L s M fa sl).forced ≤ (abs L s M fa sl).assigned :=
    Int.le_trans ht.processed_le ht.assigned_le
  have htl : trailLen (abs L s M fa sl) = (s.assigned.toInt - (abs L s M fa sl).falseStack).toNat := rfl
  obtain ⟨r1, r2, r3, r4⟩ := restartLoop_cells ht hl (L := L) rfl hn (forced := s.forced) rfl hfs _ s.db s.assigned
    rfl hsz hFA (Int.le_refl _) (fun q _ _ => rfl) (fun i hi1 hi2 => by rw [htl] at hi2; omega)
  generalize hres : restartLoop L s.db s.assigned s.forced = res at r1 r2 r3 r4
  obtain ⟨d, a⟩ := res
  have hrst : restart L s = { s with db := d, assigned := a, processed := s.forced } := by
    simp only [restart, St.take, hres]
  have ha : a = s.forced := Int32.toInt_inj.mp r1
  subst ha
  have hR : abs L (restart L s) M fa sl = { abs L s M fa sl with
      DB := toDB d, assigned := (abs L s M fa sl).forced, processed := (abs L s M fa sl).forced } := by
    rw [hrst]; rfl
  obtain ⟨st1, st2⟩ := restart_settled h hR (fun q hq hne => by rw [hR]; exact r3 q hq hne)
    (fun i hi1 hi2 => by rw [hR]; exact r4 i hi1 hi2)
  exact ⟨st1, st2, by rw [hrst]; exact r2, d, hrst⟩

end MicrosatLean.Fast.Verification
