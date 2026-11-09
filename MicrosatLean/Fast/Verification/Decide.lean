import MicrosatLean.Fast.Verification.Restart
import MicrosatLean.Faithful.Verification.Decide

/-!
# The decision of the fast port (C:173–179)

`decideLoop_spec` is the faithful `scan_spec` for the fast scan along `prev`, proved by
induction on the position of the cursor in the decision order `vs`.
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- The fast decision scan (C:173–174) meets the faithful `scan_spec`: it returns 0 when every
variable is assigned, and otherwise the first unassigned variable of the order list from the
cursor on. -/
theorem decideLoop_spec {input : Input} {L : Lay} {s : St} {M fa sl : Int} {db : Records} {vs : List Int}
    (h : Settled input (abs L s M fa sl) db vs) (hn : 10 * L.nVars.toInt + 7 ≤ 2 ^ 30)
    (hsz : s.db.size ≤ 2 ^ 31) :
    ∀ (m : Nat) (d : Cell), vs.length - vs.idxOf d.toInt = m → Cursor (abs L s M fa sl) vs d.toInt →
      ((decideLoop L s.db d).toInt = 0 ∧ ∀ v, 1 ≤ v → v ≤ (abs L s M fa sl).nVars → Assigned (abs L s M fa sl) v) ∨
      (∃ k, ∃ hk : k < vs.length, vs[k] = (decideLoop L s.db d).toInt ∧
        (∀ j (h : j < vs.length), j < k → Assigned (abs L s M fa sl) vs[j]) ∧
        ¬ Assigned (abs L s M fa sl) (decideLoop L s.db d).toInt) := by
  generalize hS : abs L s M fa sl = S at h ⊢
  have ht := h.core.trail
  have ho := h.core.order
  have hl := h.core.layout
  have hnum := hl.num
  have hn1 := hl.nVars_pos
  have hnd := ho.nodup
  have h0 : (0 : Int) ∉ vs := fun h0 => by have := ho.mem_iff.mp h0; omega
  have hz : flag S 0 = 0 := ht.flag_zero
  have hNV : S.nVars = L.nVars.toInt := by rw [← hS]; rfl
  have hDB : S.DB = toDB s.db := by rw [← hS]; rfl
  have hfl : S.false = L.fls.toInt := by rw [← hS]; rfl
  have hpv : S.prev = L.prev.toInt := by rw [← hS]; rfl
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro d hm c
  obtain ⟨k, hk, hd, before⟩ := c
  -- the cursor is a variable of the order or 0
  have hdr : 0 ≤ d.toInt ∧ d.toInt ≤ S.nVars := by
    rcases Nat.lt_or_ge k vs.length with h' | h'
    · rw [List.getElem?_eq_getElem h', Option.getD_some] at hd
      have := ho.mem_iff.mp (List.getElem_mem h'); rw [hd] at this; omega
    · rw [List.getElem?_eq_none h', Option.getD_none] at hd; omega
  have hfd : (L.fls + d).toInt = S.false + d.toInt := by rw [toInt_add (by omega) (by omega), hfl]
  have hnegd : (-d).toInt = -d.toInt := toInt_neg (by omega)
  have hfnd : (L.fls - d).toInt = S.false + -d.toInt := by rw [toInt_sub (by omega) (by omega), hfl]; omega
  have hpd : (L.prev + d).toInt = S.prev + d.toInt := by rw [toInt_add (by omega) (by omega), hpv]
  have e1 := ld_sim S hDB hsz (L.fls + d)
  have e2 := ld_sim S hDB hsz (L.fls - d)
  have e3 := ld_sim S hDB hsz (L.prev + d)
  rw [hfd] at e1; rw [hfnd] at e2; rw [hpd] at e3
  rw [decideLoop.eq_1]
  by_cases hc : (ld s.db (L.fls + d) != 0 || ld s.db (L.fls - d) != 0) = true
  · rw [if_pos hc]
    have hflag : flag S d.toInt ≠ 0 ∨ flag S (-d.toInt) ≠ 0 := by
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at hc
      rcases hc with hc | hc
      · left; intro h'; apply hc; apply Int32.toInt_inj.mp; rw [e1]; exact h'
      · right; intro h'; apply hc; apply Int32.toInt_inj.mp; rw [e2]; exact h'
    have hk' : k < vs.length := by
      rcases Nat.lt_or_ge k vs.length with h' | h'
      · exact h'
      · exfalso
        rw [List.getElem?_eq_none h'] at hd; simp at hd
        rw [← hd] at hflag; simp [hz] at hflag
    rw [List.getElem?_eq_getElem hk'] at hd; simp only [Option.getD_some] at hd
    have hmem : vs[k] ∈ vs := List.getElem_mem hk'
    have hasg := (ht.assigned_iff (ho.mem_iff.mp hmem)).mp (by rw [hd]; exact hflag)
    have hnext := ho.chain.prev_getElem k hk'
    have hnx : (ld s.db (L.prev + d)).toInt = vs[k + 1]?.getD 0 := by rw [e3, ← hd, hnext]
    refine ih _ ?_ _ rfl ⟨k + 1, by omega, by rw [hnx], ?_⟩
    · rw [← hm, hnx, ← hd, hnd.idxOf_getElem k hk']
      rcases Nat.lt_or_ge (k + 1) vs.length with h' | h'
      · rw [List.getElem?_eq_getElem h', Option.getD_some, hnd.idxOf_getElem (k + 1) h']; omega
      · rw [List.getElem?_eq_none h', Option.getD_none, List.idxOf_eq_length h0]; omega
    · intro j hj hjk
      rcases Nat.lt_or_ge j k with h' | h'
      · exact before j hj h'
      · have : j = k := by omega
        subst this; exact hasg
  · rw [if_neg hc]
    have hflag : ¬ (flag S d.toInt ≠ 0 ∨ flag S (-d.toInt) ≠ 0) := by
      intro h'; apply hc
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq]
      rcases h' with h' | h'
      · left; intro he; apply h'; show S.ld (S.false + d.toInt) = 0; rw [← e1, he]; rfl
      · right; intro he; apply h'; show S.ld (S.false + -d.toInt) = 0; rw [← e2, he]; rfl
    rcases Nat.lt_or_ge k vs.length with hk' | hk'
    · rw [List.getElem?_eq_getElem hk'] at hd; simp only [Option.getD_some] at hd
      have hmem : vs[k] ∈ vs := List.getElem_mem hk'
      refine Or.inr ⟨k, hk', hd, before, fun ha => hflag ?_⟩
      rw [← hd] at ha ⊢; exact (ht.assigned_iff (ho.mem_iff.mp hmem)).mpr ha
    · rw [List.getElem?_eq_none hk'] at hd; simp at hd
      refine Or.inl ⟨hd.symm, fun v h1 h2 => ?_⟩
      obtain ⟨j, hj, he⟩ := List.getElem_of_mem (ho.mem_iff.mpr ⟨h1, h2⟩)
      rw [← he]; exact before j hj (by omega)

/-- The fast decision (C:176–179, inside `run`) is the faithful `assignDecision` for a variable
`d ≠ 0`: the same three writes, and `assigned` one higher. -/
theorem assignDecision_sim {L : Lay} {s : St} {M fa sl : Int} (hsz : s.db.size ≤ 2 ^ 31)
    (hn : 10 * L.nVars.toInt + 7 ≤ 2 ^ 30) (hlay : L.fls.toInt = 7 * L.nVars.toInt + 5 ∧
      L.reason.toInt = 4 * L.nVars.toInt + 3 ∧ 1 ≤ L.nVars.toInt)
    {d : Cell} (hdr : 1 ≤ d.toInt ∧ d.toInt ≤ L.nVars.toInt)
    (hA : 0 ≤ s.assigned.toInt ∧ s.assigned.toInt < 2 ^ 30) :
    assignDecision (abs L s M fa sl) d.toInt =
      .running (abs L { s with
          db := st (st (st s.db (L.fls - (if ld s.db d != 0 then d else -d)) 1) s.assigned
            (-(if ld s.db d != 0 then d else -d))) (L.reason + absC (if ld s.db d != 0 then d else -d)) 0,
          assigned := s.assigned + 1 } M fa sl)
        (absC (if ld s.db d != 0 then d else -d)).toInt := by
  have hd0 : d.toInt ≠ 0 := by omega
  have hl := ld_sim (abs L s M fa sl) rfl hsz d
  have hmodel : (abs L s M fa sl).ld ((abs L s M fa sl).model + d.toInt) = (ld s.db d).toInt := by
    rw [hl]; show (abs L s M fa sl).ld (0 + d.toInt) = _; rw [Int.zero_add]
  generalize hd' : (if ld s.db d != 0 then d else -d) = d'
  have hd'i : d'.toInt = if (abs L s M fa sl).ld ((abs L s M fa sl).model + d.toInt) != 0 then d.toInt else -d.toInt := by
    rw [hmodel, ← hd']
    by_cases h : ld s.db d = 0
    · have h' : (ld s.db d).toInt = 0 := by rw [h]; rfl
      rw [if_neg (by simp [h]), if_neg (by simp [h']), toInt_neg (by omega)]
    · have h' : (ld s.db d).toInt ≠ 0 := fun e => h (Int32.toInt_inj.mp (by rw [e]; rfl))
      rw [if_pos (by simp [h]), if_pos (by simp [h'])]
  have hd'r : -L.nVars.toInt ≤ d'.toInt ∧ d'.toInt ≤ L.nVars.toInt ∧ d'.toInt ≠ 0 := by
    rw [hd'i]; split <;> omega
  unfold assignDecision
  rw [if_neg (by simp [hd0]), ← hd'i]
  have hone : ((1 : Cell)).toInt = 1 := rfl
  have hzero : ((0 : Cell)).toInt = 0 := rfl
  have p1 : (L.fls - d').toInt = (abs L s M fa sl).false + -d'.toInt := by
    rw [toInt_sub (by omega) (by omega)]; show _ = L.fls.toInt + _; omega
  have p3 : (L.reason + absC d').toInt = (abs L s M fa sl).reason + MicrosatLean.Faithful.abs d'.toInt := by
    have ha := toInt_absC (a := d') (by omega)
    have : 0 ≤ MicrosatLean.Faithful.abs d'.toInt ∧ MicrosatLean.Faithful.abs d'.toInt ≤ L.nVars.toInt := by
      rw [← ha]; unfold absC; split
      · rw [toInt_neg (by omega)]; have := Int32.lt_iff_toInt_lt.mp (by assumption : d' < 0); omega
      · have := Int.not_lt.mp (fun h => (by assumption : ¬ d' < 0) (Int32.lt_iff_toInt_lt.mpr h)); omega
    rw [toInt_add (by rw [ha]; omega) (by rw [ha]; omega), ha]; rfl
  obtain ⟨e1, s1⟩ := st_sim (abs L s M fa sl) rfl hsz (L.fls - d') 1
  rw [p1, hone] at e1
  dsimp only
  generalize hS1 : (abs L s M fa sl).st ((abs L s M fa sl).false + -d'.toInt) 1 = S1 at e1
  have hS1f : ∃ DB, S1 = { abs L s M fa sl with DB := DB } := by rw [← hS1]; exact st_eq _ _ _
  obtain ⟨D1, hD1⟩ := hS1f
  have hA1 : S1.assigned = s.assigned.toInt := by rw [hD1]; rfl
  rw [hA1]
  obtain ⟨e2, s2⟩ := st_sim S1 e1 s1 s.assigned (-d')
  rw [toInt_neg (by omega)] at e2
  generalize hS2 : S1.st s.assigned.toInt (-d'.toInt) = S2 at e2
  have hS2f : ∃ DB, S2 = { abs L s M fa sl with DB := DB } := by
    rw [← hS2, hD1]; obtain ⟨D, h⟩ := st_eq ({ abs L s M fa sl with DB := D1 } : solver) s.assigned.toInt (-d'.toInt)
    exact ⟨D, by rw [h]⟩
  obtain ⟨D2, hD2⟩ := hS2f
  have hR2 : ({ S2 with assigned := S2.assigned + 1 } : solver) =
      { abs L s M fa sl with DB := D2, assigned := s.assigned.toInt + 1 } := by rw [hD2]; rfl
  have hS2r : S2.reason = (abs L s M fa sl).reason := by rw [hD2]
  rw [hR2, hS2r]
  have e2' : ({ abs L s M fa sl with DB := D2, assigned := s.assigned.toInt + 1 } : solver).DB =
      toDB (st (st s.db (L.fls - d') 1) s.assigned (-d')) := by rw [← e2, hD2]
  obtain ⟨e3, s3⟩ := st_sim _ e2' s2 (L.reason + absC d') 0
  rw [p3, hzero] at e3
  congr 1
  · apply MicrosatLean.Faithful.solver.ext
    case DB => exact e3
    case assigned =>
      simp only [st_assigned]
      show _ = (s.assigned + 1).toInt
      rw [toInt_add (by rw [hone]; omega) (by rw [hone]; omega), hone]
    all_goals simp [abs]
  · exact (toInt_absC (by omega)).symm

end MicrosatLean.Fast.Verification
