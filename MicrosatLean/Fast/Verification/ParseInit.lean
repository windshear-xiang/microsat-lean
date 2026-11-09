import MicrosatLean.Fast.Verification.Inv
import MicrosatLean.Faithful.Verification.Init

/-!
# `initCDCL` of the fast port (C:181–210)

The fast `initCDCL` starts from `10 n + 8` zero cells and runs `initLoop`; the faithful one
grows its array to the same cells. The abstraction of the fast result, with `nClauses` set
as the faithful `initCDCL` sets it, satisfies the faithful `InitState` (proved from the
cells, by induction on `initLoop`).
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- A fast write, read through `ldA`. -/
theorem ldA_st {db : Array Cell} (hsz : db.size ≤ 2 ^ 31) {p : Cell} (hp : 0 ≤ p.toInt) (v : Cell)
    {q : Int} (hq : 0 ≤ q) :
    ldA (toDB (st db p v)) q = if q = p.toInt then v.toInt else ldA (toDB db) q := by
  obtain ⟨e, -⟩ := st_sim ({ (default : solver) with DB := toDB db } : solver) rfl hsz p v
  rw [← e, ← ld_eq_ldA, ld_st _ _ hp hq]
  rfl

/-- A fast write keeps the arena at most `2^31` cells. -/
theorem st_size {db : Array Cell} (hsz : db.size ≤ 2 ^ 31) (p v : Cell) : (st db p v).size ≤ 2 ^ 31 :=
  (st_sim ({ (default : solver) with DB := toDB db } : solver) rfl hsz p v).2

/-- One iteration of `initLoop` on the cells (C:207–209), with plain numbers: the seven
writes give `initCell` for one more variable. -/
theorem initLoop_cell {N i p : Int} (hi : 1 ≤ i ∧ i ≤ N) (hp : 0 ≤ p) :
    (if p = 9 * N + 6 + i then MicrosatLean.Faithful.END else
      if p = 9 * N + 6 - i then MicrosatLean.Faithful.END else
      if p = i then 0 else if p = 7 * N + 5 - i then 0 else if p = 7 * N + 5 + i then 0 else
      if p = N + i then i else if p = 2 * N + 2 + i then i - 1 else initCell N (vars (i - 1)) p) =
    initCell N (vars (i + 1 - 1)) p := by
  have hpre : ∀ v ∈ vars (i - 1), 1 ≤ v ∧ v ≤ N := fun v hv => by
    rw [mem_vars] at hv; omega
  have hvs : ∀ v, v ∈ vars (i + 1 - 1) ↔ v ∈ vars (i - 1) ++ [i] := fun v => by
    rw [List.mem_append, List.mem_singleton, mem_vars, mem_vars]; omega
  rw [initCell_congr hvs, initCell_snoc hpre hi]
  have e1 : prevAt N = 2 * (N + 1) := rfl
  have e2 : nextAt N = N + 1 := rfl
  have e5 : firstAt N = 9 * N + 6 := rfl
  repeat' split
  all_goals first
    | rfl
    | omega
    | (exact (initCell_zero (p := p) hpre (by omega)).symm)

/-- `initLoop` from variable `i` on (C:206–209): every cell ends as `initCell` says for all
the variables `1 … n`, given that it holds for `1 … i - 1`. -/
theorem initLoop_spec {n : Cell} (hn : NOk n) :
    ∀ (k : Nat) (db : Array Cell) (i : Cell), (n.toInt + 1 - i.toInt).toNat = k →
      1 ≤ i.toInt → i.toInt ≤ n.toInt + 1 → db.size ≤ 2 ^ 31 →
      (∀ p, 0 ≤ p → ldA (toDB db) p = initCell n.toInt (vars (i.toInt - 1)) p) →
      (initLoop (Lay.mk' n) db i).size ≤ 2 ^ 31 ∧
      ∀ p, 0 ≤ p → ldA (toDB (initLoop (Lay.mk' n) db i)) p = initCell n.toInt (vars n.toInt) p := by
  obtain ⟨eN, eNx, ePv, -, -, -, eF, eFi⟩ := Lay.mk'_toInt hn
  have hn1 := hn.1
  have hn2 := hn.2
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro db i hk hi1 hi2 hsz hcells
  rw [initLoop.eq_1]
  by_cases hle : i ≤ (Lay.mk' n).nVars
  · rw [if_pos hle]
    dsimp only
    have hle' : i.toInt ≤ n.toInt := by have := Int32.le_iff_toInt_le.mp hle; rw [eN] at this; exact this
    have h1 : ((1 : Cell)).toInt = 1 := rfl
    have h0 : ((0 : Cell)).toInt = 0 := rfl
    have hE : END.toInt = MicrosatLean.Faithful.END := by decide
    have hm1 : (i - 1).toInt = i.toInt - 1 := by rw [toInt_sub (by rw [h1]; omega) (by rw [h1]; omega), h1]
    have hp1 : (i + 1).toInt = i.toInt + 1 := by rw [toInt_add (by rw [h1]; omega) (by rw [h1]; omega), h1]
    have a1 : ((Lay.mk' n).prev + i).toInt = 2 * n.toInt + 2 + i.toInt := by
      rw [toInt_add (by omega) (by omega), ePv]
    have a2 : ((Lay.mk' n).next + (i - 1)).toInt = n.toInt + i.toInt := by
      rw [toInt_add (by rw [hm1]; omega) (by rw [hm1]; omega), eNx, hm1]; omega
    have a3 : ((Lay.mk' n).fls + i).toInt = 7 * n.toInt + 5 + i.toInt := by
      rw [toInt_add (by omega) (by omega), eF]
    have a4 : ((Lay.mk' n).fls - i).toInt = 7 * n.toInt + 5 - i.toInt := by
      rw [toInt_sub (by omega) (by omega), eF]
    have a6 : ((Lay.mk' n).first - i).toInt = 9 * n.toInt + 6 - i.toInt := by
      rw [toInt_sub (by omega) (by omega), eFi]
    have a7 : ((Lay.mk' n).first + i).toInt = 9 * n.toInt + 6 + i.toInt := by
      rw [toInt_add (by omega) (by omega), eFi]
    -- the seven writes, one at a time
    generalize hd1 : st db ((Lay.mk' n).prev + i) (i - 1) = d1
    have s1 : d1.size ≤ 2 ^ 31 := hd1 ▸ st_size hsz _ _
    have c1 : ∀ p, 0 ≤ p → ldA (toDB d1) p = if p = 2 * n.toInt + 2 + i.toInt then i.toInt - 1
        else ldA (toDB db) p := fun p hp => by
      rw [← hd1, ldA_st hsz (by omega) _ hp, a1, hm1]
    generalize hd2 : st d1 ((Lay.mk' n).next + (i - 1)) i = d2
    have s2 : d2.size ≤ 2 ^ 31 := hd2 ▸ st_size s1 _ _
    have c2 : ∀ p, 0 ≤ p → ldA (toDB d2) p = if p = n.toInt + i.toInt then i.toInt
        else ldA (toDB d1) p := fun p hp => by
      rw [← hd2, ldA_st s1 (by omega) _ hp, a2]
    generalize hd3 : st d2 ((Lay.mk' n).fls + i) 0 = d3
    have s3 : d3.size ≤ 2 ^ 31 := hd3 ▸ st_size s2 _ _
    have c3 : ∀ p, 0 ≤ p → ldA (toDB d3) p = if p = 7 * n.toInt + 5 + i.toInt then 0
        else ldA (toDB d2) p := fun p hp => by
      rw [← hd3, ldA_st s2 (by omega) _ hp, a3, h0]
    generalize hd4 : st d3 ((Lay.mk' n).fls - i) 0 = d4
    have s4 : d4.size ≤ 2 ^ 31 := hd4 ▸ st_size s3 _ _
    have c4 : ∀ p, 0 ≤ p → ldA (toDB d4) p = if p = 7 * n.toInt + 5 - i.toInt then 0
        else ldA (toDB d3) p := fun p hp => by
      rw [← hd4, ldA_st s3 (by omega) _ hp, a4, h0]
    generalize hd5 : st d4 i 0 = d5
    have s5 : d5.size ≤ 2 ^ 31 := hd5 ▸ st_size s4 _ _
    have c5 : ∀ p, 0 ≤ p → ldA (toDB d5) p = if p = i.toInt then 0
        else ldA (toDB d4) p := fun p hp => by
      rw [← hd5, ldA_st s4 (by omega) _ hp, h0]
    generalize hd6 : st d5 ((Lay.mk' n).first - i) END = d6
    have s6 : d6.size ≤ 2 ^ 31 := hd6 ▸ st_size s5 _ _
    have c6 : ∀ p, 0 ≤ p → ldA (toDB d6) p = if p = 9 * n.toInt + 6 - i.toInt then MicrosatLean.Faithful.END
        else ldA (toDB d5) p := fun p hp => by
      rw [← hd6, ldA_st s5 (by omega) _ hp, a6, hE]
    generalize hd7 : st d6 ((Lay.mk' n).first + i) END = d7
    have s7 : d7.size ≤ 2 ^ 31 := hd7 ▸ st_size s6 _ _
    have c7 : ∀ p, 0 ≤ p → ldA (toDB d7) p = if p = 9 * n.toInt + 6 + i.toInt then MicrosatLean.Faithful.END
        else ldA (toDB d6) p := fun p hp => by
      rw [← hd7, ldA_st s6 (by omega) _ hp, a7, hE]
    refine ih _ (by omega) d7 (i + 1) rfl (by omega) (by omega) s7 fun p hp => ?_
    rw [c7 p hp, c6 p hp, c5 p hp, c4 p hp, c3 p hp, c2 p hp, c1 p hp, hcells p hp, hp1]
    exact initLoop_cell ⟨hi1, hle'⟩ hp
  · rw [if_neg hle]
    have hgt : n.toInt < i.toInt := by
      rcases Int.lt_or_le n.toInt i.toInt with h | h
      · exact h
      · exact absurd (Int32.le_iff_toInt_le.mpr (by rw [eN]; exact h)) hle
    refine ⟨hsz, fun p hp => ?_⟩
    rw [hcells p hp, show i.toInt - 1 = n.toInt by omega]

/-- Zero cells read 0. -/
theorem ldA_replicate (k : Nat) {p : Int} (hp : 0 ≤ p) : ldA (toDB (Array.replicate k 0)) p = 0 := by
  unfold ldA
  rw [ld_eq_getD _ hp]
  simp only [toDB, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_replicate]
  split <;> rfl

/-- The fast `initCDCL` for a header with `0 ≤ nVars ≤ (2^30 - 7) / 10`: it does not run out
of memory, and the abstraction of its state (with any `nClauses`, `mem_max`, `fast`, `slow`)
is a faithful `initCDCL` state (`InitState`). -/
theorem initCDCL_fast {nVars : Int} (h0 : 0 ≤ nVars) (h1 : nVars ≤ 107374181) :
    ∃ L s, initCDCL (Int32.ofInt nVars) = some (L, s) ∧ NOk L.nVars ∧ s.db.size ≤ 2 ^ 31 ∧
      s.memUsed.toInt ≤ 2 ^ 30 ∧
      ∀ m M fa sl, InitState nVars m M { abs L s M fa sl with nClauses := m } := by
  have hx : (Int32.ofInt nVars).toInt = nVars := Int32.toInt_ofInt_of_le (by omega) (by omega)
  generalize Int32.ofInt nVars = x at hx
  have h1c : ((1 : Cell)).toInt = 1 := rfl
  generalize hn : (if x < 1 then 1 else x) = n
  have hnv : n.toInt = varsOf nVars := by
    rw [← hn]; unfold varsOf
    by_cases hlt : nVars < 1
    · rw [if_pos (Int32.lt_iff_toInt_lt.mpr (by rw [hx, h1c]; exact hlt)), if_pos hlt]; rfl
    · rw [if_neg (fun h => hlt (by have := Int32.lt_iff_toInt_lt.mp h; rw [hx, h1c] at this; exact this)),
        if_neg hlt, hx]
  have hN : 1 ≤ n.toInt ∧ n.toInt ≤ 107374181 := by rw [hnv]; unfold varsOf; split <;> omega
  have hok : NOk n := ⟨hN.1, by omega⟩
  obtain ⟨eN, eNx, ePv, eB, eR, eFS, eF, eFi⟩ := Lay.mk'_toInt hok
  have hlim : ((memMax - 7) / 10 : Cell).toInt = 107374181 := by decide
  have hnot : ¬ (n > (memMax - 7) / 10) := fun h => by
    have := Int32.lt_iff_toInt_lt.mp h; rw [hlim] at this; omega
  have h10c : ((10 : Cell)).toInt = 10 := rfl
  have h8c : ((8 : Cell)).toInt = 8 := rfl
  have h10 : ((10 : Cell) * n).toInt = 10 * n.toInt := by
    rw [Int32.toInt_mul, h10c]; exact Int.bmod_eq_of_le (by omega) (by omega)
  have hused : ((10 : Cell) * n + 8).toInt = 10 * n.toInt + 8 := by
    rw [toInt_add (by rw [h10, h8c]; omega) (by rw [h10, h8c]; omega), h10, h8c]
  unfold initCDCL
  rw [hn, if_neg hnot]
  dsimp only
  generalize hdb : initLoop (Lay.mk' n) (Array.replicate ((10 : Cell) * n + 8).toUInt32.toNat 0) 1 = db
  have hrep : (Array.replicate ((10 : Cell) * n + 8).toUInt32.toNat (0 : Cell)).size ≤ 2 ^ 31 := by
    rw [Array.size_replicate, toNat_toUInt32_of_nonneg (by omega), hused]; omega
  obtain ⟨hsz, hcells⟩ := initLoop_spec hok _ _ 1 rfl (by rw [h1c]; omega) (by rw [h1c]; omega) hrep
    (fun p hp => by
      rw [ldA_replicate _ hp, h1c]
      simp [initCell, vars])
  rw [hdb] at hsz hcells
  refine ⟨_, _, rfl, hok, hsz, by rw [hused]; omega, fun m M fa sl => ?_⟩
  have hst : (Lay.mk' n).falseStack.toInt = stackAt (varsOf nVars) := by rw [eFS, hnv]; rfl
  exact {
    nVars := by rw [← hnv]; exact eN
    nClauses := rfl
    mem_max := rfl
    mem_used := by show ((10 : Cell) * n + 8).toInt = _; rw [hused, hnv]; rfl
    nLemmas := rfl
    maxLemmas := rfl
    model := rfl
    next := by show (Lay.mk' n).next.toInt = _; rw [eNx, hnv]; rfl
    prev := by show (Lay.mk' n).prev.toInt = _; rw [ePv, hnv]; simp only [prevAt]; omega
    buffer := by show (Lay.mk' n).buffer.toInt = _; rw [eB, hnv]; simp only [bufferAt]; omega
    reason := by show (Lay.mk' n).reason.toInt = _; rw [eR, hnv]; rfl
    falseStack := hst
    «false» := by show (Lay.mk' n).fls.toInt = _; rw [eF, hnv]; rfl
    first := by show (Lay.mk' n).first.toInt = _; rw [eFi, hnv]; rfl
    forced := hst
    processed := hst
    assigned := hst
    head := hnv
    cells := fun p hp => by rw [← hnv]; exact hcells p hp }

end MicrosatLean.Fast.Verification
