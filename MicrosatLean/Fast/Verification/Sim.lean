import MicrosatLean.Fast.Solver
import MicrosatLean.Faithful.Verification.Memory
import MicrosatLean.Faithful.Verification.Assign
import MicrosatLean.Faithful.Verification.AddClause

/-!
# The fast port's memory simulates the faithful one

The fast arena `db : Array Int32` stands for the faithful `DB : Array Int` cell by cell
(`Int32.toInt`). Reads and writes agree while the array has fewer than `2^31` cells, which
the out-of-memory check guarantees (`memMax = 2^30`). This is the base of the simulation
proof: `FAST_PORT_NOTES.md`, "Correctness plan".
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver)
open MicrosatLean.Fast

/-- The faithful array a fast array stands for. -/
def toDB (db : Array Cell) : Array Int := db.map Int32.toInt

/-- A nonnegative `Int32` as an index. -/
theorem toNat_toUInt32_of_nonneg {p : Cell} (hp : 0 ≤ p.toInt) : p.toUInt32.toNat = p.toInt.toNat := by
  have h0 : (0 : Cell) ≤ p := Int32.le_iff_toInt_le.mpr (by simpa using hp)
  rw [Int32.toNat_toUInt32_of_le h0, Int32.toInt_eq_toNatClampNeg h0]
  simp

/-- A negative `Int32` lands at or beyond index `2^31`. -/
theorem toNat_toUInt32_of_neg {p : Cell} (hp : p.toInt < 0) : 2 ^ 31 ≤ p.toUInt32.toNat := by
  have h := BitVec.toInt_eq_toNat_cond p.toBitVec
  rw [Int32.toInt_toBitVec] at h
  have : p.toUInt32.toNat = p.toBitVec.toNat := rfl
  rw [this]
  split at h
  · omega
  · omega

/-- The `USize` index of a cell, as a number. -/
theorem toNat_toUSize (p : Cell) : p.toUInt32.toUSize.toNat = p.toUInt32.toNat := UInt32.toNat_toUSize _

/-- The array size as a `USize`, for arrays of at most `2^31` cells. -/
theorem toNat_usize {db : Array Cell} (h : db.size ≤ 2 ^ 31) : db.usize.toNat = db.size := by
  simp only [Array.usize, Nat.toUSize_eq]
  exact USize.toNat_ofNat_of_lt' (by have := USize.le_size; omega)

/-- Reading the fast arena reads the faithful one. -/
theorem ld_sim {db : Array Cell} (S : solver) (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31) (p : Cell) :
    (ld db p).toInt = S.ld p.toInt := by
  have hu := toNat_usize hsz
  unfold ld solver.ld
  by_cases hp : p.toInt < 0
  · dsimp only
    rw [if_pos hp, dif_neg]
    · rfl
    · intro h
      have := USize.lt_iff_toNat_lt.mp h
      rw [toNat_toUSize, hu] at this
      have := toNat_toUInt32_of_neg hp; omega
  · rw [if_neg hp, hDB]
    dsimp only
    have hp' : 0 ≤ p.toInt := Int.not_lt.mp hp
    have hidx := toNat_toUInt32_of_nonneg hp'
    split
    · rename_i h
      have hi : p.toInt.toNat < db.size := by
        have := USize.lt_iff_toNat_lt.mp h; rw [toNat_toUSize, hu, hidx] at this; exact this
      simp only [toDB, Array.getD_eq_getD_getElem?, Array.getElem?_map, Array.getElem?_eq_getElem hi,
        Option.map_some, Option.getD_some, Array.uget, toNat_toUSize, hidx]
    · rename_i h
      have hi : ¬ p.toInt.toNat < db.size := by
        intro hi; apply h; apply USize.lt_iff_toNat_lt.mpr; rw [toNat_toUSize, hu, hidx]; exact hi
      simp only [toDB, Array.getD_eq_getD_getElem?, Array.getElem?_map,
        Array.getElem?_eq_none (Nat.le_of_not_lt hi), Option.map_none, Option.getD_none]
      rfl

/-- `growAndStore` commutes with `toDB`. -/
theorem toDB_growAndStore (db : Array Cell) (i : Nat) (v : Cell) :
    toDB (growAndStore db i v) = solver.growAndStore (toDB db) i v.toInt := by
  simp [toDB, growAndStore, solver.growAndStore, Array.map_push, Array.map_append]

/-- Writing the fast arena writes the faithful one, and keeps it at most `2^31` cells. -/
theorem st_sim {db : Array Cell} (S : solver) (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31) (p v : Cell) :
    (S.st p.toInt v.toInt).DB = toDB (st db p v) ∧ (st db p v).size ≤ 2 ^ 31 := by
  have hu := toNat_usize hsz
  unfold st solver.st
  dsimp only
  by_cases hp : p.toInt < 0
  · have hn := toNat_toUInt32_of_neg hp
    have hlt : ¬ p.toUInt32.toUSize < db.usize := fun h => by
      have := USize.lt_iff_toNat_lt.mp h; rw [toNat_toUSize, hu] at this; omega
    have hp32 : p < 0 := Int32.lt_iff_toInt_lt.mpr (by simpa using hp)
    rw [if_pos hp, dif_neg hlt, if_pos hp32]
    exact ⟨hDB, hsz⟩
  · have hp' : 0 ≤ p.toInt := Int.not_lt.mp hp
    have hidx := toNat_toUInt32_of_nonneg hp'
    have hp32 : ¬ p < 0 := fun h => hp (by simpa using Int32.lt_iff_toInt_lt.mp h)
    rw [if_neg hp]
    have hmax := Int32.toInt_lt p
    by_cases hin : p.toInt.toNat < db.size
    · have hlt : p.toUInt32.toUSize < db.usize :=
        USize.lt_iff_toNat_lt.mpr (by rw [toNat_toUSize, hu, hidx]; exact hin)
      have hin' : p.toInt.toNat < S.DB.size := by rw [hDB, toDB, Array.size_map]; exact hin
      rw [dif_pos hlt, dif_pos hin']
      refine ⟨?_, by simp [Array.uset]; exact hsz⟩
      simp only [hDB, toDB, Array.uset, toNat_toUSize, hidx, Array.map_set]
    · have hlt : ¬ p.toUInt32.toUSize < db.usize := fun h => by
        have := USize.lt_iff_toNat_lt.mp h; rw [toNat_toUSize, hu, hidx] at this; exact hin this
      have hin' : ¬ p.toInt.toNat < S.DB.size := by rw [hDB, toDB, Array.size_map]; exact hin
      rw [dif_neg hlt, if_neg hp32, dif_neg hin', hDB, hidx, toDB_growAndStore]
      refine ⟨rfl, ?_⟩
      have := Int32.toInt_eq_toNatClampNeg (Int32.le_iff_toInt_le.mpr (by simpa using hp'))
      simp [growAndStore]; omega

/-! ### Arithmetic without overflow -/

theorem toInt_add {a b : Cell} (h1 : -2 ^ 31 ≤ a.toInt + b.toInt) (h2 : a.toInt + b.toInt < 2 ^ 31) :
    (a + b).toInt = a.toInt + b.toInt := by
  rw [Int32.toInt_add]; exact Int.bmod_eq_of_le (by omega) (by omega)

theorem toInt_sub {a b : Cell} (h1 : -2 ^ 31 ≤ a.toInt - b.toInt) (h2 : a.toInt - b.toInt < 2 ^ 31) :
    (a - b).toInt = a.toInt - b.toInt := by
  rw [Int32.toInt_sub]; exact Int.bmod_eq_of_le (by omega) (by omega)

theorem toInt_neg {a : Cell} (h : -2 ^ 31 < a.toInt) : (-a).toInt = -a.toInt := by
  rw [Int32.toInt_neg]; have := Int32.toInt_lt a; exact Int.bmod_eq_of_le (by omega) (by omega)

/-- `absC` is C's `abs` (no overflow at `-2^31`). -/
theorem toInt_absC {a : Cell} (h : -2 ^ 31 < a.toInt) : (absC a).toInt = MicrosatLean.Faithful.abs a.toInt := by
  unfold absC MicrosatLean.Faithful.abs
  by_cases ha : a.toInt < 0
  · rw [if_pos (Int32.lt_iff_toInt_lt.mpr (by simpa using ha)), if_pos ha, toInt_neg h]
  · rw [if_neg (fun h' => ha (by simpa using Int32.lt_iff_toInt_lt.mp h')), if_neg ha]

/-- The numeral `n` as a cell, for `n < 2^31`. -/
theorem toInt_ofNat {n : Nat} (h : n < 2 ^ 31) : (OfNat.ofNat n : Cell).toInt = n := by
  show (Int32.ofNat n).toInt = n
  rw [Int32.toInt_ofNat', show (Int32.size : Nat) = 4294967296 from rfl]
  exact Int.bmod_eq_of_le (by omega) (by omega)

/-! ### `assign` (C:42–47) -/

/-- The fast `assign` writes what the faithful one writes, given the offsets and bounds:
the literal is within `±2^29`, the offsets and the reason pointer below `2^30`. -/
theorem assign_sim (S : solver) {db : Array Cell} (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31)
    {L : Lay} (hfls : S.false = L.fls.toInt) (hrs : S.reason = L.reason.toInt) (hmodel : S.model = 0)
    (hL : 0 ≤ L.fls.toInt ∧ L.fls.toInt < 2 ^ 30 ∧ 0 ≤ L.reason.toInt ∧ L.reason.toInt < 2 ^ 30)
    {assigned reason : Cell} (hA : S.assigned = assigned.toInt)
    (hr : 0 ≤ reason.toInt ∧ reason.toInt < 2 ^ 30)
    (hlit : -2 ^ 29 ≤ S.ld reason.toInt ∧ S.ld reason.toInt ≤ 2 ^ 29) (f : Bool) :
    (MicrosatLean.Faithful.assign S reason.toInt (if f then 1 else 0)).DB =
      toDB (assign L db assigned reason f) ∧ (assign L db assigned reason f).size ≤ 2 ^ 31 := by
  rw [MicrosatLean.Faithful.Verification.assign_eq]
  unfold assign
  have hl := ld_sim S hDB hsz reason
  generalize hlit' : ld db reason = lit at hl ⊢
  rw [← hl] at hlit ⊢
  have h1 : ((1 : Cell)).toInt = 1 := rfl
  have habs : (absC lit).toInt = MicrosatLean.Faithful.abs lit.toInt := toInt_absC (by omega)
  have habs' : 0 ≤ MicrosatLean.Faithful.abs lit.toInt ∧ MicrosatLean.Faithful.abs lit.toInt ≤ 2 ^ 29 := by
    unfold MicrosatLean.Faithful.abs; split <;> omega
  obtain ⟨e1, s1⟩ := st_sim S hDB hsz (L.fls - lit) (if f then IMPLIED else 1)
  have p1 : (L.fls - lit).toInt = S.false + -lit.toInt := by rw [toInt_sub (by omega) (by omega), hfls]; omega
  have v1 : (if f then IMPLIED else 1 : Cell).toInt =
      (if ((if f then 1 else 0 : Int) != 0) = true then MicrosatLean.Faithful.IMPLIED else 1) := by
    cases f <;> rfl
  rw [p1, v1] at e1
  obtain ⟨e2, s2⟩ := st_sim _ e1 s1 assigned (-lit)
  rw [← hA, toInt_neg (by omega)] at e2
  obtain ⟨e3, s3⟩ := st_sim ({ (S.st (S.false + -lit.toInt)
      (if ((if f then 1 else 0 : Int) != 0) = true then MicrosatLean.Faithful.IMPLIED else 1)).st S.assigned (-lit.toInt)
      with assigned := S.assigned + 1 } : solver) e2 s2 (L.reason + absC lit) (1 + reason)
  rw [toInt_add (by omega) (by omega), toInt_add (by rw [h1]; omega) (by rw [h1]; omega), habs, ← hrs, h1] at e3
  obtain ⟨e4, s4⟩ := st_sim _ e3 s3 (absC lit) (if lit > 0 then 1 else 0)
  have v4 : (if lit > 0 then 1 else 0 : Cell).toInt = (if lit.toInt > 0 then 1 else 0 : Int) := by
    by_cases h : lit.toInt > 0
    · rw [if_pos h, if_pos (Int32.lt_iff_toInt_lt.mpr (by simpa using h))]; rfl
    · rw [if_neg h, if_neg (fun h' => h (by simpa using Int32.lt_iff_toInt_lt.mp h'))]; rfl
  rw [habs, v4] at e4
  rw [hmodel, Int.zero_add]
  exact ⟨e4, s4⟩

/-! ### The relation between fast and faithful states -/

/-- A fast state (`L`, `s`) stands for the faithful state `S`: the same cells (as `Int`), the
same offsets and the same counters and pointers. `res`, `fast`, `slow`, `mem_max` and
`nClauses` are not related (`FAST_PORT_NOTES.md`). -/
structure Sim (L : Lay) (s : St) (S : solver) : Prop where
  db : S.DB = toDB s.db
  size : s.db.size ≤ 2 ^ 31
  nVars : S.nVars = L.nVars.toInt
  model : S.model = 0
  next : S.next = L.next.toInt
  prev : S.prev = L.prev.toInt
  buffer : S.buffer = L.buffer.toInt
  reason : S.reason = L.reason.toInt
  falseStack : S.falseStack = L.falseStack.toInt
  fls : S.false = L.fls.toInt
  first : S.first = L.first.toInt
  memUsed : S.mem_used = s.memUsed.toInt
  memFixed : S.mem_fixed = s.memFixed.toInt
  maxLemmas : S.maxLemmas = s.maxLemmas.toInt
  nLemmas : S.nLemmas = s.nLemmas.toInt
  nConflicts : S.nConflicts = s.nConflicts.toInt
  forced : S.forced = s.forced.toInt
  processed : S.processed = s.processed.toInt
  assigned : S.assigned = s.assigned.toInt
  head : S.head = s.head.toInt

/-- The variable counts the fast port accepts (`initCDCL`: `10 n + 7 ≤ 2^30`). -/
def NOk (n : Cell) : Prop := 1 ≤ n.toInt ∧ 10 * n.toInt + 7 ≤ 2 ^ 30

/-- The offsets of `Lay.mk' n` as numbers (no overflow for an accepted `n`). -/
theorem Lay.mk'_toInt {n : Cell} (h : NOk n) :
    (Lay.mk' n).nVars.toInt = n.toInt ∧ (Lay.mk' n).next.toInt = n.toInt + 1 ∧
    (Lay.mk' n).prev.toInt = 2 * n.toInt + 2 ∧ (Lay.mk' n).buffer.toInt = 3 * n.toInt + 3 ∧
    (Lay.mk' n).reason.toInt = 4 * n.toInt + 3 ∧ (Lay.mk' n).falseStack.toInt = 5 * n.toInt + 4 ∧
    (Lay.mk' n).fls.toInt = 7 * n.toInt + 5 ∧ (Lay.mk' n).first.toInt = 9 * n.toInt + 6 := by
  obtain ⟨h1, h2⟩ := h
  have mul : ∀ k : Nat, k ≤ 9 → ((OfNat.ofNat k : Cell) * n).toInt = k * n.toInt := fun k hk => by
    rw [Int32.toInt_mul, toInt_ofNat (by omega)]
    have b1 : (k : Int) * n.toInt ≤ 9 * n.toInt := Int.mul_le_mul_of_nonneg_right (by omega) (by omega)
    have b2 : 0 ≤ (k : Int) * n.toInt := Int.mul_nonneg (by omega) (by omega)
    exact Int.bmod_eq_of_le (by omega) (by omega)
  have add : ∀ (a : Cell) (k : Nat), k ≤ 6 → 0 ≤ a.toInt → a.toInt ≤ 9 * n.toInt →
      (a + (OfNat.ofNat k : Cell)).toInt = a.toInt + k := fun a k hk h0 h9 => by
    rw [toInt_add (by rw [toInt_ofNat (by omega)]; omega) (by rw [toInt_ofNat (by omega)]; omega),
      toInt_ofNat (by omega)]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Lay.mk']
  · rw [add n 1 (by omega) (by omega) (by omega)]; rfl
  · rw [add _ 2 (by omega) (by rw [mul 2 (by omega)]; omega) (by rw [mul 2 (by omega)]; omega), mul 2 (by omega)]; rfl
  · rw [add _ 3 (by omega) (by rw [mul 3 (by omega)]; omega) (by rw [mul 3 (by omega)]; omega), mul 3 (by omega)]; rfl
  · rw [add _ 3 (by omega) (by rw [mul 4 (by omega)]; omega) (by rw [mul 4 (by omega)]; omega), mul 4 (by omega)]; rfl
  · rw [add _ 4 (by omega) (by rw [mul 5 (by omega)]; omega) (by rw [mul 5 (by omega)]; omega), mul 5 (by omega)]; rfl
  · rw [add _ 5 (by omega) (by rw [mul 7 (by omega)]; omega) (by rw [mul 7 (by omega)]; omega), mul 7 (by omega)]; rfl
  · rw [add _ 6 (by omega) (by rw [mul 9 (by omega)]; omega) (by rw [mul 9 (by omega)]; omega), mul 9 (by omega)]; rfl

/-! ### `addWatch` (C:49–50) and `unassign` (C:36) -/

/-- The fast `addWatch` writes what the faithful one writes (the head cell `first + lit`
without overflow, and the link cell `mem` nonnegative). -/
theorem addWatch_sim (S : solver) {db : Array Cell} (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31)
    {L : Lay} (hfirst : S.first = L.first.toInt) {lit mem : Cell}
    (hb : -2 ^ 31 ≤ L.first.toInt + lit.toInt ∧ L.first.toInt + lit.toInt < 2 ^ 31) :
    (MicrosatLean.Faithful.addWatch S lit.toInt mem.toInt).DB = toDB (addWatch L db lit mem) ∧
      (addWatch L db lit mem).size ≤ 2 ^ 31 := by
  unfold MicrosatLean.Faithful.addWatch addWatch
  have hh : (L.first + lit).toInt = S.first + lit.toInt := by rw [toInt_add hb.1 hb.2, hfirst]
  have hl := ld_sim S hDB hsz (L.first + lit)
  rw [hh] at hl
  obtain ⟨e1, s1⟩ := st_sim S hDB hsz mem (ld db (L.first + lit))
  rw [hl] at e1
  obtain ⟨e2, s2⟩ := st_sim _ e1 s1 (L.first + lit) mem
  rw [hh] at e2
  dsimp only
  rw [MicrosatLean.Faithful.Verification.st_first]
  exact ⟨e2, s2⟩

/-- The fast `unassign` (a flag write) is the faithful one. -/
theorem unassign_sim (S : solver) {db : Array Cell} (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31)
    {L : Lay} (hfls : S.false = L.fls.toInt) {lit : Cell}
    (hb : -2 ^ 31 ≤ L.fls.toInt + lit.toInt ∧ L.fls.toInt + lit.toInt < 2 ^ 31) :
    (MicrosatLean.Faithful.unassign S lit.toInt).DB = toDB (st db (L.fls + lit) 0) ∧
      (st db (L.fls + lit) 0).size ≤ 2 ^ 31 := by
  rw [MicrosatLean.Faithful.Verification.unassign_eq]
  have hh : (L.fls + lit).toInt = S.false + lit.toInt := by rw [toInt_add hb.1 hb.2, hfls]
  obtain ⟨e, s1⟩ := st_sim S hDB hsz (L.fls + lit) 0
  rw [hh] at e
  exact ⟨e, s1⟩

/-! ### The abstraction function -/

/-- The faithful state a fast state stands for. `mem_max`, `fast` and `slow` are given
(`FAST_PORT_NOTES.md`); `res` and `nClauses` are 0. -/
def abs (L : Lay) (s : St) (M fa sl : Int) : solver where
  DB := toDB s.db
  nVars := L.nVars.toInt
  nClauses := 0
  mem_used := s.memUsed.toInt
  mem_fixed := s.memFixed.toInt
  mem_max := M
  maxLemmas := s.maxLemmas.toInt
  nLemmas := s.nLemmas.toInt
  buffer := L.buffer.toInt
  nConflicts := s.nConflicts.toInt
  model := 0
  reason := L.reason.toInt
  falseStack := L.falseStack.toInt
  «false» := L.fls.toInt
  first := L.first.toInt
  forced := s.forced.toInt
  processed := s.processed.toInt
  assigned := s.assigned.toInt
  next := L.next.toInt
  prev := L.prev.toInt
  head := s.head.toInt
  res := 0
  fast := fa
  slow := sl

/-- Writing to the fast state, then abstracting, is writing to the abstraction. -/
theorem abs_st (L : Lay) (s : St) (M fa sl : Int) (hsz : s.db.size ≤ 2 ^ 31) (p v : Cell) :
    abs L { s with db := st s.db p v } M fa sl = (abs L s M fa sl).st p.toInt v.toInt := by
  obtain ⟨e, -⟩ := st_sim (abs L s M fa sl) rfl hsz p v
  apply MicrosatLean.Faithful.solver.ext
  case DB => exact e.symm
  all_goals simp [abs]

/-! ### `addClause` (C:59–66) -/

/-- Reading memory depends only on `DB`. -/
theorem ld_with_DB (S T : solver) (A : Array Int) (q : Int) :
    ({ S with DB := A } : solver).ld q = ({ T with DB := A } : solver).ld q := rfl

/-- The copy loop of `addClause` (C:64) from index `i`: the cells `dst + j` (`i ≤ j < size`)
get the starting memory's cells `src + j`, and no other cell changes. The source lies below
the destination (the buffer), or at or above it (`reduceDB` moves lemmas down), so every
source cell is read before any write could reach it. -/
theorem copyLoop_spec {dst src size : Cell} (hd0 : 0 ≤ dst.toInt) (hs0 : 0 ≤ src.toInt)
    (hd : dst.toInt + size.toInt < 2 ^ 31) (hs : src.toInt + size.toInt < 2 ^ 31)
    (hsep : src.toInt + size.toInt ≤ dst.toInt ∨ dst.toInt ≤ src.toInt) :
    ∀ (k : Nat) (S : solver) (db : Array Cell) (i : Cell), (size.toInt - i.toInt).toNat = k →
      S.DB = toDB db → db.size ≤ 2 ^ 31 → 0 ≤ i.toInt → i.toInt ≤ size.toInt →
      (copyLoop db dst src i size).size ≤ 2 ^ 31 ∧
      (∀ j : Int, i.toInt ≤ j → j < size.toInt →
        ({ S with DB := toDB (copyLoop db dst src i size) } : solver).ld (dst.toInt + j) = S.ld (src.toInt + j)) ∧
      (∀ q, 0 ≤ q → (q < dst.toInt + i.toInt ∨ dst.toInt + size.toInt ≤ q) →
        ({ S with DB := toDB (copyLoop db dst src i size) } : solver).ld q = S.ld q) := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro S db i hk hDB hsz hi0 hi
  rw [copyLoop.eq_1]
  by_cases hlt : i < size
  · rw [if_pos hlt]
    have hlt' : i.toInt < size.toInt := Int32.lt_iff_toInt_lt.mp hlt
    have h1 : ((1 : Cell)).toInt = 1 := rfl
    have hdi : (dst + i).toInt = dst.toInt + i.toInt := toInt_add (by omega) (by omega)
    have hsi : (src + i).toInt = src.toInt + i.toInt := toInt_add (by omega) (by omega)
    have hi1 : (i + 1).toInt = i.toInt + 1 := by rw [toInt_add (by rw [h1]; omega) (by rw [h1]; omega), h1]
    have hl := ld_sim S hDB hsz (src + i)
    obtain ⟨e, hsz'⟩ := st_sim S hDB hsz (dst + i) (ld db (src + i))
    rw [hdi, hl, hsi] at e
    obtain ⟨r1, r2, r3⟩ := ih _ (by omega) _ _ (i + 1) rfl e hsz' (by omega) (by omega)
    rw [hi1] at r2 r3
    refine ⟨r1, fun j hj1 hj2 => ?_, fun q hq hout => ?_⟩
    · rcases Int.lt_or_eq_of_le hj1 with hj | hj
      · rw [ld_with_DB S _, r2 j (by omega) hj2,
          MicrosatLean.Faithful.Verification.ld_st_of_ne _ _ (by omega) (by omega) (by omega)]
      · subst hj
        rw [ld_with_DB S _, r3 _ (by omega) (by omega),
          MicrosatLean.Faithful.Verification.ld_st_self _ _ (by omega)]
    · rw [ld_with_DB S _, r3 q hq (by omega),
        MicrosatLean.Faithful.Verification.ld_st_of_ne _ _ (by omega) hq (by omega)]
  · rw [if_neg hlt]
    have hge : size.toInt ≤ i.toInt := Int.not_lt.mp (fun h => hlt (Int32.lt_iff_toInt_lt.mpr h))
    refine ⟨hsz, fun j hj1 hj2 => by omega, fun q _ _ => ?_⟩
    rw [← hDB]

open MicrosatLean.Faithful.Verification in
/-- The two watch writes of `addClause` (C:61–63) leave every cell as `afterWatches` says:
link 0 and link 1 of the new record hold the old list heads, and the heads point to them.
(The faithful proof does this inside `addClause_spec`.) -/
theorem afterWatches_two (S0 : solver) {Ls : List Int} {in_ : Int} (hin : 0 ≤ in_)
    (hu : 0 ≤ S0.mem_used) (hl : 1 < Ls.length)
    (hsrc0 : S0.ld in_ = Ls[0]!) (hsrc1 : S0.ld (in_ + 1) = Ls[1]!)
    (hheads : ∀ i < 2, 0 ≤ S0.first + Ls[i]! ∧ S0.first + Ls[i]! < S0.mem_used ∧
       (S0.first + Ls[i]! < in_ ∨ in_ + 1 < S0.first + Ls[i]!))
    (hsrc_le : in_ + 1 < S0.mem_used ∨ S0.mem_used + 2 ≤ in_)
    (hdistinct : Ls[0]! ≠ Ls[1]!) :
    ∀ q, 0 ≤ q → (MicrosatLean.Faithful.addWatch
      (MicrosatLean.Faithful.addWatch S0 (S0.ld in_) S0.mem_used)
      ((MicrosatLean.Faithful.addWatch S0 (S0.ld in_) S0.mem_used).ld (in_ + 1)) (S0.mem_used + 1)).ld q =
      afterWatches S0 Ls q := by
  intro q hq
  obtain ⟨h0n, h0lt, h0src⟩ := hheads 0 (by omega)
  obtain ⟨h1n, h1lt, h1src⟩ := hheads 1 (by omega)
  have hd : S0.first + Ls[0]! ≠ S0.first + Ls[1]! := fun h => hdistinct (by omega)
  have a1 : S0.first + Ls[0]! ≠ S0.mem_used := by omega
  have a2 : S0.first + Ls[0]! ≠ S0.mem_used + 1 := by omega
  have a3 : S0.first + Ls[1]! ≠ S0.mem_used := by omega
  have a4 : S0.first + Ls[1]! ≠ S0.mem_used + 1 := by omega
  have a6 : (S0.mem_used + 1 : Int) ≠ S0.mem_used := by omega
  have a7 : S0.first + Ls[0]! ≠ in_ + 1 := by omega
  have a8 : S0.mem_used ≠ in_ + 1 := by omega
  have hW1 : (MicrosatLean.Faithful.addWatch S0 (S0.ld in_) S0.mem_used).ld (in_ + 1) = Ls[1]! := by
    rw [addWatch_eq, hsrc0, ld_st _ _ (by omega) (by omega), if_neg (Ne.symm a7),
      ld_st _ _ (by omega) (by omega), if_neg (Ne.symm a8), hsrc1]
  rw [hW1]
  simp only [addWatch_eq, st_first, hsrc0, afterWatches, if_pos hl]
  have hin1 : ((S0.st S0.mem_used (S0.ld (S0.first + Ls[0]!))).st (S0.first + Ls[0]!) S0.mem_used).ld
      (S0.first + Ls[1]!) = S0.ld (S0.first + Ls[1]!) := by
    rw [ld_st _ _ (by omega) (by omega), if_neg (Ne.symm hd), ld_st _ _ (by omega) (by omega), if_neg a3]
  rw [hin1, ld_st _ _ (by omega) hq, ld_st _ _ (by omega) hq, ld_st _ _ (by omega) hq, ld_st _ _ (by omega) hq]
  by_cases e1 : q = S0.first + Ls[1]!
  · subst e1
    rw [if_pos rfl, if_neg a3, if_neg (Ne.symm hd), if_neg a4, if_pos rfl]
  · by_cases e2 : q = S0.mem_used + 1
    · subst e2
      rw [if_neg e1, if_pos rfl, if_neg a6, if_neg (Ne.symm a2), if_pos rfl]
    · by_cases e3 : q = S0.first + Ls[0]!
      · subst e3
        rw [if_neg e1, if_neg e2, if_pos rfl, if_neg a1, if_pos rfl]
      · by_cases e4 : q = S0.mem_used
        · subst e4
          rw [if_neg e1, if_neg e2, if_neg e3, if_pos rfl, if_pos rfl]
        · rw [if_neg e1, if_neg e2, if_neg e3, if_neg e4, if_neg e4, if_neg e3, if_neg e2, if_neg e1]

theorem memMax_toInt : memMax.toInt = 2 ^ 30 := by decide

open MicrosatLean.Faithful.Verification in
@[simp] theorem addWatch_first (S : solver) (lit mem : Int) :
    (MicrosatLean.Faithful.addWatch S lit mem).first = S.first := by
  simp [addWatch_eq]

open MicrosatLean.Faithful.Verification in
/-- The two watch writes of the fast `addClause` (C:61–63) leave the cells as `afterWatches`
says (with no watch writes for a unit or empty clause). -/
theorem addClause_watches {L : Lay} {s : St} {M fa sl : Int} {src size : Cell} {Ls : List Int}
    (hsz : s.db.size ≤ 2 ^ 31) (hsize : size.toInt = Ls.length)
    (hsrc : ∀ i (h : i < Ls.length), (abs L s M fa sl).ld (src.toInt + i) = Ls[i])
    (hin : 0 ≤ src.toInt) (hsrc_hi : src.toInt + size.toInt ≤ 2 ^ 30)
    (hsrc_le : src.toInt + size.toInt ≤ s.memUsed.toInt ∨ (0 ≤ s.memUsed.toInt ∧ s.memUsed.toInt + 2 ≤ src.toInt))
    (hheads : 1 < Ls.length → ∀ i < 2, 0 ≤ L.first.toInt + Ls[i]! ∧ L.first.toInt + Ls[i]! < s.memUsed.toInt ∧
       (L.first.toInt + Ls[i]! < src.toInt ∨ src.toInt + size.toInt ≤ L.first.toInt + Ls[i]!))
    (hdistinct : 1 < Ls.length → Ls[0]! ≠ Ls[1]!)
    (hu0 : 0 ≤ s.memUsed.toInt) (hmem : s.memUsed.toInt + size.toInt + 3 ≤ 2 ^ 30)
    (hfirst : 0 ≤ L.first.toInt ∧ L.first.toInt < 2 ^ 30) (hlits : ∀ l ∈ Ls, -2 ^ 29 ≤ l ∧ l ≤ 2 ^ 29) :
    let db1 := if size > 1 then
      addWatch L (addWatch L s.db (ld s.db src) s.memUsed) (ld (addWatch L s.db (ld s.db src) s.memUsed) (src + 1))
        (s.memUsed + 1) else s.db
    db1.size ≤ 2 ^ 31 ∧
      ∀ q, 0 ≤ q → ({ abs L s M fa sl with DB := toDB db1 } : solver).ld q = afterWatches (abs L s M fa sl) Ls q := by
  intro db1
  generalize hS0 : abs L s M fa sl = S0 at hsrc ⊢
  have h1 : ((1 : Cell)).toInt = 1 := rfl
  have hmu : S0.mem_used = s.memUsed.toInt := by rw [← hS0]; rfl
  have hfi : S0.first = L.first.toInt := by rw [← hS0]; rfl
  have hDB0 : S0.DB = toDB s.db := by rw [← hS0]; rfl
  by_cases hgt : size > 1
  · have hdb1 : db1 = addWatch L (addWatch L s.db (ld s.db src) s.memUsed)
        (ld (addWatch L s.db (ld s.db src) s.memUsed) (src + 1)) (s.memUsed + 1) := if_pos hgt
    rw [hdb1]
    have hgt' : 1 < Ls.length := by have := Int32.lt_iff_toInt_lt.mp hgt; rw [h1] at this; omega
    have hsrc0 : S0.ld src.toInt = Ls[0]! := by
      have := hsrc 0 (by omega); simp only [Int.ofNat_zero, Int.add_zero] at this
      rw [this, getElem!_pos Ls 0 (by omega)]
    have hsrc1 : S0.ld (src.toInt + 1) = Ls[1]! := by
      have := hsrc 1 (by omega); rw [show ((1 : Nat) : Int) = 1 from rfl] at this
      rw [this, getElem!_pos Ls 1 (by omega)]
    have hl0 : -2 ^ 29 ≤ Ls[0]! ∧ Ls[0]! ≤ 2 ^ 29 := by
      rw [getElem!_pos Ls 0 (by omega)]; exact hlits _ (List.getElem_mem _)
    have hl1 : -2 ^ 29 ≤ Ls[1]! ∧ Ls[1]! ≤ 2 ^ 29 := by
      rw [getElem!_pos Ls 1 (by omega)]; exact hlits _ (List.getElem_mem _)
    obtain ⟨hh0n, hh0lt, hh0src⟩ := hheads hgt' 0 (by omega)
    obtain ⟨hh1n, hh1lt, hh1src⟩ := hheads hgt' 1 (by omega)
    have e0 := ld_sim S0 hDB0 hsz src
    obtain ⟨w1, sz1⟩ := addWatch_sim S0 hDB0 hsz (L := L) hfi (lit := ld s.db src) (mem := s.memUsed)
      (by rw [e0, hsrc0]; omega)
    -- the second literal, read after the first watch write
    have hW1v : (MicrosatLean.Faithful.addWatch S0 (S0.ld src.toInt) S0.mem_used).ld (src.toInt + 1) = Ls[1]! := by
      rw [addWatch_eq, hsrc0, ld_st _ _ (by omega) (by omega), if_neg (by omega),
        ld_st _ _ (by omega) (by omega), if_neg (by omega), hsrc1]
    have e1 := ld_sim _ w1 sz1 (src + 1)
    rw [toInt_add (by rw [h1]; omega) (by rw [h1]; omega), h1, e0, ← hmu, hW1v] at e1
    obtain ⟨w2, sz2⟩ := addWatch_sim _ w1 sz1 (L := L) (by rw [addWatch_first]; exact hfi)
      (lit := ld (addWatch L s.db (ld s.db src) s.memUsed) (src + 1)) (mem := s.memUsed + 1)
      (by rw [e1]; omega)
    refine ⟨sz2, fun q hq => ?_⟩
    have hm1 : (s.memUsed + 1).toInt = S0.mem_used + 1 := by
      rw [toInt_add (by rw [h1]; omega) (by rw [h1]; omega), h1, hmu]
    rw [← w2, e1, e0, ← hmu, hm1]
    show (MicrosatLean.Faithful.addWatch (MicrosatLean.Faithful.addWatch S0 (S0.ld src.toInt) S0.mem_used) Ls[1]!
      (S0.mem_used + 1)).ld q = _
    rw [← hW1v]
    exact afterWatches_two S0 hin (by omega) hgt' hsrc0 hsrc1
      (fun i hi => by have := hheads hgt' i hi; omega) (by omega) (hdistinct hgt') q hq
  · have hdb1 : db1 = s.db := if_neg hgt
    have hle : ¬ 1 < Ls.length := fun h => hgt (Int32.lt_iff_toInt_lt.mpr (by rw [h1]; omega))
    rw [hdb1]
    refine ⟨hsz, fun q hq => ?_⟩
    rw [← hDB0]
    simp [afterWatches, hle]

/-- Reading a faithful memory given as its array (`ld` only reads `DB`). -/
def ldA (A : Array Int) (q : Int) : Int := ({ (default : solver) with DB := A } : solver).ld q

theorem ld_eq_ldA (S : solver) (q : Int) : S.ld q = ldA S.DB q := rfl

open MicrosatLean.Faithful.Verification in
/-- The fields after the fast `addClause` are those of `added`. -/
theorem abs_added {L : Lay} {s : St} {M fa sl : Int} {size mu : Cell} (D : Array Cell) (irr : Bool)
    (hmu : mu.toInt = s.memUsed.toInt + size.toInt + 3) (hcnt : 0 ≤ s.nLemmas.toInt ∧ s.nLemmas.toInt < 2 ^ 30) :
    abs L { s with
        db := D, memUsed := mu, memFixed := if irr then mu else s.memFixed,
        nLemmas := if irr then s.nLemmas else s.nLemmas + 1 } M fa sl =
      added (abs L s M fa sl) size.toInt (if irr then 1 else 0) (toDB D) := by
  have h1 : ((1 : Cell)).toInt = 1 := rfl
  have hn : (s.nLemmas + 1).toInt = s.nLemmas.toInt + 1 := by
    rw [toInt_add (by rw [h1]; omega) (by rw [h1]; omega), h1]
  cases irr
  · simp only [abs, added, hmu, hn, Bool.false_eq_true, if_false]; rfl
  · simp only [abs, added, hmu, if_true]; rfl

open MicrosatLean.Faithful.Verification in
/-- The fast `addClause` (C:59–66), when the record fits below `memMax`, meets the faithful
postcondition `AddClausePost` (used by `WatchLists.addClause` and `Database.addLemma`) for the
abstracted states. The hypotheses are those of `addClause_spec`, plus bounds that rule out
`Int32` overflow. The caller updates `memFixed` (input clause) or `nLemmas` (lemma). -/
theorem addClause_post {L : Lay} {s : St} {M fa sl : Int} {src size : Cell} {Ls : List Int}
    (irr : Bool) (hsz : s.db.size ≤ 2 ^ 31) (hsize : size.toInt = Ls.length)
    (hsrc : ∀ i (h : i < Ls.length), (abs L s M fa sl).ld (src.toInt + i) = Ls[i])
    (hin : 0 ≤ src.toInt) (hsrc_hi : src.toInt + size.toInt ≤ 2 ^ 30)
    (hsrc_le : src.toInt + size.toInt ≤ s.memUsed.toInt ∨ (0 ≤ s.memUsed.toInt ∧ s.memUsed.toInt + 2 ≤ src.toInt))
    (hheads : 1 < Ls.length → ∀ i < 2, 0 ≤ L.first.toInt + Ls[i]! ∧ L.first.toInt + Ls[i]! < s.memUsed.toInt ∧
       (L.first.toInt + Ls[i]! < src.toInt ∨ src.toInt + size.toInt ≤ L.first.toInt + Ls[i]!))
    (hdistinct : 1 < Ls.length → Ls[0]! ≠ Ls[1]!)
    (hu0 : 0 ≤ s.memUsed.toInt) (hmem : s.memUsed.toInt + size.toInt + 3 ≤ 2 ^ 30)
    (hfirst : 0 ≤ L.first.toInt ∧ L.first.toInt < 2 ^ 30) (hlits : ∀ l ∈ Ls, -2 ^ 29 ≤ l ∧ l ≤ 2 ^ 29)
    (hcnt : 0 ≤ s.nLemmas.toInt ∧ s.nLemmas.toInt < 2 ^ 30) :
    (addClause L s.db s.memUsed src size).2.2.toInt = s.memUsed.toInt + 2 ∧
    (addClause L s.db s.memUsed src size).2.1.toInt = s.memUsed.toInt + size.toInt + 3 ∧
    (addClause L s.db s.memUsed src size).1.size ≤ 2 ^ 31 ∧
    AddClausePost (abs L s M fa sl) Ls size.toInt (if irr then 1 else 0)
      (abs L { s with
          db := (addClause L s.db s.memUsed src size).1,
          memUsed := (addClause L s.db s.memUsed src size).2.1,
          memFixed := if irr then (addClause L s.db s.memUsed src size).2.1 else s.memFixed,
          nLemmas := if irr then s.nLemmas else s.nLemmas + 1 } M fa sl,
        (addClause L s.db s.memUsed src size).2.2.toInt) := by
  obtain ⟨hw1, hw2⟩ := addClause_watches (M := M) (fa := fa) (sl := sl) hsz hsize hsrc hin hsrc_hi hsrc_le
    hheads hdistinct hu0 hmem hfirst hlits
  have h0 : ((0 : Cell)).toInt = 0 := rfl
  have h2 : ((2 : Cell)).toInt = 2 := rfl
  have h3 : ((3 : Cell)).toInt = 3 := rfl
  have hsz0 : 0 ≤ size.toInt := by omega
  have hus : (s.memUsed + size).toInt = s.memUsed.toInt + size.toInt := toInt_add (by omega) (by omega)
  have hus3 : (s.memUsed + size + 3).toInt = s.memUsed.toInt + size.toInt + 3 := by
    rw [toInt_add (by rw [hus, h3]; omega) (by rw [hus, h3]; omega), hus, h3]
  have hcl : (s.memUsed + 2).toInt = s.memUsed.toInt + 2 := by
    rw [toInt_add (by rw [h2]; omega) (by rw [h2]; omega), h2]
  have hcls : (s.memUsed + 2 + size).toInt = s.memUsed.toInt + 2 + size.toInt := by
    rw [toInt_add (by rw [hcl]; omega) (by rw [hcl]; omega), hcl]
  have hnot : ¬ (s.memUsed + size + 3 > memMax) := fun h => by
    have := Int32.lt_iff_toInt_lt.mp h; rw [hus3, memMax_toInt] at this; omega
  unfold addClause
  rw [if_neg hnot]
  dsimp only
  generalize hdb1 : (if size > 1 then
      addWatch L (addWatch L s.db (ld s.db src) s.memUsed) (ld (addWatch L s.db (ld s.db src) s.memUsed) (src + 1))
        (s.memUsed + 1) else s.db) = db1 at hw1 hw2
  -- cell facts, as reads of the arrays
  have w2 : ∀ q, 0 ≤ q → ldA (toDB db1) q = afterWatches (abs L s M fa sl) Ls q := hw2
  have hsep : src.toInt + size.toInt ≤ (s.memUsed + 2).toInt ∨ (s.memUsed + 2).toInt ≤ src.toInt := by
    rw [hcl]; omega
  obtain ⟨c1, c2, c3⟩ := copyLoop_spec (dst := s.memUsed + 2) (src := src) (size := size)
    (by rw [hcl]; omega) hin (by rw [hcl]; omega) (by omega) hsep _ ({ (default : solver) with DB := toDB db1 } : solver)
    db1 0 rfl rfl hw1 (by rw [h0]; omega) (by rw [h0]; omega)
  rw [h0] at c2 c3
  simp only [Int.add_zero] at c3
  generalize hdb2 : copyLoop db1 (s.memUsed + 2) src 0 size = db2 at c1 c2 c3
  have cp : ∀ j, 0 ≤ j → j < size.toInt → ldA (toDB db2) ((s.memUsed + 2).toInt + j) = ldA (toDB db1) (src.toInt + j) :=
    fun j a b => c2 j a b
  have un : ∀ q, 0 ≤ q → (q < (s.memUsed + 2).toInt ∨ (s.memUsed + 2).toInt + size.toInt ≤ q) →
      ldA (toDB db2) q = ldA (toDB db1) q := fun q a b => c3 q a b
  obtain ⟨t1, t2⟩ := st_sim ({ (default : solver) with DB := toDB db2 } : solver) rfl c1 (s.memUsed + 2 + size) 0
  have tm : ∀ q, 0 ≤ q → ldA (toDB (st db2 (s.memUsed + 2 + size) 0)) q =
      if q = s.memUsed.toInt + 2 + size.toInt then 0 else ldA (toDB db2) q := fun q hq => by
    rw [← t1, hcls, h0]
    exact ld_st _ _ (by omega) hq
  rw [hcl] at cp un
  -- cells outside the record are those after the watch writes
  have hout : ∀ q, 0 ≤ q → (q < s.memUsed.toInt + 2 ∨ s.memUsed.toInt + 2 + size.toInt < q) →
      ldA (toDB (st db2 (s.memUsed + 2 + size) 0)) q = afterWatches (abs L s M fa sl) Ls q := fun q hq hq' => by
    rw [tm q hq, if_neg (by omega), un q hq (by omega), w2 q hq]
  -- `afterWatches` is the old memory on the source and above the record
  have keep : ∀ q, 0 ≤ q → s.memUsed.toInt + 1 < q →
      afterWatches (abs L s M fa sl) Ls q = (abs L s M fa sl).ld q := fun q hq hgt => by
    unfold afterWatches
    split
    · rename_i hl
      obtain ⟨_, a1, _⟩ := hheads hl 0 (by omega)
      obtain ⟨_, b1, _⟩ := hheads hl 1 (by omega)
      show (if q = s.memUsed.toInt then _ else if q = L.first.toInt + Ls[0]! then _ else
        if q = s.memUsed.toInt + 1 then _ else if q = L.first.toInt + Ls[1]! then _ else _) = _
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rfl
  refine ⟨hcl, hus3, t2, ⟨by rw [hcl]; rfl, ?_, fun i hi => ?_, ?_, fun q hq hlt => ?_, fun q hlt => ?_, ?_⟩⟩
  · show (s.memUsed + size + 3).toInt = _; rw [hus3]; rfl
  · -- the record holds `Ls`
    rw [ld_eq_ldA, hcl]
    show ldA (toDB (st db2 (s.memUsed + 2 + size) 0)) _ = _
    rw [tm _ (by omega), if_neg (by omega), cp i (by omega) (by omega), w2 _ (by omega), ← hsrc i hi]
    unfold afterWatches
    split
    · rename_i hl
      obtain ⟨_, a1, a2⟩ := hheads hl 0 (by omega)
      obtain ⟨_, b1, b2⟩ := hheads hl 1 (by omega)
      show (if _ = s.memUsed.toInt then _ else if _ = L.first.toInt + Ls[0]! then _ else
        if _ = s.memUsed.toInt + 1 then _ else if _ = L.first.toInt + Ls[1]! then _ else _) = _
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rfl
  · rw [ld_eq_ldA, hcl]
    show ldA (toDB (st db2 (s.memUsed + 2 + size) 0)) _ = _
    rw [tm _ (by omega), if_pos rfl]
  · rw [hcl] at hlt; rw [ld_eq_ldA]; exact hout q hq (Or.inl hlt)
  · rw [hcl] at hlt; rw [ld_eq_ldA]
    show ldA (toDB (st db2 (s.memUsed + 2 + size) 0)) q = _
    rw [hout q (by omega) (Or.inr hlt), keep q (by omega) (by omega)]
  · exact ⟨_, abs_added _ irr hus3 hcnt⟩

end MicrosatLean.Fast.Verification
