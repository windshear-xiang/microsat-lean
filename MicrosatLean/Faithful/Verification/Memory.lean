import MicrosatLean.Faithful.Memory

/-!
# Reading and writing `DB`

`S.ld p` (C's `*p`) and `S.st p v` (C's `*p = v`) behave like one zero-initialized
memory: a write changes exactly one cell, and nothing else in the solver. Every
proof about a C function uses these lemmas to track cells.
-/

namespace MicrosatLean.Faithful.Verification

open solver

-- Two solver states are equal when all their fields are; used to state which fields a
-- C function changes.
attribute [ext] MicrosatLean.Faithful.solver

/-- Reading a cell of the physical array, or 0 past its end (C's zeroed block, E1). -/
theorem ld_eq_getD (S : solver) {p : Int} (hp : 0 ≤ p) : S.ld p = S.DB.getD p.toNat 0 := by
  unfold ld
  rw [if_neg (Int.not_lt.mpr hp)]

/-- Storing to a nonnegative pointer: `set` inside the array, `growAndStore` past it. -/
theorem st_eq_dite (S : solver) {p : Int} (v : CInt) (hp : 0 ≤ p) :
    S.st p v = if h : p.toNat < S.DB.size then { S with DB := S.DB.set p.toNat v h }
      else { S with DB := growAndStore S.DB p.toNat v } := by
  unfold st
  rw [if_neg (Int.not_lt.mpr hp)]

/-- `panicWith` continues with its fallback value. -/
@[simp] theorem panicWith_eq {α : Type} (x : α) (msg : String) : panicWith x msg = x := rfl

/-- A store only replaces `DB` (a negative pointer panics and changes nothing). -/
theorem st_eq (S : solver) (p : Int) (v : CInt) : ∃ DB, S.st p v = { S with DB := DB } := by
  unfold st
  split
  · exact ⟨S.DB, by simp⟩
  · dsimp only
    split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- `growAndStore` writes `v` at `i` and keeps every other readable cell. -/
theorem getD_growAndStore (DB : Array CInt) {i j : Nat} (v : CInt) (hi : DB.size ≤ i) :
    (growAndStore DB i v).getD j 0 = if j = i then v else DB.getD j 0 := by
  unfold growAndStore
  have hsize : (DB ++ Array.replicate (i - DB.size) (0 : CInt)).size = i := by simp; omega
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push, hsize]
  by_cases hj : j = i
  · simp [hj]
  · simp only [hj, if_false]
    rw [Array.getElem?_append]
    by_cases hlt : j < DB.size
    · simp [hlt]
    · simp only [hlt, if_false]
      rw [Array.getElem?_replicate]
      have hnone : DB[j]? = none := Array.getElem?_eq_none (by omega)
      by_cases hk : j - DB.size < i - DB.size
      · simp [hk, hnone]
      · simp [hk, hnone]

/-- After `*p = v`, reading any cell `q`: `v` at `p`, the old value elsewhere. -/
theorem ld_st (S : solver) {p q : Int} (v : CInt) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    (S.st p v).ld q = if q = p then v else S.ld q := by
  have key : q.toNat = p.toNat ↔ q = p := by omega
  rw [st_eq_dite S v hp]
  split
  · rename_i h
    rw [ld_eq_getD _ hq, ld_eq_getD _ hq]
    simp only [Array.getD_eq_getD_getElem?, Array.getElem?_set]
    by_cases hqp : q = p
    · simp [hqp, h]
    · have : ¬ p.toNat = q.toNat := by omega
      simp [hqp, this]
  · rename_i h
    rw [ld_eq_getD _ hq, ld_eq_getD _ hq]
    show (growAndStore S.DB p.toNat v).getD q.toNat 0 = _
    rw [getD_growAndStore _ _ (by omega)]
    by_cases hqp : q = p
    · simp [hqp]
    · have : ¬ q.toNat = p.toNat := by omega
      simp [hqp, this]

/-- Reading the cell just written. -/
@[simp] theorem ld_st_self (S : solver) {p : Int} (v : CInt) (hp : 0 ≤ p) :
    (S.st p v).ld p = v := by
  simp [ld_st S v hp hp]

/-- A write leaves every other cell unchanged. -/
theorem ld_st_of_ne (S : solver) {p q : Int} (v : CInt) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hne : q ≠ p) : (S.st p v).ld q = S.ld q := by
  simp [ld_st S v hp hq, hne]

section fields
variable (S : solver) (p : Int) (v : CInt)

/-! A write changes no field other than `DB`. -/

@[simp] theorem st_nVars : (S.st p v).nVars = S.nVars := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_nClauses : (S.st p v).nClauses = S.nClauses := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_mem_used : (S.st p v).mem_used = S.mem_used := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_mem_fixed : (S.st p v).mem_fixed = S.mem_fixed := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_mem_max : (S.st p v).mem_max = S.mem_max := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_maxLemmas : (S.st p v).maxLemmas = S.maxLemmas := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_nLemmas : (S.st p v).nLemmas = S.nLemmas := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_buffer : (S.st p v).buffer = S.buffer := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_nConflicts : (S.st p v).nConflicts = S.nConflicts := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_model : (S.st p v).model = S.model := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_reason : (S.st p v).reason = S.reason := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_falseStack : (S.st p v).falseStack = S.falseStack := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_false : (S.st p v).false = S.false := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_first : (S.st p v).first = S.first := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_forced : (S.st p v).forced = S.forced := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_processed : (S.st p v).processed = S.processed := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_assigned : (S.st p v).assigned = S.assigned := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_next : (S.st p v).next = S.next := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_prev : (S.st p v).prev = S.prev := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_head : (S.st p v).head = S.head := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_res : (S.st p v).res = S.res := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_fast : (S.st p v).fast = S.fast := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]
@[simp] theorem st_slow : (S.st p v).slow = S.slow := by obtain ⟨_, h⟩ := st_eq S p v; rw [h]

end fields

end MicrosatLean.Faithful.Verification
