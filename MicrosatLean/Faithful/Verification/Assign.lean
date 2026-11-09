import MicrosatLean.Faithful.Microsat
import MicrosatLean.Faithful.Verification.Memory

/-!
# `assign` and `unassign` (C:36, C:42–47)

`assign S c forced` makes `lit = c[0]` true: it tags `false[-lit]`, pushes `-lit` on
the trail, and records the reason `1 + c` and the model value. Nothing else changes.
-/

namespace MicrosatLean.Faithful.Verification

/-- `assign` as its five memory writes and the `assigned` increment. -/
theorem assign_eq (S : solver) (c : Ptr) (forced : CInt) :
    assign S c forced =
      ((({ (S.st (S.false + -S.ld c) (if forced != 0 then IMPLIED else 1)).st S.assigned (-S.ld c)
          with assigned := S.assigned + 1 } : solver).st (S.reason + abs (S.ld c)) (1 + c)).st
        (S.model + abs (S.ld c)) (if S.ld c > 0 then 1 else 0)) := by
  simp [assign]

/-- The cells after `assign` (C:44–47), for nonnegative pointers. -/
theorem assign_ld (S : solver) (c : Ptr) (forced : CInt) {q : CInt} (hq : 0 ≤ q)
    (hf : 0 ≤ S.false + -S.ld c) (ha : 0 ≤ S.assigned) (hr : 0 ≤ S.reason + abs (S.ld c))
    (hm : 0 ≤ S.model + abs (S.ld c)) :
    (assign S c forced).ld q =
      if q = S.model + abs (S.ld c) then (if S.ld c > 0 then 1 else 0)
      else if q = S.reason + abs (S.ld c) then 1 + c
      else if q = S.assigned then -S.ld c
      else if q = S.false + -S.ld c then (if forced != 0 then IMPLIED else 1)
      else S.ld q := by
  rw [assign_eq, ld_st _ _ hm hq, ld_st _ _ hr hq]
  have keep : ∀ (X : solver) (x : CInt), ({ X with assigned := x } : solver).ld q = X.ld q :=
    fun _ _ => rfl
  rw [keep, ld_st _ _ ha hq, ld_st _ _ hf hq]

/-- Fields after `assign`: only `DB` and `assigned` change. -/
theorem assign_fields (S : solver) (c : Ptr) (forced : CInt) :
    ∃ DB, assign S c forced = { S with DB := DB, assigned := S.assigned + 1 } := by
  rw [assign_eq]
  exact ⟨_, by apply solver.ext <;> first | rfl | simp⟩

/-- `unassign` clears one flag (C:36). -/
theorem unassign_eq (S : solver) (lit : CInt) : unassign S lit = S.st (S.false + lit) 0 := rfl

end MicrosatLean.Faithful.Verification
