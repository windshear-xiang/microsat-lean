import MicrosatLean.Faithful.Verification.Trail

/-!
# The decision order: `head`, `prev`, `next`

The variables form a doubly linked list (C:206–210): `prev` from `head` visits every
variable and ends at 0; `next` links back. `bump` moves a variable to the head
(C:85–91) and the decision scan walks `prev` from a cursor (C:173–174).
-/

namespace MicrosatLean.Faithful.Verification

/-- The variables `1 … n`. -/
def vars (n : CInt) : List CInt := List.map (fun i : Nat => (i : CInt) + 1) (List.range n.toNat)

/-- Membership in `vars N`: the variables `1 … N`. -/
theorem mem_vars {N v : CInt} : v ∈ vars N ↔ 1 ≤ v ∧ v ≤ N := by
  simp only [vars, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, rfl⟩; omega
  · intro h; exact ⟨(v - 1).toNat, by omega, by omega⟩

/-- Starting at `v` and following `prev` visits `vs` in order, then reaches 0. -/
def PrevChain (S : solver) : CInt → List CInt → Prop
  | v, [] => v = 0
  | v, w :: ws => v = w ∧ PrevChain S (S.ld (S.prev + w)) ws

/-- A `prev` chain depends only on the `prev` cells. -/
theorem PrevChain.congr {S T : solver} {v : CInt} {vs : List CInt} (h : PrevChain S v vs)
    (same : ∀ w ∈ vs, T.ld (T.prev + w) = S.ld (S.prev + w)) : PrevChain T v vs := by
  induction vs generalizing v with
  | nil => exact h
  | cons w ws ih =>
    refine ⟨h.1, ?_⟩
    rw [same w (by simp)]
    exact ih h.2 fun x hx => same x (by simp [hx])

/-- Variable `v` is assigned: one of its literals is on the trail. -/
def Assigned (S : solver) (v : CInt) : Prop :=
  ∃ i < trailLen S, abs (trailAt S i) = v

/-- `vs` is the decision order: a `prev` chain from `head` through every variable,
with `next` as its inverse (`next[0]` is the last variable). -/
structure OrderList (S : solver) (vs : List CInt) : Prop where
  chain : PrevChain S S.head vs
  perm : vs.Perm (vars S.nVars)
  next_back : ∀ i (h : i + 1 < vs.length), S.ld (S.next + vs[i + 1]) = vs[i]
  next_zero : S.ld (S.next + 0) = vs.getLast?.getD 0

/-- The decision cursor of `solve` (C:161) is in the order list, or 0 past its end,
and every variable before it is assigned. Used to show that `decision == 0`
(C:175) means every variable is assigned. -/
def Cursor (S : solver) (vs : List CInt) (decision : CInt) : Prop :=
  ∃ k ≤ vs.length, vs[k]?.getD 0 = decision ∧ ∀ j (h : j < vs.length), j < k → Assigned S vs[j]

end MicrosatLean.Faithful.Verification
