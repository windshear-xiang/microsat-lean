import MicrosatLean.Faithful.Verification.Database
import MicrosatLean.Faithful.Verification.Memory

/-!
# Which cells each part of the database depends on

A clause record depends only on its literal cells and terminator; a watch list
only on its head cell and its link cells. These frame lemmas let every C function's
proof say "these cells did not change, so this part of the invariant still holds".
-/

namespace MicrosatLean.Faithful.Verification

/-- A record's literals and terminator: the cells `ClauseAt` reads. -/
def RecordCell (r : Record) (q : CInt) : Prop := r.1 ≤ q ∧ q ≤ r.1 + r.2.length

/-- `ClauseAt` survives any change that keeps the record's cells. -/
theorem ClauseAt.frame {S T : solver} {c : Ptr} {lits : List CInt} (h : ClauseAt S c lits)
    (same : ∀ q, c ≤ q → q ≤ c + lits.length → T.ld q = S.ld q) : ClauseAt T c lits := by
  refine ⟨fun i hi => ?_, ?_⟩
  · rw [same _ (by omega) (by omega)]; exact h.1 i hi
  · rw [same _ (by omega) (by omega)]; exact h.2

/-- Records tiling `[a, b)` lie inside `[a, b)`, each at least 3 cells long. -/
theorem Tiling.bounds {S : solver} {a b : Ptr} {rs : List Record} (h : Tiling S a b rs) :
    a ≤ b ∧ ∀ r ∈ rs, a + 2 ≤ r.1 ∧ r.1 + r.2.length < b := by
  induction h with
  | nil p => simp
  | cons hc ht ih =>
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp; omega
    · have := ih.2 r hr; omega

/-- A tiling survives any change that keeps every record's cells. Used by every
function that writes outside the clause literals (watches, trail, flags). -/
theorem Tiling.frame {S T : solver} {a b : Ptr} {rs : List Record} (h : Tiling S a b rs)
    (same : ∀ r ∈ rs, ∀ q, RecordCell r q → T.ld q = S.ld q) : Tiling T a b rs := by
  induction h with
  | nil p => exact .nil p
  | @cons p q lits rest hc ht ih =>
    refine .cons (hc.frame fun x h1 h2 => same (p + 2, lits) (by simp) x ⟨h1, h2⟩) (ih ?_)
    intro r hr x hx
    exact same r (by simp [hr]) x hx

/-- Appending a record at the end of a tiling (as `addClause` does at `mem_used`). -/
theorem Tiling.append {S : solver} {a b : Ptr} {rs : List Record} {lits : List CInt}
    (h : Tiling S a b rs) (hc : ClauseAt S (b + 2) lits) :
    Tiling S a (b + 3 + lits.length) (rs ++ [(b + 2, lits)]) := by
  induction h with
  | nil p => exact .cons hc (.nil _)
  | cons hc' _ ih => exact .cons hc' (ih hc)

/-- A watch list survives any change that keeps its head cell and its link cells. -/
theorem ListFrom.frame {S T : solver} {head : Ptr} {links : List Ptr} (h : ListFrom S head links)
    (same : ∀ q, (q = head ∨ q ∈ links) → T.ld q = S.ld q) : ListFrom T head links := by
  induction links generalizing head with
  | nil => simp only [ListFrom] at h ⊢; rw [same head (Or.inl rfl)]; exact h
  | cons x xs ih =>
    simp only [ListFrom] at h ⊢
    refine ⟨by rw [same head (Or.inl rfl)]; exact h.1, ih h.2 ?_⟩
    intro q hq
    rcases hq with rfl | hq
    · exact same _ (Or.inr (by simp))
    · exact same _ (Or.inr (by simp [hq]))

/-- Pushing `link` onto the front of the list at `head`: once `DB[link]` holds the old
head value and `head` holds `link`, the list is `link :: links` (C:49–50, `addWatch`). -/
theorem ListFrom.push {S T : solver} {head link : Ptr} {links : List Ptr}
    (h : ListFrom S head links) (hhead : T.ld head = link) (hlink : T.ld link = S.ld head)
    (same : ∀ q ∈ links, T.ld q = S.ld q) : ListFrom T head (link :: links) := by
  refine ⟨hhead, ?_⟩
  cases links with
  | nil => simp only [ListFrom] at h ⊢; rw [hlink, h]
  | cons x xs =>
    simp only [ListFrom] at h ⊢
    refine ⟨by rw [hlink, h.1], h.2.frame fun q hq => ?_⟩
    rcases hq with rfl | hq
    · exact same q (by simp)
    · exact same q (by simp [hq])

/-- Link cells watching `lit` after appending record `r`: the old ones, and `r`'s link 0
or link 1 if it watches `lit` (C:62–63). -/
theorem watches_append (rs : List Record) (r : Record) (lit link : CInt) (flip : Ptr → Bool := fun _ => false) :
    Watches (rs ++ [r]) lit link flip ↔ Watches rs lit link flip ∨
      (2 ≤ r.2.length ∧ ((link = r.1 - 2 ∧ r.2[if flip r.1 then 1 else 0]? = some lit) ∨
        (link = r.1 - 1 ∧ r.2[if flip r.1 then 0 else 1]? = some lit))) := by
  unfold Watches
  constructor
  · rintro ⟨r', hr', h⟩
    rcases List.mem_append.mp hr' with hr' | hr'
    · exact Or.inl ⟨r', hr', h⟩
    · simp only [List.mem_singleton] at hr'; subst hr'; exact Or.inr h
  · rintro (⟨r', hr', h⟩ | h)
    · exact ⟨r', List.mem_append_left _ hr', h⟩
    · exact ⟨r, List.mem_append_right _ (by simp), h⟩

/-- Watching depends on the orientation of the listed records only. -/
theorem Watches.congr_flip {rs : List Record} {f g : Ptr → Bool} (h : ∀ r ∈ rs, f r.1 = g r.1)
    {lit link : CInt} : Watches rs lit link f ↔ Watches rs lit link g := by
  constructor
  · rintro ⟨r, hr, h2, hw⟩; exact ⟨r, hr, h2, by rw [← h r hr]; exact hw⟩
  · rintro ⟨r, hr, h2, hw⟩; exact ⟨r, hr, h2, by rw [h r hr]; exact hw⟩

/-- The records of an input-only database. -/
@[simp] theorem records_all_inputs (rs : List Record) (f : Ptr → Bool) :
    (⟨rs, [], f⟩ : Records).all = rs := by
  simp [Records.all]

end MicrosatLean.Faithful.Verification
