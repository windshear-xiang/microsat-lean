import MicrosatLean.Faithful.Verification.Regions

/-!
# Walking and editing watch lists

`propagate` (C:139–152) and `reduceDB` (C:73–77) walk a watch list with a cursor `watch`,
the cell holding the next link, and unlink the next link with `*watch = DB[*watch]`.
`Path` is the part of a list before the cursor.
-/

namespace MicrosatLean.Faithful.Verification

/-- Following links from cell `a` through `xs` reaches cell `b`. -/
def Path (S : solver) : Ptr → List Ptr → Ptr → Prop
  | a, [], b => a = b
  | a, x :: xs, b => S.ld a = x ∧ Path S x xs b

/-- A watch list split at a cursor: the visited part, then the rest from the cursor. -/
theorem listFrom_append {S : solver} {a : Ptr} {xs ys : List Ptr} :
    ListFrom S a (xs ++ ys) ↔ ∃ b, Path S a xs b ∧ ListFrom S b ys := by
  induction xs generalizing a with
  | nil => simp [Path]
  | cons x xs ih =>
    simp only [List.cons_append, ListFrom, Path, ih]
    exact ⟨fun ⟨h1, b, h2, h3⟩ => ⟨b, ⟨h1, h2⟩, h3⟩, fun ⟨b, ⟨h1, h2⟩, h3⟩ => ⟨h1, b, h2, h3⟩⟩

/-- A list of nonnegative links ending at `END` is determined by its start. -/
theorem ListFrom.unique {S : solver} {w : Ptr} {l1 l2 : List Ptr} (h1 : ListFrom S w l1)
    (h2 : ListFrom S w l2) (p1 : ∀ q ∈ l1, 0 ≤ q) (p2 : ∀ q ∈ l2, 0 ≤ q) : l1 = l2 := by
  induction l1 generalizing w l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons y ys =>
      simp only [ListFrom] at h1 h2
      have := p2 y (by simp); rw [h1] at h2; have := h2.1; simp [END] at this; omega
  | cons x xs ih =>
    cases l2 with
    | nil =>
      simp only [ListFrom] at h1 h2
      have := p1 x (by simp); rw [h2] at h1; have := h1.1; simp [END] at this; omega
    | cons y ys =>
      simp only [ListFrom] at h1 h2
      have hxy : x = y := by rw [← h1.1, ← h2.1]
      subst hxy
      rw [ih h1.2 h2.2 (fun q hq => p1 q (by simp [hq])) (fun q hq => p2 q (by simp [hq]))]

/-- The links after cell `w` (the measure of a list walk). -/
noncomputable def linksAfter (S : solver) (w : Ptr) : List Ptr :=
  open Classical in if h : ∃ l : List Ptr, ListFrom S w l ∧ ∀ q ∈ l, 0 ≤ q then Classical.choose h else []

theorem linksAfter_eq {S : solver} {w : Ptr} {l : List Ptr} (h : ListFrom S w l) (hl : ∀ q ∈ l, 0 ≤ q) :
    linksAfter S w = l := by
  have hex : ∃ l : List Ptr, ListFrom S w l ∧ ∀ q ∈ l, 0 ≤ q := ⟨l, h, hl⟩
  unfold linksAfter
  rw [dif_pos hex]
  exact (Classical.choose_spec hex).1.unique h (Classical.choose_spec hex).2 hl

/-- A path ends at its last link (or its start). -/
theorem Path.end_eq {S : solver} {a b : Ptr} {xs : List Ptr} (h : Path S a xs b) :
    b = (a :: xs).getLast (by simp) := by
  induction xs generalizing a with
  | nil => exact h.symm
  | cons x xs ih => rw [ih h.2]; simp

/-- A path only reads the cells before its end. -/
theorem Path.frame {S T : solver} {a b : Ptr} {xs : List Ptr} (h : Path S a xs b)
    (same : ∀ q, (q = a ∨ q ∈ xs) → q ≠ b → T.ld q = S.ld q) (hnd : (a :: xs).Nodup) : Path T a xs b := by
  induction xs generalizing a with
  | nil => exact h
  | cons x xs ih =>
    have hne : a ≠ b := by
      rw [h.2.end_eq]; intro he
      have : a ∈ x :: xs := by rw [he]; exact List.getLast_mem _
      exact (List.nodup_cons.mp hnd).1 this
    refine ⟨by rw [same a (Or.inl rfl) hne]; exact h.1, ih h.2 (fun q hq hqb => same q (by
      rcases hq with rfl | hq
      · exact Or.inr (by simp)
      · exact Or.inr (by simp [hq])) hqb) (List.nodup_cons.mp hnd).2⟩

/-- Extending a path by one link. -/
theorem Path.snoc {S : solver} {a b c : Ptr} {xs : List Ptr} (h : Path S a xs b) (hb : S.ld b = c) :
    Path S a (xs ++ [c]) c := by
  induction xs generalizing a with
  | nil => exact ⟨by rw [h]; exact hb, rfl⟩
  | cons x xs ih => exact ⟨h.1, ih h.2⟩

/-- The cells of a list: its head and its links. -/
theorem ListFrom.nodup_cells {S : solver} {head : Ptr} {links : List Ptr} (h : ListFrom S head links)
    (hnd : links.Nodup) (hhead : head ∉ links) : (head :: links).Nodup :=
  List.nodup_cons.mpr ⟨hhead, hnd⟩

/-- Unlinking the link after the cursor `w` (`*w = DB[*w]`, C:76, C:151). -/
theorem ListFrom.unlink {S T : solver} {w x : Ptr} {post : List Ptr} (h : ListFrom S w (x :: post))
    (hw : T.ld w = S.ld x) (same : ∀ q ∈ post, T.ld q = S.ld q) (hnd : (x :: post).Nodup) :
    ListFrom T w post := by
  cases post with
  | nil => simp only [ListFrom] at h ⊢; rw [hw, h.2]
  | cons y ys =>
    simp only [ListFrom] at h ⊢
    refine ⟨by rw [hw, h.2.1], h.2.2.frame fun q hq => ?_⟩
    rcases hq with rfl | hq
    · exact same _ (by simp)
    · exact same _ (by simp [hq])

/-- Records in a tiling are at least three cells apart. -/
theorem Tiling.sorted {S : solver} {a b : Ptr} {rs : List Record} (h : Tiling S a b rs) :
    rs.Pairwise (fun r s => r.1 + (r.2.length : CInt) + 3 ≤ s.1) := by
  induction h with
  | nil => exact List.Pairwise.nil
  | cons hc ht ih =>
    refine List.Pairwise.cons (fun s hs => ?_) ih
    have := ht.bounds.2 s hs; simp; omega

/-- Distinct records of the database are at least three cells apart. -/
theorem Database.apart {input : Input} {S : solver} {db : Records} (h : Database input S db)
    {r s : Record} (hr : r ∈ db.all) (hs : s ∈ db.all) (hne : r.1 ≠ s.1) :
    r.1 + (r.2.length : CInt) + 3 ≤ s.1 ∨ s.1 + (s.2.length : CInt) + 3 ≤ r.1 := by
  have h1 := h.inputs_tile.sorted
  have h2 := h.lemmas_tile.sorted
  have b1 := h.inputs_tile.bounds
  have b2 := h.lemmas_tile.bounds
  have hall : db.all.Pairwise (fun r s => r.1 + (r.2.length : CInt) + 3 ≤ s.1) := by
    unfold Records.all
    refine List.pairwise_append.mpr ⟨h1, h2, fun r hr s hs => ?_⟩
    have := b1.2 r hr; have := b2.2 s hs; omega
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exact Or.inl ((List.pairwise_iff_getElem.mp hall) i j hi hj hij)
  · exact absurd rfl hne
  · exact Or.inr ((List.pairwise_iff_getElem.mp hall) j i hj hi hij)

/-- Records of the database are determined by their position. -/
theorem Database.record_eq {input : Input} {S : solver} {db : Records} (h : Database input S db)
    {r s : Record} (hr : r ∈ db.all) (hs : s ∈ db.all) (he : r.1 = s.1) : r = s := by
  have hall : db.all.Pairwise (fun r s => r.1 + (r.2.length : CInt) + 3 ≤ s.1) := by
    unfold Records.all
    refine List.pairwise_append.mpr ⟨h.inputs_tile.sorted, h.lemmas_tile.sorted, fun r hr s hs => ?_⟩
    have := h.inputs_tile.bounds.2 r hr; have := h.lemmas_tile.bounds.2 s hs
    have := h.lemmas_tile.bounds.1; omega
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hs
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · have := (List.pairwise_iff_getElem.mp hall) i j hi hj hij; omega
  · rfl
  · have := (List.pairwise_iff_getElem.mp hall) j i hj hi hij; omega

/-- A link cell watches one literal only. -/
theorem Database.watches_unique {input : Input} {S : solver} {db : Records}
    (h : Database input S db) {L L' link : CInt} {f : Ptr → Bool}
    (hw : Watches db.all L link f) (hw' : Watches db.all L' link f) : L = L' := by
  obtain ⟨r, hr, h2, hr'⟩ := hw
  obtain ⟨s, hs, h2', hs'⟩ := hw'
  have key : ∀ (r s : Record), r ∈ db.all → s ∈ db.all → 2 ≤ r.2.length → 2 ≤ s.2.length →
      (link = r.1 - 2 ∨ link = r.1 - 1) → (link = s.1 - 2 ∨ link = s.1 - 1) → r.1 = s.1 := by
    intro r s hr hs _ _ e1 e2
    refine Classical.byContradiction fun hne => ?_
    rcases h.apart hr hs hne with h' | h' <;> omega
  have hrs : r = s := h.record_eq hr hs (key r s hr hs h2 h2'
    (by rcases hr' with ⟨e, _⟩ | ⟨e, _⟩ <;> omega) (by rcases hs' with ⟨e, _⟩ | ⟨e, _⟩ <;> omega))
  subst hrs
  rcases hr' with ⟨e1, g1⟩ | ⟨e1, g1⟩ <;> rcases hs' with ⟨e2, g2⟩ | ⟨e2, g2⟩
  · rw [g1] at g2; exact Option.some.inj g2
  · omega
  · omega
  · rw [g1] at g2; exact Option.some.inj g2

/-- A link cell is never a literal or terminator cell of a record. -/
theorem Database.link_not_record {input : Input} {S : solver} {db : Records} (h : Database input S db)
    {r : Record} (hr : r ∈ db.all) {q lit : CInt} {f : Ptr → Bool} (hq : RecordCell r q) :
    ¬ Watches db.all lit q f := by
  rintro ⟨s, hs, h2, hw⟩
  simp only [RecordCell] at hq
  by_cases he : r.1 = s.1
  · rcases hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  · rcases h.apart hr hs he with h' | h' <;> rcases hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega

/-- With an input record, a link watches an input record exactly when it lies below
`mem_fixed` (C:75). -/
theorem Database.watches_input_iff {input : Input} {S : solver} {db : Records} (h : Database input S db)
    (hin : db.inputs ≠ []) {lit link : CInt} {f : Ptr → Bool} (hw : Watches db.all lit link f) :
    Watches db.inputs lit link f ↔ link < S.mem_fixed := by
  have hst : lemmasStart S db = S.mem_fixed := by simp [lemmasStart, hin]
  have b1 := h.inputs_tile.bounds
  have b2 := h.lemmas_tile.bounds
  rw [← hst]
  constructor
  · rintro ⟨r, hr, -, hw'⟩
    have := b1.2 r hr
    rcases hw' with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  · intro hlt
    obtain ⟨r, hr, h2, hw'⟩ := hw
    rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, hr, h2, hw'⟩
    · have := b2.2 r hr
      rcases hw' with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega

/-- Where the `j`-th record of a tiling ending at `b` has its literals; `b + 2` past the end.
`reduceDB` walks the lemma records with this position (C:79, C:82). -/
def tilePos (rs : List Record) (b : Ptr) (j : Nat) : Ptr :=
  ((rs.drop j).head?.map (·.1)).getD (b + 2)

/-- Each record of a tiling holds its literals. -/
theorem Tiling.clauseAt {S : solver} {a b : Ptr} {rs : List Record} (h : Tiling S a b rs)
    {r : Record} (hr : r ∈ rs) : ClauseAt S r.1 r.2 := by
  induction h with
  | nil => simp at hr
  | cons hc _ ih =>
    rcases List.mem_cons.mp hr with rfl | hr
    · exact hc
    · exact ih hr

/-- The first record of a tiling starts at its start. -/
theorem Tiling.tilePos_zero {S : solver} {a b : Ptr} {rs : List Record} (h : Tiling S a b rs) :
    tilePos rs b 0 = a + 2 := by
  cases h with
  | nil => rfl
  | cons => rfl

/-- The record after record `j` starts three cells past its terminator. -/
theorem Tiling.tilePos_succ {S : solver} {a b : Ptr} {rs : List Record} (h : Tiling S a b rs)
    (j : Nat) (hj : j < rs.length) :
    tilePos rs b (j + 1) = rs[j].1 + rs[j].2.length + 3 ∧ tilePos rs b j = rs[j].1 := by
  induction h generalizing j with
  | nil => simp at hj
  | @cons p q lits rest hc ht ih =>
    cases j with
    | zero =>
      have := ht.tilePos_zero
      simp only [tilePos, List.drop_zero] at this
      constructor
      · show ((rest.head?.map (·.1)).getD (q + 2)) = _
        rw [this]; simp; omega
      · simp [tilePos]
    | succ j =>
      have := ih j (by simpa using hj)
      simpa [tilePos] using this

/-- Past the last record of a tiling. -/
theorem tilePos_length (rs : List Record) (b : Ptr) : tilePos rs b rs.length = b + 2 := by
  simp [tilePos]

end MicrosatLean.Faithful.Verification
