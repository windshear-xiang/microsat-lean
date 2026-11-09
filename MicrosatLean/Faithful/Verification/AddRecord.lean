import MicrosatLean.Faithful.Verification.AddClause
import MicrosatLean.Faithful.Verification.Lists

/-!
# Appending a record with `addClause`

`addClause` (C:59–66) puts the new record at `mem_used` and pushes its two watches on
the lists of its first two literals. These lemmas give the watch lists and the clause
database afterwards; `analyze` and `reduceDB` use them.
-/

namespace MicrosatLean.Faithful.Verification

/-- `addClause` keeps the array pointers. -/
theorem AddClausePost.shape {S0 : solver} {L : List CInt} {size irr : CInt} {r : solver × Ptr}
    (post : AddClausePost S0 L size irr r) : SameShape S0 r.1 := by
  obtain ⟨DB, h⟩ := post.2.2.2.2.2.2
  rw [h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Cells below the new record other than its link cells and the two list heads are
unchanged. -/
theorem AddClausePost.below {S0 : solver} {L : List CInt} {size irr : CInt} {r : solver × Ptr}
    (post : AddClausePost S0 L size irr r) {q : CInt} (hq : 0 ≤ q) (hu : q < S0.mem_used)
    (hh : 1 < L.length → q ≠ S0.first + L[0]! ∧ q ≠ S0.first + L[1]!) : r.1.ld q = S0.ld q := by
  rw [post.2.2.2.2.1 q hq (by rw [post.1]; omega)]
  unfold afterWatches
  split
  · rename_i hl
    obtain ⟨n0, n1⟩ := hh hl
    simp only
    rw [if_neg (by omega), if_neg n0, if_neg (by omega), if_neg n1]
  · rfl

/-- The first two literals of a record, as `getElem!`. -/
theorem first_two {L : List CInt} (hl : 1 < L.length) (hnd : L.Nodup) :
    L[0]! ∈ L ∧ L[1]! ∈ L ∧ L[0]! ≠ L[1]! ∧ L[0]? = some L[0]! ∧ L[1]? = some L[1]! := by
  rw [getElem!_pos L 0 (by omega), getElem!_pos L 1 (by omega)]
  exact ⟨List.getElem_mem _, List.getElem_mem _,
    (List.pairwise_iff_getElem.mp hnd) 0 1 (by omega) (by omega) (by omega),
    List.getElem?_eq_getElem _, List.getElem?_eq_getElem _⟩

/-- The watch lists after `addClause` appends the record `(mem_used + 2, L)`: its link 0
heads `L[0]`'s list and its link 1 heads `L[1]`'s (C:62–63); other lists are kept. -/
theorem WatchLists.addClause {S0 : solver} {db db' : Records} {L : List CInt} {size irr : CInt}
    {r : solver × Ptr} (h : WatchLists S0 db) (hl : Layout S0)
    (hrec : ∀ s ∈ db.all, clausesAt S0.nVars + 2 ≤ s.1 ∧ s.1 + s.2.length < S0.mem_used)
    (hu : clausesAt S0.nVars ≤ S0.mem_used)
    (post : AddClausePost S0 L size irr r) (hall : db'.all = db.all ++ [(S0.mem_used + 2, L)])
    (hf0 : db'.flip (S0.mem_used + 2) = false) (hf : ∀ s ∈ db.all, db'.flip s.1 = db.flip s.1)
    (hlit : ∀ x ∈ L, InRange S0.nVars x) (hnd : L.Nodup) : WatchLists r.1 db' := by
  have hs := post.shape
  have hn := hl.num
  have hn1 := hl.nVars_pos
  have hu' : 10 * S0.nVars + 8 ≤ S0.mem_used := by simp only [clausesAt] at hu; exact hu
  intro lit hlitr
  rw [hs.nVars] at hlitr
  obtain ⟨links, hlf, hlnd, hmem⟩ := h lit hlitr
  have hr := inRange_iff.mp hlitr
  have hlinks : ∀ q ∈ links, clausesAt S0.nVars ≤ q ∧ q < S0.mem_used := by
    intro q hq
    obtain ⟨s, hs', -, hw⟩ := (hmem q).1 hq
    have := hrec s hs'
    rcases hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  have hL : 1 < L.length → (-S0.nVars ≤ L[0]! ∧ L[0]! ≤ S0.nVars) ∧ (-S0.nVars ≤ L[1]! ∧ L[1]! ≤ S0.nVars) :=
    fun hl2 => by
      obtain ⟨m0, m1, -⟩ := first_two hl2 hnd
      have a := inRange_iff.mp (hlit _ m0); have b := inRange_iff.mp (hlit _ m1)
      exact ⟨⟨a.2.1, a.2.2⟩, ⟨b.2.1, b.2.2⟩⟩
  have hsameL : ∀ q ∈ links, r.1.ld q = S0.ld q := fun q hq => by
    have := hlinks q hq
    refine post.below (by simp only [clausesAt] at this; omega) this.2 fun hl2 => ?_
    have := hL hl2; simp only [clausesAt] at *; omega
  have hcell : ∀ q, 0 ≤ q → q < S0.mem_used + 2 → r.1.ld q = afterWatches S0 L q := fun q h0 h1 =>
    post.2.2.2.2.1 q h0 (by rw [post.1]; exact h1)
  have hfirst : 0 ≤ S0.first + lit ∧ S0.first + lit < S0.mem_used := by simp only [clausesAt] at hu; omega
  rw [hs.first, hall]
  have hw : ∀ link, Watches (db.all ++ [(S0.mem_used + 2, L)]) lit link db'.flip ↔
      Watches db.all lit link db.flip ∨
      (1 < L.length ∧ ((link = S0.mem_used ∧ L[0]! = lit) ∨ (link = S0.mem_used + 1 ∧ L[1]! = lit))) := by
    intro link
    rw [watches_append (flip := db'.flip), Watches.congr_flip hf]
    dsimp only
    rw [hf0]
    simp only [Bool.false_eq_true, ite_false]
    refine or_congr Iff.rfl ⟨fun ⟨h2, hx⟩ => ⟨by omega, ?_⟩, fun ⟨h2, hx⟩ => ⟨by omega, ?_⟩⟩
    · obtain ⟨-, -, -, g0, g1⟩ := first_two (show 1 < L.length by omega) hnd
      rcases hx with ⟨e, hx⟩ | ⟨e, hx⟩
      · rw [g0] at hx; exact Or.inl ⟨by omega, Option.some.inj hx⟩
      · rw [g1] at hx; exact Or.inr ⟨by omega, Option.some.inj hx⟩
    · obtain ⟨-, -, -, g0, g1⟩ := first_two h2 hnd
      rcases hx with ⟨e, hx⟩ | ⟨e, hx⟩
      · exact Or.inl ⟨by omega, by rw [g0, hx]⟩
      · exact Or.inr ⟨by omega, by rw [g1, hx]⟩
  have hnotin : ∀ x, S0.mem_used ≤ x → x ∉ links := fun x hx hm => by have := hlinks x hm; omega
  by_cases c0 : 1 < L.length ∧ L[0]! = lit
  · obtain ⟨-, -, hne, -⟩ := first_two c0.1 hnd
    have h0 := hL c0.1
    refine ⟨S0.mem_used :: links, hlf.push ?_ ?_ hsameL, List.nodup_cons.mpr ⟨hnotin _ (by omega), hlnd⟩,
      fun link => ?_⟩
    · rw [hcell _ hfirst.1 (by omega)]; unfold afterWatches
      simp only [c0.1, if_true]; rw [if_neg (by omega), if_pos (by rw [c0.2])]
    · rw [hcell _ (by omega) (by omega)]; unfold afterWatches
      simp only [c0.1, if_true]; rw [c0.2]
    · rw [hw, List.mem_cons, hmem]
      constructor
      · rintro (rfl | hm)
        · exact Or.inr ⟨c0.1, Or.inl ⟨rfl, c0.2⟩⟩
        · exact Or.inl hm
      · rintro (hm | ⟨-, ⟨e, -⟩ | ⟨-, e⟩⟩)
        · exact Or.inr hm
        · exact Or.inl e
        · exact absurd (e.trans c0.2.symm) (Ne.symm hne)
  · by_cases c1 : 1 < L.length ∧ L[1]! = lit
    · obtain ⟨-, -, hne, -⟩ := first_two c1.1 hnd
      have h0 := hL c1.1
      refine ⟨(S0.mem_used + 1) :: links, hlf.push ?_ ?_ hsameL,
        List.nodup_cons.mpr ⟨hnotin _ (by omega), hlnd⟩, fun link => ?_⟩
      · rw [hcell _ hfirst.1 (by omega)]; unfold afterWatches
        simp only [c1.1, if_true]
        rw [if_neg (by omega), if_neg (by rw [← c1.2]; omega), if_neg (by omega), if_pos (by rw [c1.2])]
      · rw [hcell _ (by omega) (by omega)]; unfold afterWatches
        simp only [c1.1, if_true]; rw [if_neg (by omega), if_neg (by omega), c1.2]
      · rw [hw, List.mem_cons, hmem]
        constructor
        · rintro (rfl | hm)
          · exact Or.inr ⟨c1.1, Or.inr ⟨rfl, c1.2⟩⟩
          · exact Or.inl hm
        · rintro (hm | ⟨-, ⟨-, e⟩ | ⟨e, -⟩⟩)
          · exact Or.inr hm
          · exact absurd (e.trans c1.2.symm) hne
          · exact Or.inl e
    · refine ⟨links, hlf.frame fun q hq => ?_, hlnd, fun link => ?_⟩
      · rcases hq with rfl | hq
        · refine post.below hfirst.1 hfirst.2 fun hl2 => ⟨fun he => c0 ⟨hl2, ?_⟩, fun he => c1 ⟨hl2, ?_⟩⟩
          · have := hL hl2; omega
          · have := hL hl2; omega
        · exact hsameL q hq
      · rw [hw, hmem]
        constructor
        · exact Or.inl
        · rintro (hm | ⟨hl2, ⟨-, e⟩ | ⟨-, e⟩⟩)
          · exact hm
          · exact absurd ⟨hl2, e⟩ c0
          · exact absurd ⟨hl2, e⟩ c1

/-- The database after `addClause` appends a learned lemma `L` (C:65, `irr = 0`): one more
lemma record at the end. The lemma must be a new, entailed clause over distinct variables. -/
theorem Database.addLemma {input : Input} {S0 : solver} {db : Records} {L : List CInt} {size : CInt}
    {r : solver × Ptr} (f : Ptr → Bool) (h : Database input S0 db) (hl : Layout S0)
    (post : AddClausePost S0 L size 0 r) (hsize : size = L.length) (hin : db.inputs ≠ [])
    (shape : L ≠ [] ∧ (L.map Int.natAbs).Nodup ∧ ∀ l ∈ L, InRange S0.nVars l)
    (entailed : input.Entails L) (new : ∀ s ∈ db.lemmas, ¬ s.2.Perm L) :
    Database input r.1 ⟨db.inputs, db.lemmas ++ [(S0.mem_used + 2, L)], f⟩ := by
  have hs := post.shape
  obtain ⟨hr2, hmu, hlits, hterm, -, -, DB, hr1⟩ := id post
  have hn := hl.num
  have hn1 := hl.nVars_pos
  have hfix : r.1.mem_fixed = S0.mem_fixed := by rw [hr1]; rfl
  have hnl : r.1.nLemmas = S0.nLemmas + 1 := by rw [hr1]; rfl
  have hstart : lemmasStart r.1 ⟨db.inputs, db.lemmas ++ [(S0.mem_used + 2, L)], f⟩ = lemmasStart S0 db := by
    simp only [lemmasStart, hin, if_false, hfix]
  have hb1 := h.inputs_tile.bounds
  have hb2 := h.lemmas_tile.bounds
  have hu : clausesAt S0.nVars ≤ S0.mem_used := by omega
  have same : ∀ s ∈ db.all, ∀ q, RecordCell s q → r.1.ld q = S0.ld q := by
    intro s hs' q hq
    have := h.record_ge hs'
    simp only [RecordCell] at hq
    refine post.below (by simp only [clausesAt] at this; omega) (by omega) fun hl2 => ?_
    have hlit0 := inRange_iff.mp (shape.2.2 _ (first_two hl2 (List.Pairwise.of_map Int.natAbs
      (fun a b hab he => hab (by rw [he])) shape.2.1)).1)
    have hlit1 := inRange_iff.mp (shape.2.2 _ (first_two hl2 (List.Pairwise.of_map Int.natAbs
      (fun a b hab he => hab (by rw [he])) shape.2.1)).2.1)
    simp only [clausesAt] at this; omega
  have hclause : ClauseAt r.1 (S0.mem_used + 2) L := by
    refine ⟨fun i hi => ?_, ?_⟩
    · rw [← hr2]; exact hlits i hi
    · rw [← hr2, ← hsize]; exact hterm
  refine ⟨?_, ?_, h.inputs_length, h.inputs_perm, h.inputs_nonempty, fun hnil => absurd hnil hin, ?_, ?_, ?_, ?_⟩
  · rw [hstart, hs.nVars]
    exact h.inputs_tile.frame fun s hs' => same s (List.mem_append_left _ hs')
  · rw [hstart, hmu, hsize, show S0.mem_used + (L.length : CInt) + 3 = S0.mem_used + 3 + L.length by omega]
    exact (h.lemmas_tile.frame fun s hs' => same s (List.mem_append_right _ hs')).append hclause
  · rw [hnl, h.nLemmas]; simp
  · intro s hs'
    rw [hs.nVars]
    rcases List.mem_append.mp hs' with hs' | hs'
    · exact h.lemma_shape s hs'
    · simp only [List.mem_singleton] at hs'; subst hs'; exact shape
  · intro s hs'
    rcases List.mem_append.mp hs' with hs' | hs'
    · exact h.lemma_entailed s hs'
    · simp only [List.mem_singleton] at hs'; subst hs'; exact entailed
  · refine List.pairwise_append.mpr ⟨h.lemma_distinct, List.pairwise_singleton _ _, fun a ha b hb => ?_⟩
    simp only [List.mem_singleton] at hb; subst hb; exact new a ha

end MicrosatLean.Faithful.Verification
