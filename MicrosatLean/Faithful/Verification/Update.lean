import MicrosatLean.Faithful.Verification.PropagateLoop

/-!
# Rewriting one record in place

Visiting a clause (C:139–151) reorders its literals and may cross its links. `Records.update`
replaces the record at clause pointer `c` by a reordering, with a new orientation; these
lemmas show the database facts survive.
-/

namespace MicrosatLean.Faithful.Verification

/-- Replace the literals of the record at `c` and set its orientation. -/
def Records.update (db : Records) (c : Ptr) (lits : List CInt) (fl : Bool) : Records where
  inputs := db.inputs.map fun r => if r.1 = c then (c, lits) else r
  lemmas := db.lemmas.map fun r => if r.1 = c then (c, lits) else r
  flip := fun p => if p = c then fl else db.flip p

theorem Records.update_all (db : Records) (c : Ptr) (lits : List CInt) (fl : Bool) :
    (db.update c lits fl).all = db.all.map fun r => if r.1 = c then (c, lits) else r := by
  simp [Records.update, Records.all]

/-- Updating a tiling: the record at `c` now holds `lits`, of the same length; the other
records keep their cells. -/
theorem Tiling.update {S T : solver} {a b c : Ptr} {rs : List Record} {lits : List CInt}
    (h : Tiling S a b rs) (hlen : ∀ r ∈ rs, r.1 = c → lits.length = r.2.length)
    (hc : ClauseAt T c lits)
    (same : ∀ r ∈ rs, r.1 ≠ c → ∀ q, RecordCell r q → T.ld q = S.ld q) :
    Tiling T a b (rs.map fun r => if r.1 = c then (c, lits) else r) := by
  induction h with
  | nil => exact .nil _
  | @cons p q l rest hcl ht ih =>
    simp only [List.map_cons]
    by_cases he : p + 2 = c
    · simp only [he, if_true]
      have hl := hlen (p + 2, l) (List.mem_cons_self) he
      have := Tiling.cons (S := T) (p := p) (lits := lits) (by rw [he]; exact hc)
        (by rw [hl]; exact ih (fun r hr => hlen r (by simp [hr])) (fun r hr => same r (by simp [hr])))
      rw [he] at this; exact this
    · simp only [he, if_false]
      exact .cons (hcl.frame fun q h1 h2 => same (p + 2, l) List.mem_cons_self he q ⟨h1, h2⟩)
        (ih (fun r hr => hlen r (by simp [hr])) (fun r hr => same r (by simp [hr])))

/-- The records of the database other than `r` sit elsewhere. -/
theorem Database.other_ne {input : Input} {S : solver} {db : Records} (h : Database input S db)
    {r s : Record} (hr : r ∈ db.all) (hs : s ∈ db.all) (hne : s ≠ r) : s.1 ≠ r.1 :=
  fun he => hne (h.record_eq hs hr he)

/-- The database after reordering the literals of record `r` (at `c`) in place. -/
theorem Database.update {input : Input} {S T : solver} {db : Records} {r : Record} {c : Ptr}
    {lits : List CInt} (fl : Bool) (h : Database input S db) (hr : r ∈ db.all) (hrc : r.1 = c)
    (hperm : lits.Perm r.2) (hc : ClauseAt T c lits)
    (hs : T.nVars = S.nVars ∧ T.mem_used = S.mem_used ∧ T.mem_fixed = S.mem_fixed ∧ T.nLemmas = S.nLemmas)
    (same : ∀ s ∈ db.all, s.1 ≠ c → ∀ q, RecordCell s q → T.ld q = S.ld q) :
    Database input T (db.update c lits fl) := by
  obtain ⟨hn, hu, hf, hl⟩ := hs
  have hlen : ∀ s ∈ db.all, s.1 = c → lits.length = s.2.length := fun s hs he => by
    rw [h.record_eq hs hr (he.trans hrc.symm)]; exact hperm.length_eq
  have hupd : ∀ s ∈ db.all, (if s.1 = c then (c, lits) else s).2.Perm s.2 := fun s hs => by
    split
    · rename_i he; rw [h.record_eq hs hr (he.trans hrc.symm)]; exact hperm
    · exact List.Perm.refl _
  have hstart : lemmasStart T (db.update c lits fl) = lemmasStart S db := by
    simp [lemmasStart, Records.update, hn, hf]
  have samei : ∀ s ∈ db.inputs, s.1 ≠ c → ∀ q, RecordCell s q → T.ld q = S.ld q :=
    fun s hs => same s (List.mem_append_left _ hs)
  have samel : ∀ s ∈ db.lemmas, s.1 ≠ c → ∀ q, RecordCell s q → T.ld q = S.ld q :=
    fun s hs => same s (List.mem_append_right _ hs)
  refine ⟨?_, ?_, by simp [Records.update, h.inputs_length], fun i hi hi' => ?_, fun s hs => ?_,
    fun he => ?_, by simp [Records.update, hl, h.nLemmas], fun s hs => ?_, fun s hs => ?_, ?_⟩
  · rw [hstart, hn]
    exact h.inputs_tile.update (fun s hs => hlen s (List.mem_append_left _ hs)) hc samei
  · rw [hstart, hu]
    exact h.lemmas_tile.update (fun s hs => hlen s (List.mem_append_right _ hs)) hc samel
  · simp only [Records.update, List.getElem_map]
    have hi2 : i < db.inputs.length := by simpa [Records.update] using hi
    exact (hupd _ (List.mem_append_left _ (List.getElem_mem hi2))).trans (h.inputs_perm i hi2 hi')
  · simp only [Records.update, List.mem_map] at hs
    obtain ⟨s0, hs0, rfl⟩ := hs
    have := h.inputs_nonempty s0 hs0
    intro he; apply this
    exact List.Perm.eq_nil ((hupd s0 (List.mem_append_left _ hs0)).symm.trans (by rw [he]))
  · simp only [Records.update, List.map_eq_nil_iff] at he ⊢; exact h.no_lemmas he
  · simp only [Records.update, List.mem_map] at hs
    obtain ⟨s0, hs0, rfl⟩ := hs
    have hp := hupd s0 (List.mem_append_right _ hs0)
    obtain ⟨h1, h2, h3⟩ := h.lemma_shape s0 hs0
    rw [hn]
    refine ⟨fun he => h1 (List.Perm.eq_nil (hp.symm.trans (by rw [he]))), (hp.map _).nodup_iff.mpr h2,
      fun l hl => h3 l (hp.mem_iff.mp hl)⟩
  · simp only [Records.update, List.mem_map] at hs
    obtain ⟨s0, hs0, rfl⟩ := hs
    intro a ha
    exact (clauseSat_perm (hupd s0 (List.mem_append_right _ hs0))).mpr (h.lemma_entailed s0 hs0 a ha)
  · simp only [Records.update]
    rw [List.pairwise_map]
    exact h.lemma_distinct.imp_of_mem fun {a b} ha hb hab hp => hab
      (((hupd a (List.mem_append_right _ ha)).symm.trans hp).trans (hupd b (List.mem_append_right _ hb)))

/-- Who watches what after updating record `r` (at `c`): its two links follow the new
literals and orientation; every other link is unchanged. -/
theorem Database.watches_update {input : Input} {S : solver} {db : Records} {r : Record} {c : Ptr}
    {lits : List CInt} {fl : Bool} (h : Database input S db) (hr : r ∈ db.all) (hrc : r.1 = c)
    {L link : CInt} :
    Watches (db.update c lits fl).all L link (db.update c lits fl).flip ↔
      (Watches db.all L link db.flip ∧ link ≠ c - 2 ∧ link ≠ c - 1) ∨
      (2 ≤ lits.length ∧ ((link = c - 2 ∧ lits[if fl then 1 else 0]? = some L) ∨
        (link = c - 1 ∧ lits[if fl then 0 else 1]? = some L))) := by
  rw [Records.update_all]
  constructor
  · rintro ⟨s, hs, h2, hw⟩
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
    by_cases he : s0.1 = c
    · simp only [he, if_true] at h2 hw
      simp only [Records.update, if_true] at hw
      exact Or.inr ⟨h2, hw⟩
    · simp only [he, if_false] at h2 hw
      simp only [Records.update, he, if_false] at hw
      have hap := h.apart hs0 hr (by rw [hrc]; exact he)
      refine Or.inl ⟨⟨s0, hs0, h2, hw⟩, ?_, ?_⟩ <;> rcases hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  · rintro (⟨⟨s0, hs0, h2, hw⟩, n0, n1⟩ | ⟨h2, hw⟩)
    · have he : s0.1 ≠ c := fun he => by rcases hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> simp_all
      refine ⟨s0, List.mem_map.mpr ⟨s0, hs0, by simp [he]⟩, h2, ?_⟩
      simp only [Records.update, he, if_false]; exact hw
    · refine ⟨(c, lits), List.mem_map.mpr ⟨r, hr, by simp [hrc]⟩, h2, ?_⟩
      simp only [Records.update, if_true]; exact hw

end MicrosatLean.Faithful.Verification
