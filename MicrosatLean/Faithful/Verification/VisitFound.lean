import MicrosatLean.Faithful.Verification.VisitAssign

/-!
# A visited clause with a new literal to watch (C:144–150)

The scan found a non-false literal `z` at position `t`: `z` moves to position 1, `lit` to
position `t`, and the visited link moves from `lit`'s watch list to `z`'s.
-/

namespace MicrosatLean.Faithful.Verification

/-- Swapping an element into the head: `a :: l` and `l[j] :: l.set j a` are reorderings. -/
theorem perm_set_head {a : CInt} {l : List CInt} {j : Nat} (hj : j < l.length) :
    (l[j] :: l.set j a).Perm (a :: l) := by
  have h1 : l = l.take j ++ l[j] :: l.drop (j + 1) := by
    conv => lhs; rw [← List.take_append_drop j l]
    rw [List.drop_eq_getElem_cons hj]
  have h2 : l.set j a = l.take j ++ a :: l.drop (j + 1) := by
    rw [List.set_eq_take_append_cons_drop, if_pos hj]
  rw [h2]
  conv => rhs; rw [h1]
  exact ((List.perm_middle).cons _).trans ((List.Perm.swap _ _ _).trans ((List.perm_middle).symm.cons _))

/-- The record's literals after C:142 and C:145–146 with the new literal at `t`. -/
def foundLits (r : Record) (lit : CInt) (t : Nat) : List CInt :=
  otherLit r lit :: r.2[t]! :: (r.2.drop 2).set (t - 2) lit

/-- The cells after C:142 and C:145–150: the record holds `foundLits`, the cursor cell `w`
skips the visited link `x`, `x` points to the old head of `z`'s list, and `z`'s head
points to `x`. -/
theorem Visit.found_cells {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S))
    {t : CInt} (ht2 : 2 ≤ t) (htl : t < r.2.length) :
    let z := r.2[t.toNat]!
    ClauseAt (foundState Ss c t w lit) c (foundLits r lit t.toNat) ∧
    (foundLits r lit t.toNat).Perm r.2 ∧
    (∃ DB, foundState Ss c t w lit = { S with DB := DB }) ∧
    (foundState Ss c t w lit).ld (S.first + z) = S.ld w ∧
    (foundState Ss c t w lit).ld (S.ld w) = S.ld (S.first + z) ∧
    (foundState Ss c t w lit).ld w = S.ld (S.ld w) ∧
    ∀ q, 0 ≤ q → q ≠ c → q ≠ c + 1 → q ≠ c + t → q ≠ w → q ≠ S.ld w → q ≠ S.first + z →
      (foundState Ss c t w lit).ld q = S.ld q := by
  intro z
  obtain ⟨a, b, tl, hr2, hab, hne, hrec⟩ := hv.slot
  obtain ⟨hlinks, hhd⟩ := hv.cells_ne hc
  have hl := hv.core.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hcb := hv.core.database.record_ge hv.hr; rw [← hc] at hcb; simp only [clausesAt] at hcb
  have hlen : r.2.length = tl.length + 2 := by rw [hr2]; simp
  obtain ⟨k, hk⟩ : ∃ k, t.toNat = k + 2 := ⟨t.toNat - 2, by omega⟩
  have ht' : k < tl.length := by omega
  have hz : z = tl[k] := by
    show r.2[t.toNat]! = _
    rw [getElem!_pos r.2 _ (by omega)]; simp only [hr2, hk]; rfl
  have hzmem : z ∈ r.2 := by rw [hz, hr2]; simp
  have hzr := inRange_iff.mp (hv.core.record_lit hv.hr hzmem)
  -- the cursor cell and the visited link are list cells, not literal cells
  have hwin : w ∈ (S.first + lit) :: visited := by rw [hv.path.end_eq]; exact List.getLast_mem _
  have hwc : 0 ≤ w ∧ w ≠ c ∧ w ≠ c + 1 ∧ (w = S.first + lit ∨ 10 * S.nVars + 8 ≤ w) := by
    rcases List.mem_cons.mp hwin with he | hm
    · rw [he]; exact ⟨hhd.1, hhd.2.1, hhd.2.2, Or.inl rfl⟩
    · have hw := (hv.mem w).mp (by simp [hm])
      obtain ⟨h0, h1, h2⟩ := hlinks lit w hw
      have := Watches.link_ge hv.core.database hw; simp only [clausesAt] at this
      exact ⟨h0, h1, h2, Or.inr this⟩
  have hxw := (hv.mem (S.ld w)).mp (by simp)
  obtain ⟨hx0, hx1, hx2⟩ := hlinks lit _ hxw
  have hxge := Watches.link_ge hv.core.database hxw; simp only [clausesAt] at hxge
  have hlitr := inRange_iff.mp (hv.core.trail.lit _ hv.hP); rw [hv.hlit] at hlitr
  -- distinct addresses
  have hwx : w ≠ S.ld w := by
    intro he
    have hnd := hv.nodup
    rcases List.mem_cons.mp hwin with he' | hm
    · omega
    · rw [he] at hm
      have := (List.nodup_cons.mp hnd).2
      exact (List.nodup_append.mp this).2.2 _ hm _ (by simp) rfl
  have hlinkcj : ∀ L q, Watches db.all L q db.flip → ∀ j : CInt, 0 ≤ j → j ≤ r.2.length → q ≠ c + j := by
    intro L q hw j hj0 hj1
    obtain ⟨s, hs, h2s, hsx⟩ := hw
    by_cases hsr : s.1 = c
    · rcases hsx with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
    · have := hv.core.database.apart hs hv.hr (by rw [← hc]; exact hsr); rw [← hc] at this
      rcases hsx with ⟨he, _⟩ | ⟨he, _⟩ <;> omega
  have hlinkct : ∀ L q, Watches db.all L q db.flip → q ≠ c + t := fun L q hw =>
    hlinkcj L q hw t (by omega) (by omega)
  have hct : ∀ q, (q = w ∨ q = S.ld w) → q ≠ c + t := by
    rintro q (rfl | rfl)
    · rcases List.mem_cons.mp hwin with he | hm
      · rw [he]; omega
      · exact hlinkct lit _ ((hv.mem _).mp (by simp [hm]))
    · exact hlinkct lit _ hxw
  have hfz : S.first + z ≠ w ∧ S.first + z ≠ S.ld w ∧ S.first + z ≠ c ∧ S.first + z ≠ c + 1 ∧
      S.first + z ≠ c + t ∧ 0 ≤ S.first + z := by
    refine ⟨fun he => ?_, by omega, by omega, by omega, by omega, by omega⟩
    rcases hwc.2.2.2 with he' | he'
    · rw [he'] at he
      have hzl : z ≠ lit := fun hzl => by
        -- `z` sits at position `t ≥ 2`, `lit` at position 0 or 1: distinct records literals
        have hnd := hv.core.record_nodup hv.hr
        rw [hr2] at hnd
        have hza : tl[k] ≠ a := fun h' => (List.nodup_cons.mp hnd).1 (by rw [← h']; simp)
        have hzb : tl[k] ≠ b := fun h' => (List.nodup_cons.mp (List.nodup_cons.mp hnd).2).1 (by rw [← h']; simp)
        rw [hz] at hzl
        rcases hab with h' | h'
        · exact hza (hzl.trans h'.symm)
        · exact hzb (hzl.trans h'.symm)
      omega
    · omega
  -- the cells, write by write
  have hSs' : ∀ q, 0 ≤ q → q ≠ c → Ss.ld q = S.ld q := fun q hq hqc => by
    rcases hSs with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rw [ld_st _ _ (by omega) hq, if_neg hqc]
    · rfl
  have hSsc : Ss.ld c = otherLit r lit := by
    have h0 := hrec.1 0 (by rw [hr2]; simp); rw [← hc] at h0; simp [hr2] at h0
    have h1 := hrec.1 1 (by rw [hr2]; simp); rw [← hc] at h1; simp [hr2] at h1
    rw [show otherLit r lit = if a = lit then b else a by simp [otherLit, hr2]]
    rcases hSs with ⟨hl', rfl⟩ | ⟨hl', rfl⟩
    · have hal : a = lit := h0.symm.trans hl'
      rw [ld_st_self _ _ (by omega), h1, if_pos hal]
    · have hal : a ≠ lit := fun h' => hl' (h0.trans h')
      rw [h0, if_neg hal]
  have hzc : Ss.ld (c + t) = z := by
    rw [hSs' _ (by omega) (by omega), hz]
    have := hrec.1 t.toNat (by omega); rw [← hc] at this
    rw [show c + ((t.toNat : Nat) : CInt) = c + t by omega] at this
    rw [this]; simp only [hr2, hk]; rfl
  -- the four writes of C:145–150
  have hc0 : 0 ≤ c := by omega
  have hS1 : ∀ q, 0 ≤ q → (Ss.st (c + 1) (Ss.ld (c + t))).ld q = if q = c + 1 then z else Ss.ld q := by
    intro q hq; rw [ld_st _ _ (by omega) hq, hzc]
  generalize hS1d : Ss.st (c + 1) (Ss.ld (c + t)) = S1 at hS1
  have hS2 : ∀ q, 0 ≤ q → (S1.st (c + t) lit).ld q = if q = c + t then lit else S1.ld q := by
    intro q hq; rw [ld_st _ _ (by omega) hq]
  generalize hS2d : S1.st (c + t) lit = S2 at hS2
  have hS2w : S2.ld w = S.ld w := by
    rw [hS2 _ hwc.1, if_neg (hct w (Or.inl rfl)), hS1 _ hwc.1, if_neg hwc.2.2.1, hSs' _ hwc.1 hwc.2.1]
  have hS2x : S2.ld (S.ld w) = S.ld (S.ld w) := by
    rw [hS2 _ hx0, if_neg (hct _ (Or.inr rfl)), hS1 _ hx0, if_neg hx2, hSs' _ hx0 hx1]
  have hS3 : ∀ q, 0 ≤ q → (S2.st w (S2.ld (S2.ld w))).ld q = if q = w then S.ld (S.ld w) else S2.ld q := by
    intro q hq; rw [ld_st _ _ hwc.1 hq, hS2w, hS2x]
  have hfirst : (S2.st w (S2.ld (S2.ld w))).first = S.first := by
    rw [st_first, ← hS2d, st_first, ← hS1d, st_first]
    rcases hSs with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rw [st_first]
    · rfl
  generalize hS3d : S2.st w (S2.ld (S2.ld w)) = S3 at hS3 hfirst
  have hS3c1 : S3.ld (c + 1) = z := by
    rw [hS3 _ (by omega), if_neg (Ne.symm hwc.2.2.1), hS2 _ (by omega), if_neg (by omega), hS1 _ (by omega), if_pos rfl]
  have hS3fz : S3.ld (S.first + z) = S.ld (S.first + z) := by
    rw [hS3 _ hfz.2.2.2.2.2, if_neg hfz.1, hS2 _ hfz.2.2.2.2.2, if_neg hfz.2.2.2.2.1, hS1 _ hfz.2.2.2.2.2,
      if_neg hfz.2.2.2.1, hSs' _ hfz.2.2.2.2.2 hfz.2.2.1]
  have hfs : foundState Ss c t w lit = addWatch S3 (S3.ld (c + 1)) (S2.ld w) := by
    rw [← hS3d, ← hS2d, ← hS1d]; rfl
  have hcell : ∀ q, 0 ≤ q → (foundState Ss c t w lit).ld q =
      if q = S.first + z then S.ld w else if q = S.ld w then S.ld (S.first + z)
      else if q = w then S.ld (S.ld w) else if q = c + t then lit else if q = c + 1 then z
      else if q = c then otherLit r lit else S.ld q := by
    intro q hq
    rw [hfs, addWatch_eq, hS3c1, hS2w, hfirst, ld_st _ _ hfz.2.2.2.2.2 hq]
    split; rfl
    rw [ld_st _ _ hx0 hq, hS3fz]
    split; rfl
    rw [hS3 _ hq]
    split; rfl
    rw [hS2 _ hq]
    split; rfl
    rw [hS1 _ hq]
    split; rfl
    by_cases hqc : q = c
    · rw [if_pos hqc, hqc, hSsc]
    · rw [if_neg hqc, hSs' _ hq hqc]
  -- the record after the writes
  have hflen : (foundLits r lit t.toNat).length = r.2.length := by simp [foundLits, hlen]
  have hcj : ∀ q, (q = w ∨ q = S.ld w ∨ q = S.first + z) → ∀ j : CInt, 0 ≤ j → j ≤ r.2.length → q ≠ c + j := by
    rintro q (rfl | rfl | rfl) j hj0 hj1
    · rcases List.mem_cons.mp hwin with he | hm
      · rw [he]; omega
      · exact hlinkcj lit _ ((hv.mem _).mp (by simp [hm])) j hj0 hj1
    · exact hlinkcj lit _ hxw j hj0 hj1
    · omega
  have hfl : ∀ j (hj : j < (foundLits r lit t.toNat).length), (foundState Ss c t w lit).ld (c + j) =
      (foundLits r lit t.toNat)[j] := by
    intro j hj
    have hjl : j < r.2.length := by rw [← hflen]; exact hj
    rw [hcell _ (by omega), if_neg (hcj _ (Or.inr (Or.inr rfl)) j (by omega) (by omega)).symm,
      if_neg (hcj _ (Or.inr (Or.inl rfl)) j (by omega) (by omega)).symm,
      if_neg (hcj _ (Or.inl rfl) j (by omega) (by omega)).symm]
    rcases j with _ | _ | j
    · rw [if_neg (by omega), if_neg (by omega), if_pos (by omega)]; rfl
    · rw [if_neg (by omega), if_pos (by omega)]; rfl
    · have hjt : j < tl.length := by omega
      by_cases hje : j = k
      · subst hje
        rw [if_pos (by omega)]
        simp only [foundLits, hr2, List.drop_succ_cons, List.drop_zero, List.getElem_cons_succ]
        simp only [show t.toNat - 2 = j by omega, List.getElem_set_self]
      · rw [if_neg (by omega), if_neg (by omega), if_neg (by omega)]
        simp only [foundLits, hr2, List.drop_succ_cons, List.drop_zero, List.getElem_cons_succ]
        simp only [show t.toNat - 2 = k by omega]
        rw [List.getElem_set_ne (by omega)]
        have := hrec.1 (j + 2) hjl; rw [← hc] at this
        rw [show c + ((j + 1 + 1 : Nat) : CInt) = c + ((j + 2 : Nat) : CInt) by omega, this]
        simp [hr2]
  have hfterm : (foundState Ss c t w lit).ld (c + (foundLits r lit t.toNat).length) = 0 := by
    rw [hflen, hcell _ (by omega), if_neg (hcj _ (Or.inr (Or.inr rfl)) _ (by omega) (by omega)).symm,
      if_neg (hcj _ (Or.inr (Or.inl rfl)) _ (by omega) (by omega)).symm,
      if_neg (hcj _ (Or.inl rfl) _ (by omega) (by omega)).symm, if_neg (by omega), if_neg (by omega),
      if_neg (by omega), hc]
    exact hrec.2
  have hst : ∀ (X : solver) (p v : CInt), (∃ DB, X = { S with DB := DB }) → ∃ DB, X.st p v = { S with DB := DB } :=
    fun X p v ⟨DB, hX⟩ => by obtain ⟨DB', hD⟩ := st_eq X p v; exact ⟨DB', by rw [hD, hX]⟩
  have hSsS : ∃ DB, Ss = { S with DB := DB } := by
    rcases hSs with ⟨_, he⟩ | ⟨_, he⟩
    · rw [he]; exact hst S _ _ ⟨S.DB, rfl⟩
    · rw [he]; exact ⟨S.DB, rfl⟩
  refine ⟨⟨hfl, hfterm⟩, ?_, ?_, ?_, ?_, ?_, fun q hq h1 h2 h3 h4 h5 h6 => ?_⟩
  · have hd2 : r.2.drop 2 = tl := by rw [hr2]; rfl
    rw [show foundLits r lit t.toNat = otherLit r lit :: tl[k] :: tl.set k lit by
      show otherLit r lit :: r.2[t.toNat]! :: (r.2.drop 2).set (t.toNat - 2) lit = _
      rw [hd2, show t.toNat - 2 = k by omega, show r.2[t.toNat]! = tl[k] from hz], hr2]
    rw [show otherLit r lit = if a = lit then b else a by simp [otherLit, hr2]]
    rcases hab with h' | h'
    · rw [if_pos h', h']
      exact ((perm_set_head ht').cons b).trans (List.Perm.swap _ _ _)
    · rw [if_neg (fun h'' => hne (h''.trans h'.symm)), h']
      exact (perm_set_head ht').cons a
  · rw [hfs, addWatch_eq]
    refine hst _ _ _ (hst _ _ _ ?_)
    rw [← hS3d]; refine hst _ _ _ ?_
    rw [← hS2d]; refine hst _ _ _ ?_
    rw [← hS1d]; exact hst _ _ _ hSsS
  · rw [hcell _ hfz.2.2.2.2.2, if_pos rfl]
  · rw [hcell _ hx0, if_neg (Ne.symm hfz.2.1), if_pos rfl]
  · rw [hcell _ hwc.1, if_neg (Ne.symm hfz.1), if_neg hwx, if_pos rfl]
  · rw [hcell q hq, if_neg h6, if_neg h5, if_neg h4, if_neg h3, if_neg h2, if_neg h1]

/-- Who watches what after the found case: the visited link `x` now watches `z`, the record's
other link still watches `y`, and `lit` is no longer watched by this record. -/
theorem Visit.found_watches {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1)
    {t : CInt} (ht2 : 2 ≤ t) (htl : t < r.2.length) (L link : CInt) :
    Watches (db.update c (foundLits r lit t.toNat) (decide (S.ld w = c - 2))).all L link
      (db.update c (foundLits r lit t.toNat) (decide (S.ld w = c - 2))).flip ↔
    (Watches db.all L link db.flip ∧ link ≠ S.ld w) ∨ (link = S.ld w ∧ L = r.2[t.toNat]!) := by
  obtain ⟨a, b, tl, hr2, hab, hne, -⟩ := hv.slot
  have hd := hv.core.database
  have hown := hd.watches_own hv.hr hv.h2 (L := L)
  rw [hd.watches_update hv.hr hc.symm]
  have hlen : 2 ≤ (foundLits r lit t.toNat).length := by simp [foundLits]
  have hx := hv.hx
  have hy : otherLit r lit = if a = lit then b else a := by simp [otherLit, hr2]
  rw [← hc] at hown hx
  have hfl0 : (foundLits r lit t.toNat)[0]? = some (otherLit r lit) := rfl
  have hfl1 : (foundLits r lit t.toNat)[1]? = some r.2[t.toNat]! := rfl
  have hxc : S.ld w = c - 2 ∨ S.ld w = c - 1 := by rcases hx with ⟨h1, _⟩ | ⟨h1, _⟩ <;> simp [h1]
  have hba : a ≠ lit → b = lit := fun h' => by rcases hab with h'' | h''; exact absurd h'' h'; exact h''
  -- the record's other link watches `y`, before and after
  have hother : ∀ link', (link' = c - 2 ∨ link' = c - 1) → link' ≠ S.ld w →
      (Watches db.all L link' db.flip ↔ L = otherLit r lit) := by
    intro link' hl1 hl2
    rw [hy]
    rcases hl1 with rfl | rfl
    · rw [hown.1]
      rcases hx with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact absurd h1.symm hl2
      · rw [hr2] at h2 ⊢
        cases hf : db.flip c <;> simp only [hf, Bool.false_eq_true, ite_false, ite_true] at h2 ⊢ <;>
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h2 ⊢
        · rw [if_neg (fun h' => hne (h'.trans h2.symm))]; exact eq_comm
        · rw [if_pos h2]; exact eq_comm
    · rw [hown.2]
      rcases hx with ⟨_, h2⟩ | ⟨h1, _⟩
      · rw [hr2] at h2 ⊢
        cases hf : db.flip c <;> simp only [hf, Bool.false_eq_true, ite_false, ite_true] at h2 ⊢ <;>
          simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.some.injEq] at h2 ⊢
        · rw [if_pos h2]; exact eq_comm
        · rw [if_neg (fun h' => hne (h'.trans h2.symm))]; exact eq_comm
      · exact absurd h1.symm hl2
  constructor
  · rintro (⟨hw, h1, h2⟩ | ⟨-, ⟨rfl, hl⟩ | ⟨rfl, hl⟩⟩)
    · exact Or.inl ⟨hw, by rcases hxc with he | he <;> rw [he] <;> assumption⟩
    · by_cases hxe : S.ld w = c - 2
      · simp only [hxe, decide_true, if_true] at hl; rw [hfl1] at hl
        exact Or.inr ⟨hxe.symm, (Option.some.inj hl).symm⟩
      · simp only [hxe, decide_false, Bool.false_eq_true, if_false] at hl; rw [hfl0] at hl
        exact Or.inl ⟨(hother _ (Or.inl rfl) (Ne.symm hxe)).mpr (Option.some.inj hl).symm, Ne.symm hxe⟩
    · by_cases hxe : S.ld w = c - 2
      · simp only [hxe, decide_true, if_true] at hl; rw [hfl0] at hl
        exact Or.inl ⟨(hother _ (Or.inr rfl) (by omega)).mpr (Option.some.inj hl).symm, by omega⟩
      · simp only [hxe, decide_false, Bool.false_eq_true, if_false] at hl; rw [hfl1] at hl
        have : S.ld w = c - 1 := by rcases hxc with h' | h'; exact absurd h' hxe; exact h'
        exact Or.inr ⟨this.symm, (Option.some.inj hl).symm⟩
  · rintro (⟨hw, hne'⟩ | ⟨rfl, rfl⟩)
    · by_cases h1 : link = c - 2
      · subst h1
        refine Or.inr ⟨hlen, Or.inl ⟨rfl, ?_⟩⟩
        have hxe : S.ld w ≠ c - 2 := Ne.symm hne'
        simp only [hxe, decide_false, Bool.false_eq_true, if_false]; rw [hfl0]
        rw [(hother _ (Or.inl rfl) hne').mp hw]
      · by_cases h2 : link = c - 1
        · subst h2
          refine Or.inr ⟨hlen, Or.inr ⟨rfl, ?_⟩⟩
          have hxe : S.ld w = c - 2 := by rcases hxc with h' | h'; exact h'; exact absurd h'.symm hne'
          simp only [hxe, decide_true, if_true]; rw [hfl0]
          rw [(hother _ (Or.inr rfl) hne').mp hw]
        · exact Or.inl ⟨hw, h1, h2⟩
    · refine Or.inr ⟨hlen, ?_⟩
      by_cases hxe : S.ld w = c - 2
      · exact Or.inl ⟨hxe, by simp only [hxe, decide_true, if_true]; exact hfl1⟩
      · have : S.ld w = c - 1 := by rcases hxc with h' | h'; exact absurd h' hxe; exact h'
        exact Or.inr ⟨this, by simp only [hxe, decide_false, Bool.false_eq_true, if_false]; exact hfl1⟩

/-- C:144–150: the scan found a non-false literal `z`; it becomes watched and the cursor
stays, now at the link after the one just moved. -/
theorem Visit.found_step {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S))
    {t : CInt} (ht2 : 2 ≤ t) (htl : t < r.2.length) (hfz : flag Ss (Ss.ld (c + t)) = 0) :
    WInv input S0 vs0 P lit (foundState Ss c t w lit) f w ∧
    (foundState Ss c t w lit).nLemmas = S.nLemmas ∧
    (linksAfter (foundState Ss c t w lit) w).length < (linksAfter S w).length := by
  obtain ⟨hcl, hperm, ⟨DB, hT⟩, hhz, hhx, hhw, hsame⟩ := hv.found_cells hc hSs ht2 htl
  have hwat := hv.found_watches hc ht2 htl
  obtain ⟨a, b, tl, hr2, hab, hne, hrec⟩ := hv.slot
  obtain ⟨hlinks, hhd⟩ := hv.cells_ne hc
  generalize hTd : foundState Ss c t w lit = T at *
  generalize hzd : r.2[t.toNat]! = z at *
  have core := hv.core; have hd := core.database; have ht := core.trail; have hl := core.layout
  have hn := hl.num; have hn1 := hl.nVars_pos; have hP := hv.hP
  have hcb := hd.record_ge hv.hr; rw [← hc] at hcb; simp only [clausesAt] at hcb
  have hzmem : z ∈ r.2 := by rw [← hzd, getElem!_pos r.2 _ (by omega)]; exact List.getElem_mem _
  have hzr := inRange_iff.mp (core.record_lit hv.hr hzmem)
  have hlitr := inRange_iff.mp (ht.lit _ hP); rw [hv.hlit] at hlitr
  -- `z` is not false
  have hzS : flag S z = 0 := by
    have hzc : Ss.ld (c + t) = z := by
      rcases hSs with ⟨_, he⟩ | ⟨_, he⟩ <;> subst he
      · rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)]
        have := hrec.1 t.toNat (by omega); rw [← hc, show c + ((t.toNat : Nat) : CInt) = c + t by omega] at this
        rw [this, ← hzd, getElem!_pos r.2 _ (by omega)]
      · have := hrec.1 t.toNat (by omega); rw [← hc, show c + ((t.toNat : Nat) : CInt) = c + t by omega] at this
        rw [this, ← hzd, getElem!_pos r.2 _ (by omega)]
    rw [hzc] at hfz
    simp only [flag] at hfz ⊢
    rcases hSs with ⟨_, he⟩ | ⟨_, he⟩ <;> subst he
    · simp only [st_false] at hfz; rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)] at hfz; exact hfz
    · exact hfz
  have hznot : ∀ j < trailLen S, trailAt S j ≠ z := fun j hj he => ht.flag_ne_zero hj (by rw [he]; exact hzS)
  have hzl : z ≠ lit := fun he => hznot P hP (by rw [hv.hlit, he])
  -- the cursor and the moved link
  have hwin : w ∈ (S.first + lit) :: visited := by rw [hv.path.end_eq]; exact List.getLast_mem _
  have hxw := (hv.mem (S.ld w)).mp (by simp)
  have hxge := Watches.link_ge hd hxw; simp only [clausesAt] at hxge
  have hwge : 8 * S.nVars + 6 ≤ w := by
    rcases List.mem_cons.mp hwin with he | hm
    · rw [he]; omega
    · have := Watches.link_ge hd ((hv.mem w).mp (by simp [hm])); simp only [clausesAt] at this; omega
  have hlow : LowSame S T := ⟨by rw [hT]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    by rw [hT], by rw [hT], by rw [hT], fun q h0 h1 => hsame q h0 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)⟩
  have hct : RecordCell r (c + t) := by simp only [RecordCell]; rw [← hc]; omega
  have hxne : S.ld w ≠ S.first + z := by omega
  -- cells of lists other than `lit`'s are untouched
  have hlinkL : ∀ L q, L ≠ lit → Watches db.all L q db.flip → T.ld q = S.ld q := by
    intro L q hL hw
    obtain ⟨h0, h1, h2⟩ := hlinks L q hw
    have hge := Watches.link_ge hd hw; simp only [clausesAt] at hge
    refine hsame q h0 h1 h2 (fun he => hd.link_not_record hv.hr hct (he ▸ hw)) (fun he => ?_)
      (fun he => hL (hd.watches_unique hw (he ▸ hxw))) (by omega)
    rcases List.mem_cons.mp hwin with he' | hm
    · omega
    · exact hL (hd.watches_unique hw (he ▸ (hv.mem w).mp (by simp [hm])))
  have hlinkLit : ∀ q ∈ visited ++ rest, T.ld q = S.ld q ∨ q = w := by
    intro q hq
    by_cases hqw : q = w
    · exact Or.inr hqw
    · left
      have hw := (hv.mem q).mp (by
        rcases List.mem_append.mp hq with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h'))
      obtain ⟨h0, h1, h2⟩ := hlinks lit q hw
      have hge := Watches.link_ge hd hw; simp only [clausesAt] at hge
      refine hsame q h0 h1 h2 (fun he => hd.link_not_record hv.hr hct (he ▸ hw)) hqw (fun he => ?_) (by omega)
      have hnd := (List.nodup_cons.mp hv.nodup).2
      rw [he] at hq
      simp only [List.mem_append] at hq
      rcases hq with hq | hq
      · exact (List.nodup_append.mp hnd).2.2 _ hq _ (by simp) rfl
      · exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 hq
  -- the new list of `lit`: the visited part, then the rest after the unlinked link
  have hpathT : Path T (S.first + lit) visited w := by
    refine hv.path.frame (fun q hq hqw => ?_) (hv.nodup.sublist (List.Sublist.cons₂ _ (List.sublist_append_left _ _)))
    rcases hq with rfl | hq
    · exact hsame _ hhd.1 hhd.2.1 hhd.2.2 (by omega) hqw (by omega) (by omega)
    · rcases hlinkLit q (by simp [hq]) with h' | h'
      · exact h'
      · exact absurd h' hqw
  have hrestT : ListFrom T w rest := hv.list.unlink hhw (fun q hq => by
      rcases hlinkLit q (by simp [hq]) with h' | h'
      · exact h'
      · exfalso
        have hnd := (List.nodup_cons.mp hv.nodup)
        rcases List.mem_cons.mp hwin with he | hm
        · exact hnd.1 (by rw [← he, ← h']; simp [hq])
        · exact (List.nodup_append.mp hnd.2).2.2 _ hm _ (by simp [← h', hq]) rfl)
    (hv.nodup.sublist (by
      refine List.Sublist.cons _ ?_; exact List.sublist_append_right _ _))
  have hpos : ∀ q ∈ rest, 0 ≤ q := fun q hq => (hlinks lit q ((hv.mem q).mp (by simp [hq]))).1
  have hwl : WatchLists T (db.update c (foundLits r lit t.toNat) (decide (S.ld w = c - 2))) := by
    intro L hL
    rw [hlow.shape.nVars] at hL
    have hLr := inRange_iff.mp hL
    rw [hlow.shape.first]
    by_cases hLl : L = lit
    · subst hLl
      refine ⟨visited ++ rest, listFrom_append.mpr ⟨w, hpathT, hrestT⟩,
        (List.nodup_cons.mp hv.nodup).2.sublist (List.Sublist.append_left (List.sublist_cons_self _ _) _), fun link => ?_⟩
      rw [hwat]
      constructor
      · intro hm
        have hm' : link ∈ visited ++ S.ld w :: rest := by
          rcases List.mem_append.mp hm with h' | h'
          · exact List.mem_append_left _ h'
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
        refine Or.inl ⟨(hv.mem link).mp hm', fun he => ?_⟩
        have hnd := (List.nodup_cons.mp hv.nodup).2
        rw [he] at hm
        rcases List.mem_append.mp hm with h' | h'
        · exact (List.nodup_append.mp hnd).2.2 _ h' _ (by simp) rfl
        · exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 h'
      · rintro (⟨hw, hne'⟩ | ⟨-, he⟩)
        · have := (hv.mem link).mpr hw
          rcases List.mem_append.mp this with h' | h'
          · exact List.mem_append_left _ h'
          · rcases List.mem_cons.mp h' with h'' | h''
            · exact absurd h'' hne'
            · exact List.mem_append_right _ h''
        · exact absurd he.symm hzl
    · by_cases hLz : L = z
      · subst hLz
        obtain ⟨lz, hlz, hndz, hmz⟩ := core.watches L hL
        have hlzc : ∀ q ∈ lz, T.ld q = S.ld q := fun q hq => hlinkL L q hLl ((hmz q).mp hq)
        refine ⟨S.ld w :: lz, hlz.push hhz hhx hlzc, List.nodup_cons.mpr ⟨fun hm =>
          hLl (hd.watches_unique ((hmz _).mp hm) hxw), hndz⟩, fun link => ?_⟩
        rw [hwat, List.mem_cons, hmz]
        constructor
        · rintro (rfl | hw)
          · exact Or.inr ⟨rfl, rfl⟩
          · exact Or.inl ⟨hw, fun he => hLl (hd.watches_unique hw (he ▸ hxw))⟩
        · rintro (⟨hw, -⟩ | ⟨he, -⟩)
          · exact Or.inr hw
          · exact Or.inl he
      · obtain ⟨ll, hll, hndl, hml⟩ := core.watches L hL
        refine ⟨ll, hll.frame fun q hq => ?_, hndl, fun link => ?_⟩
        · rcases hq with rfl | hq
          · refine hsame _ (by omega) (by omega) (by omega) (by omega) (fun he => ?_) (by omega) (by omega)
            rcases List.mem_cons.mp hwin with he' | hm
            · exact hLl (by omega)
            · have := Watches.link_ge hd ((hv.mem w).mp (by simp [hm])); simp only [clausesAt] at this; omega
          · exact hlinkL L q hLl ((hml q).mp hq)
        · rw [hwat, hml]
          constructor
          · intro hw; exact Or.inl ⟨hw, fun he => hLl (hd.watches_unique hw (he ▸ hxw))⟩
          · rintro (⟨hw, -⟩ | ⟨-, he⟩)
            · exact hw
            · exact absurd he hLz
  have hmemlit : ∀ link, link ∈ visited ++ rest ↔
      Watches (db.update c (foundLits r lit t.toNat) (decide (S.ld w = c - 2))).all lit link
        (db.update c (foundLits r lit t.toNat) (decide (S.ld w = c - 2))).flip := by
    intro link
    rw [hwat]
    constructor
    · intro hm
      have hm' : link ∈ visited ++ S.ld w :: rest := by
        rcases List.mem_append.mp hm with h' | h'
        · exact List.mem_append_left _ h'
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ h')
      refine Or.inl ⟨(hv.mem link).mp hm', fun he => ?_⟩
      have hnd := (List.nodup_cons.mp hv.nodup).2
      rw [he] at hm
      rcases List.mem_append.mp hm with h' | h'
      · exact (List.nodup_append.mp hnd).2.2 _ h' _ (by simp) rfl
      · exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 h'
    · rintro (⟨hw, hne'⟩ | ⟨-, he⟩)
      · have := (hv.mem link).mpr hw
        rcases List.mem_append.mp this with h' | h'
        · exact List.mem_append_left _ h'
        · rcases List.mem_cons.mp h' with h'' | h''
          · exact absurd h'' hne'
          · exact List.mem_append_right _ h''
      · exact absurd he.symm hzl
  -- the other records' cells are untouched
  have hother : ∀ s ∈ db.all, s.1 ≠ c → ∀ q, RecordCell s q → T.ld q = S.ld q := fun s hs hsc q hq => by
    have hap := hd.apart hs hv.hr (by rw [← hc]; exact hsc); rw [← hc] at hap
    have hsb := hd.record_ge hs; simp only [clausesAt] at hsb
    have h2 := hv.h2
    simp only [RecordCell] at hq
    refine hsame q (by omega) (by omega) (by omega) (by omega) (fun he => ?_) (fun he => ?_) (by omega)
    · rcases List.mem_cons.mp hwin with he' | hm
      · omega
      · exact hd.link_not_record hs (r := s) (q := q) (lit := lit) ⟨hq.1, hq.2⟩ (he ▸ (hv.mem w).mp (by simp [hm]))
    · exact hd.link_not_record hs (r := s) (q := q) (lit := lit) ⟨hq.1, hq.2⟩ (he ▸ hxw)
  have hsent : T.ld (clausesAt S.nVars - 1) = S.ld (clausesAt S.nVars - 1) := by
    simp only [clausesAt]
    refine hsame _ (by omega) (by omega) (by omega) (by omega) (fun he => ?_) (by omega) (by omega)
    rcases List.mem_cons.mp hwin with he' | hm
    · omega
    · have := Watches.link_ge hd ((hv.mem w).mp (by simp [hm])); simp only [clausesAt] at this; omega
  have hcore : Core input T (db.update c (foundLits r lit t.toNat) (decide (S.ld w = c - 2))) vs := by
    refine ⟨core.valid, by rw [hlow.shape.nVars]; exact core.nVars, by rw [hT]; exact core.memory,
      by rw [hT]; exact core.maxLemmas, hl.frame hlow.shape hsent, hlow.trail ht hl, hlow.root ht hl core.root,
      hd.update _ hv.hr hc.symm hperm hcl ⟨hlow.shape.nVars, by rw [hT], by rw [hT], by rw [hT]⟩ hother,
      hwl, ?_, ?_, hlow.order ht hl core.order (by rw [hT])⟩
    · -- the visited record is no reason: its literal `z` is not false
      intro i hi hfi hrs
      rw [hlow.trailLen ht hl] at hi; rw [hlow.forcedPos ht hl] at hfi
      have hti := inRange_iff.mp (ht.lit i hi)
      rw [hlow.trailAt ht hl hi, hlow.reasonOf ht hl (by omega) (by omega)] at hrs ⊢
      obtain ⟨s0, hs0, e1, e2, e3, e4⟩ := core.reasons i hi hfi hrs
      by_cases hsc : s0.1 = c
      · exfalso
        have hsr := hd.record_eq hs0 hv.hr (by rw [hsc, hc]); subst hsr
        have hzd1 : z ∈ s0.2.drop 1 := by
          rw [← hzd, getElem!_pos s0.2 _ (by omega)]
          rw [List.mem_iff_getElem]
          exact ⟨t.toNat - 1, by simp; omega, by rw [List.getElem_drop]; congr 1; omega⟩
        obtain ⟨j, hj, hfa⟩ := e3 z hzd1
        exact hznot j hfa.1 hfa.2
      · refine ⟨s0, by rw [Records.update_all]; exact List.mem_map.mpr ⟨s0, hs0, by simp [hsc]⟩, e1, e2,
          fun l hl' => ?_, fun hnr => ?_⟩
        · obtain ⟨j, hj, hfa⟩ := e3 l hl'; exact ⟨j, hj, (hlow.falseAt ht hl).mpr hfa⟩
        · obtain ⟨l, hl', j, hj, hfa, hsl⟩ := e4 fun h' => hnr ((hlow.rootLevel ht hl hi).mpr h')
          exact ⟨l, hl', j, hj, (hlow.falseAt ht hl).mpr hfa, (hlow.sameLevel ht hl hi).mpr hsl⟩
    · intro s hs h1
      rw [Records.update_all] at hs
      obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
      by_cases hsc : s0.1 = c
      · simp only [hsc, if_true, foundLits] at h1; simp at h1
      · simp only [hsc, if_false] at h1 ⊢
        obtain ⟨i, hi, hroot, he⟩ := core.units s0 hs0 h1
        exact ⟨i, by rw [hlow.trailLen ht hl]; exact hi, (hlow.rootLevel ht hl hi).mpr hroot,
          by rw [hlow.trailAt ht hl hi]; exact he⟩
  -- the visited record has no obligations: neither `y` nor `z` is false at a processed position
  have hy : ∀ p ≤ P, ¬ FalseAt S (otherLit r lit) p := by
    intro p hp hfa
    have hyl : otherLit r lit ≠ lit := by
      simp only [otherLit, hr2]; split
      · rename_i h'; exact fun h'' => hne (h'.trans h''.symm)
      · rename_i h'; simpa using h'
    rcases Nat.lt_or_ge p P with hpP | hpP
    · -- the old invariant would make `lit` true
      have hwy : ∃ w0 o0, (w0 = 0 ∧ o0 = 1 ∨ w0 = 1 ∧ o0 = 0) ∧ r.2[w0]! = otherLit r lit ∧ r.2[o0]! = lit := by
        simp only [otherLit, hr2]
        rcases hab with h' | h'
        · exact ⟨1, 0, Or.inr ⟨rfl, rfl⟩, by simp [h'], by simp [h']⟩
        · exact ⟨0, 1, Or.inl ⟨rfl, rfl⟩, by simp [show a ≠ lit from fun h'' => hne (h''.trans h'.symm)], by simp [h']⟩
      obtain ⟨w0, o0, hwo, hw0, ho0⟩ := hwy
      obtain ⟨q, hq, -⟩ := hv.watched r hv.hr hv.h2 w0 o0 hwo p (by rw [hv.hpp]; omega) (by rw [hw0]; exact hfa)
        (fun h' => absurd h' (by omega))
      rw [ho0] at hq
      have hqP := ht.distinct q hq.1 P hP (by rw [hq.2, hv.hlit, abs_neg'])
      have h1 := hq.2; rw [hqP, hv.hlit] at h1
      omega
    · have : p = P := by omega
      subst this; exact hyl (hfa.2.symm.trans hv.hlit)
  have hwe : WatchedExcept T (db.update c (foundLits r lit t.toNat) (decide (S.ld w = c - 2))) P rest := by
    intro s hs h2 w0 o hwo p hp hfa hex
    rw [hlow.processedPos ht hl, hv.hpp] at hp
    rw [Records.update_all] at hs
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
    by_cases hsc : s0.1 = c
    · exfalso
      simp only [hsc, if_true] at hfa
      rw [hlow.falseAt ht hl] at hfa
      rcases hwo with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact hy p (by omega) (by simpa [foundLits] using hfa)
      · exact hznot p hfa.1 (by have := hfa.2; simpa [foundLits, hzd] using this)
    · simp only [hsc, if_false] at h2 hfa hex ⊢
      exact hv.unit_hold hc (fun h' => Or.inl ((hlow.falseAt ht hl).mp h')) (fun h' => (hlow.falseAt ht hl).mpr h')
        (fun p q hq h' => (hlow.sameLevel ht hl hq).mpr h') s0 hs0 hsc h2 w0 o hwo p hp hfa hex
  refine ⟨⟨_, vs, visited, rest, hcore, by rw [hlow.processedPos ht hl, hv.hpp],
    by rw [hlow.trailLen ht hl]; exact hP, by rw [hlow.trailAt ht hl hP]; exact hv.hlit,
    by rw [hlow.shape.first]; exact hpathT, hrestT,
    by rw [hlow.shape.first]; exact hv.nodup.sublist (List.Sublist.cons₂ _
      (List.Sublist.append_left (List.sublist_cons_self _ _) _)),
    hmemlit, hwe, hlow.pmode ht hl hv.pmode, hlow.rel ht hl hv.rel (by rw [hT]) (by rw [hT])⟩, by rw [hT], ?_⟩
  rw [linksAfter_eq hrestT hpos, linksAfter_eq hv.list (fun q hq => by
    rcases List.mem_cons.mp hq with rfl | hq
    · exact (hlinks lit _ hxw).1
    · exact hpos q hq)]
  simp

end MicrosatLean.Faithful.Verification
