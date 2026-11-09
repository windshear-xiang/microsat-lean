import MicrosatLean.Fast.Verification.Inv

/-!
# The loops of the fast `reduceDB` (C:68–83)

Each fast loop of `reduceDB` meets the contract of the faithful phase it implements, proved
by induction on the fast loop with the faithful loop invariant and per-iteration lemmas
(`MicrosatLean/Faithful/Verification/ReduceDB.lean`):

* `raiseLoop_spec`: C:69–70, `maxLemmas` rises past `nLemmas` by less than 300;
* `unlinkLoop_spec`, `unlinkAll_fast`: C:73–77, with the invariants `Unlinking` and
  `UnlinkedUpTo`. Both ports run over the literals in the same order (`-nVars` up to
  `nVars`, skipping 0);
* `countLoop_end`, `keepLoop_fast`: C:78–83, with the invariant `KeepInv`. The faithful
  per-record lemmas `KeepInv.drop` and (generalized to any result meeting `AddClausePost`)
  `KeepInv.add_of_post` do each iteration. The count of literals agreeing with the saved phase
  only chooses between the two, so its value does not matter for the contract.

Equalities between abstractions of fast states that differ in some field are never left to the
kernel (`ld_abs_eq_ldA`, `ld_with_counters`): unfolding `Int32.toInt` there recurses too deeply.
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast
set_option linter.deprecated false

/-- `raiseLoop` (C:69–70): from `m ≤ n + 299`, the result is at least `m` and `n`, and at
most `n + 299`. -/
theorem raiseLoop_spec (n : Cell) (hn : n.toInt + 300 < 2 ^ 31) :
    ∀ (k : Nat) (m : Cell), (n.toInt - m.toInt).toNat = k → m.toInt ≤ n.toInt + 299 →
      m.toInt ≤ (raiseLoop n m).toInt ∧ n.toInt ≤ (raiseLoop n m).toInt ∧
        (raiseLoop n m).toInt ≤ n.toInt + 299 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro m hk hm
  rw [raiseLoop.eq_1]
  by_cases hgt : n > m
  · rw [if_pos hgt]
    have hgt' : m.toInt < n.toInt := Int32.lt_iff_toInt_lt.mp hgt
    have h300 : ((300 : Cell)).toInt = 300 := rfl
    have hm3 : (m + 300).toInt = m.toInt + 300 := by
      rw [toInt_add (by rw [h300]; have := Int32.le_toInt m; omega) (by rw [h300]; omega), h300]
    obtain ⟨r1, r2, r3⟩ := ih _ (by omega) (m + 300) rfl (by rw [hm3]; omega)
    exact ⟨by omega, r2, r3⟩
  · rw [if_neg hgt]
    have hle : n.toInt ≤ m.toInt := Int.not_lt.mp (fun h => hgt (Int32.lt_iff_toInt_lt.mpr h))
    exact ⟨Int.le_refl _, hle, hm⟩

/-- The scan of `countLoop` (C:79) from `i` stops at the first 0 cell, `e`. -/
theorem countLoop_end {db : Array Cell} (hsz : db.size ≤ 2 ^ 31) {e : Int} (he : e < 2 ^ 30)
    (hz : ldA (toDB db) e = 0) :
    ∀ (k : Nat) (i c : Cell), (e - i.toInt).toNat = k → 0 ≤ i.toInt → i.toInt ≤ e →
      (∀ q, i.toInt ≤ q → q < e → ldA (toDB db) q ≠ 0) → (countLoop db i c).2.toInt = e := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro i c hk hi0 hie hnz
  rw [countLoop.eq_1]
  have hl : (ld db i).toInt = ldA (toDB db) i.toInt := ld_sim _ rfl hsz i
  by_cases heq : i.toInt = e
  · have h0 : ld db i = 0 := Int32.toInt_inj.mp (by rw [hl, heq, hz]; rfl)
    simp only [h0, beq_self_eq_true, if_true]
    exact heq
  · have h0 : ¬ ld db i = 0 := fun h => hnz i.toInt (Int.le_refl _) (by omega) (by rw [← hl, h]; rfl)
    have h1 : ((1 : Cell)).toInt = 1 := rfl
    have hi1 : (i + 1).toInt = i.toInt + 1 := by rw [toInt_add (by rw [h1]; omega) (by rw [h1]; omega), h1]
    rw [if_neg (by simpa using h0)]
    exact ih _ (by omega) (i + 1) _ rfl (by omega) (by omega)
      (fun q h1 h2 => hnz q (by omega) h2)

/-- `unlinkLoop` (C:74–76) on the list of literal `i`, from the cursor `watch`: the faithful
`unlinkList_spec` (whose loop invariant is `Unlinking`) for the fast loop. `S` is the
faithful state before the loop; `pa` are the links visited, `pb` those still to visit. -/
theorem unlinkLoop_spec {S : solver} {i : Int} {links : List Ptr} {memFixed : Cell}
    (hmf : S.mem_fixed = memFixed.toInt)
    (hnd : ((S.first + i) :: links).Nodup) (hpos : 0 ≤ S.first + i) (hlinks : ∀ q ∈ links, 0 ≤ q) :
    ∀ (pb pa : List Ptr) (db : Array Cell) (watch : Cell), links = pa ++ pb → db.size ≤ 2 ^ 31 →
      Path { S with DB := toDB db } (S.first + i) (pa.filter (· < S.mem_fixed)) watch.toInt →
      ListFrom { S with DB := toDB db } watch.toInt pb →
      (∀ q, 0 ≤ q → q ≠ S.first + i → q ∉ pa.filter (· < S.mem_fixed) →
        ({ S with DB := toDB db } : solver).ld q = S.ld q) →
      (unlinkLoop db memFixed watch).size ≤ 2 ^ 31 ∧
      ListFrom { S with DB := toDB (unlinkLoop db memFixed watch) } (S.first + i)
        (links.filter (· < S.mem_fixed)) ∧
      (∀ q, 0 ≤ q → q ≠ S.first + i → q ∉ links.filter (· < S.mem_fixed) →
        ({ S with DB := toDB (unlinkLoop db memFixed watch) } : solver).ld q = S.ld q) := by
  have hEND : (Fast.END).toInt = -9 := by decide
  intro pb
  induction pb with
  | nil =>
    intro pa db watch hsplit hsz hpath hlf hcells
    rw [unlinkLoop.eq_1]
    have hw : (ld db watch).toInt = MicrosatLean.Faithful.END := by
      rw [ld_sim { S with DB := toDB db } rfl hsz]; exact hlf
    have hw' : ld db watch = Fast.END := Int32.toInt_inj.mp (by rw [hw, hEND])
    simp only [hw', beq_self_eq_true, if_true]
    simp only [List.append_nil] at hsplit
    rw [hsplit]
    have h1 : ListFrom ({ S with DB := toDB db } : solver) (S.first + i)
        (pa.filter (· < S.mem_fixed) ++ []) :=
      listFrom_append.mpr ⟨watch.toInt, hpath, hlf⟩
    rw [List.append_nil] at h1
    exact ⟨hsz, h1, hcells⟩
  | cons x pb' ih =>
    intro pa db watch hsplit hsz hpath hlf hcells
    rw [unlinkLoop.eq_1]
    have hx : ({ S with DB := toDB db } : solver).ld watch.toInt = x := hlf.1
    have hxw : (ld db watch).toInt = x := by rw [ld_sim { S with DB := toDB db } rfl hsz]; exact hx
    have hx0 : 0 ≤ x := hlinks x (by rw [hsplit]; simp)
    have hne : ¬ (ld db watch == Fast.END) = true := by
      rw [beq_iff_eq]; intro he; rw [he, hEND] at hxw; omega
    have hpos' : ∀ q ∈ pb', 0 ≤ q := fun q hq => hlinks q (by rw [hsplit]; simp [hq])
    rw [if_neg hne]
    by_cases hlt : x < S.mem_fixed
    · -- an input link: keep it and move the cursor (C:76, `watch = DB + *watch`)
      have hlt' : ld db watch < memFixed := Int32.lt_iff_toInt_lt.mpr (by rw [hxw, ← hmf]; exact hlt)
      rw [if_pos hlt']
      refine ih (pa ++ [x]) db (ld db watch) (by rw [hsplit]; simp) hsz ?_ (by rw [hxw]; exact hlf.2)
        fun q hq h1 h2 => hcells q hq h1 fun hm => h2 (by rw [List.filter_append]; exact List.mem_append_left _ hm)
      rw [List.filter_append]; simp only [List.filter_cons, List.filter_nil, decide_eq_true hlt, if_true]
      rw [hxw]
      exact hpath.snoc hx
    · -- a lemma link: unlink it (C:76, `*watch = DB[*watch]`)
      have hlt' : ¬ ld db watch < memFixed := fun h => hlt (by rw [hmf, ← hxw]; exact Int32.lt_iff_toInt_lt.mp h)
      rw [if_neg hlt']
      generalize hS' : ({ S with DB := toDB db } : solver) = S' at hpath hlf hcells hx
      have hnd' : ((S.first + i) :: (pa ++ x :: pb')).Nodup := by rw [← hsplit]; exact hnd
      have hwin : watch.toInt ∈ (S.first + i) :: pa.filter (· < S.mem_fixed) := by
        rw [hpath.end_eq]; exact List.getLast_mem _
      have hsub : ((S.first + i) :: pa.filter (· < S.mem_fixed)).Sublist ((S.first + i) :: (pa ++ x :: pb')) :=
        List.Sublist.cons₂ _ ((List.filter_sublist).trans (List.sublist_append_left _ _))
      have hndw : ((S.first + i) :: pa.filter (· < S.mem_fixed)).Nodup := hnd'.sublist hsub
      have hwpos : 0 ≤ watch.toInt := by
        simp only [List.mem_cons, List.mem_filter] at hwin
        rcases hwin with he | ⟨hm, -⟩
        · rw [he]; exact hpos
        · exact hlinks _ (by rw [hsplit]; simp [hm])
      have hwpb : ∀ q ∈ x :: pb', q ≠ watch.toInt := fun q hq he => by
        rw [← he] at hwin
        rw [List.nodup_cons] at hnd'
        simp only [List.mem_cons] at hwin
        rcases hwin with he' | hwin
        · exact hnd'.1 (by rw [← he']; simp [hq])
        · have := List.nodup_append.mp hnd'.2
          exact this.2.2 _ (List.mem_filter.mp hwin).1 _ hq rfl
      -- the write, on the faithful side
      have hvx : (ld db (ld db watch)).toInt = S'.ld x := by
        rw [ld_sim S' (by rw [← hS']) hsz, hxw]
      obtain ⟨e, hsz'⟩ := st_sim S' (by rw [← hS']) hsz watch (ld db (ld db watch))
      rw [hvx] at e
      have hT : ∀ q, ({ S with DB := toDB (st db watch (ld db (ld db watch))) } : solver).ld q =
          (S'.st watch.toInt (S'.ld x)).ld q := fun q => by
        rw [ld_eq_ldA, ld_eq_ldA (S'.st _ _)]; exact congrArg (ldA · q) e.symm
      have hlf' : ListFrom { S with DB := toDB (st db watch (ld db (ld db watch))) } watch.toInt pb' := by
        refine (hlf.unlink (T := S'.st watch.toInt (S'.ld x)) (by rw [ld_st_self _ _ hwpos])
          (fun q hq => ld_st_of_ne _ _ hwpos (hpos' q hq) (hwpb q (by simp [hq])))
          (hnd'.sublist (by simp))).frame fun q _ => hT q
      have hfilt : (pa ++ [x]).filter (· < S.mem_fixed) = pa.filter (· < S.mem_fixed) := by
        rw [List.filter_append]; simp [hlt]
      refine ih (pa ++ [x]) _ watch (by rw [hsplit]; simp) hsz' ?_ hlf' fun q hq h1 h2 => ?_
      · rw [hfilt]
        have hp1 : Path (S'.st watch.toInt (S'.ld x)) (S.first + i) (pa.filter (· < S.mem_fixed)) watch.toInt := by
          refine hpath.frame (fun q hq hqw => ?_) hndw
          have hq' : 0 ≤ q := by
            rcases hq with rfl | hq
            · exact hpos
            · exact hlinks q (by rw [hsplit]; simp [(List.mem_filter.mp hq).1])
          exact ld_st_of_ne _ _ hwpos hq' hqw
        exact hp1.frame (fun q _ _ => hT q) hndw
      · rw [hfilt] at h2
        have hqw : q ≠ watch.toInt := fun he => by
          rw [← he] at hwin; simp only [List.mem_cons] at hwin
          rcases hwin with he' | hm
          · exact h1 he'
          · exact h2 hm
        rw [hT, ld_st_of_ne _ _ hwpos hq hqw]
        exact hcells q hq h1 h2

/-- `unlinked_step` for any state `U` that meets `unlinkList_spec`'s postcondition (instead of
the faithful `unlinkList S' x`). -/
theorem unlinked_step_of {S : solver} {db : Records} (hl : Layout S)
    (hd : LinkFacts S db) {pre : List CInt} {x : CInt} {S' U : solver}
    (hx : InRange S.nVars x) (hxpre : x ∉ pre) (h : UnlinkedUpTo S db pre S')
    (hU : ∀ links, ListFrom S' (S'.first + x) links → ((S'.first + x) :: links).Nodup →
      0 ≤ S'.first + x → (∀ q ∈ links, 0 ≤ q) →
      (∃ DB, U = { S' with DB := DB }) ∧
      ListFrom U (S'.first + x) (links.filter (· < S'.mem_fixed)) ∧
      (∀ q, 0 ≤ q → q ≠ S'.first + x → q ∉ links.filter (· < S'.mem_fixed) → U.ld q = S'.ld q)) :
    UnlinkedUpTo S db (pre ++ [x]) U := by
  obtain ⟨⟨DB, hS'⟩, hlists, hcells⟩ := h
  have hfS : S'.first = S.first ∧ S'.mem_fixed = S.mem_fixed := by rw [hS']; exact ⟨rfl, rfl⟩
  have hn := hl.num; have hn1 := hl.nVars_pos
  have hxr := inRange_iff.mp hx
  obtain ⟨lx, hlx, hndx, hmx⟩ := hlists x hx
  simp only [hxpre, if_false] at hmx
  have hge : ∀ q ∈ lx, clausesAt S.nVars ≤ q := fun q hq => hd.ge x q ((hmx q).mp hq)
  obtain ⟨⟨DB', hU⟩, hlU, hcU⟩ := hU lx
    (by rw [hfS.1]; exact hlx)
    (List.nodup_cons.mpr ⟨fun hm => by have := hge _ hm; rw [hfS.1] at this; simp only [clausesAt] at this; omega,
      hndx⟩)
    (by rw [hfS.1]; omega) (fun q hq => by have := hge q hq; simp only [clausesAt] at this; omega)
  rw [hfS.1, hfS.2] at hlU hcU
  have hnotx : ∀ lit, lit ≠ x → ∀ q, Watches db.all lit q db.flip → q ∉ lx.filter (· < S.mem_fixed) :=
    fun lit hne q hq hm => hne (hd.unique _ _ q hq ((hmx q).mp (List.mem_filter.mp hm).1))
  refine ⟨⟨DB', by rw [hU, hS']⟩, fun lit hlit => ?_, fun q hq hall => ?_⟩
  · by_cases hlx' : lit = x
    · subst hlx'
      refine ⟨lx.filter (· < S.mem_fixed), hlU, hndx.filter _, fun link => ?_⟩
      simp only [List.mem_append, List.mem_singleton, or_true, if_true, List.mem_filter, hmx,
        decide_eq_true_eq]
      exact ⟨fun ⟨hw, hlt⟩ => (hd.input_iff _ _ hw).mpr hlt,
        fun hw => ⟨hw.of_inputs, (hd.input_iff _ _ hw.of_inputs).mp hw⟩⟩
    · obtain ⟨ll, hll, hndl, hml⟩ := hlists lit hlit
      have hlr := inRange_iff.mp hlit
      refine ⟨ll, hll.frame fun q hq => ?_, hndl, fun link => ?_⟩
      rotate_left
      · have e := hml link
        by_cases hp : lit ∈ pre
        · rw [if_pos (by simp [hp])]; rw [if_pos hp] at e; exact e
        · rw [if_neg (by simp [hp, hlx'])]; rw [if_neg hp] at e; exact e
      have hw : ∀ q ∈ ll, Watches db.all lit q db.flip := fun q hq => by
        have := (hml q).mp hq; split at this
        · exact this.of_inputs
        · exact this
      rcases hq with rfl | hq
      · apply hcU _ (by omega) (by omega)
        intro hm; have := hge _ (List.mem_filter.mp hm).1; simp only [clausesAt] at this; omega
      · have := hd.ge lit q (hw q hq)
        exact hcU q (by simp only [clausesAt] at this; omega) (by simp only [clausesAt] at this; omega)
          (hnotx lit hlx' q (hw q hq))
  · obtain ⟨n0, n1⟩ := hall x (by simp)
    rw [hcU q hq n0 fun hm => n1 ((hmx q).mp (List.mem_filter.mp hm).1)]
    exact hcells q hq fun lit hl' => hall lit (by simp [hl'])

/-- `unlinkAll` (C:73–77) from literal `i` on: the faithful `unlinkAll_spec` for the fast loop,
which runs over the literals in the same order (`-nVars` up to `nVars`, skipping 0). The
literals `pre` already done are those from `-nVars` below `i`. -/
theorem unlinkAll_fast {S : solver} {db : Records} {L : Lay} {memFixed : Cell} (hl : Layout S)
    (hd : LinkFacts S db)
    (hfirst : S.first = L.first.toInt) (hnv : S.nVars = L.nVars.toInt) (hmf : S.mem_fixed = memFixed.toInt)
    (hN : 10 * S.nVars + 7 ≤ 2 ^ 30) :
    ∀ (k : Nat) (dbA : Array Cell) (i : Cell), (S.nVars + 1 - i.toInt).toNat = k → dbA.size ≤ 2 ^ 31 →
      -S.nVars ≤ i.toInt → i.toInt ≤ S.nVars + 1 →
      ∀ pre, (∀ v, v ∈ pre ↔ -S.nVars ≤ v ∧ v < i.toInt ∧ v ≠ 0) →
      UnlinkedUpTo S db pre { S with DB := toDB dbA } →
      (unlinkAll L dbA memFixed i).size ≤ 2 ^ 31 ∧
      ∃ pre, (∀ v, v ∈ pre ↔ InRange S.nVars v) ∧
        UnlinkedUpTo S db pre { S with DB := toDB (unlinkAll L dbA memFixed i) } := by
  have hn := hl.num; have hn1 := hl.nVars_pos
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro dbA i hk hsz hi1 hi2 pre hpre hinv
  rw [unlinkAll.eq_1]
  have h1 : ((1 : Cell)).toInt = 1 := rfl
  by_cases hle : i ≤ L.nVars
  · rw [if_pos hle]
    have hle' : i.toInt ≤ S.nVars := by rw [hnv]; exact Int32.le_iff_toInt_le.mp hle
    have hi1' : (i + 1).toInt = i.toInt + 1 := by
      rw [toInt_add (by rw [h1]; omega) (by rw [h1]; omega), h1]
    by_cases h0 : i = 0
    · have h0' : i.toInt = 0 := by rw [h0]; rfl
      rw [if_pos (by simp [h0])]
      exact ih _ (by omega) dbA (i + 1) rfl hsz (by omega) (by omega) pre
        (fun v => by rw [hpre v, hi1']; omega) hinv
    · have h0' : i.toInt ≠ 0 := fun h => h0 (Int32.toInt_inj.mp (by rw [h]; rfl))
      rw [if_neg (by simpa using h0)]
      have hx : InRange S.nVars i.toInt := inRange_iff.mpr ⟨h0', hi1, hle'⟩
      have hxpre : i.toInt ∉ pre := fun hm => by have := (hpre _).mp hm; omega
      have hw : (L.first + i).toInt = S.first + i.toInt := by
        rw [toInt_add (by omega) (by omega), hfirst]
      -- the fast inner loop meets `unlinkList_spec`
      have hspec : ∀ links, ListFrom ({ S with DB := toDB dbA } : solver) (S.first + i.toInt) links →
          ((S.first + i.toInt) :: links).Nodup → 0 ≤ S.first + i.toInt → (∀ q ∈ links, 0 ≤ q) →
          (unlinkLoop dbA memFixed (L.first + i)).size ≤ 2 ^ 31 ∧
          ListFrom { S with DB := toDB (unlinkLoop dbA memFixed (L.first + i)) } (S.first + i.toInt)
            (links.filter (· < S.mem_fixed)) ∧
          (∀ q, 0 ≤ q → q ≠ S.first + i.toInt → q ∉ links.filter (· < S.mem_fixed) →
            ({ S with DB := toDB (unlinkLoop dbA memFixed (L.first + i)) } : solver).ld q =
              ({ S with DB := toDB dbA } : solver).ld q) := fun links hlf hnd hpos hlinks =>
        unlinkLoop_spec (S := { S with DB := toDB dbA }) (i := i.toInt) hmf hnd hpos hlinks links [] dbA
          (L.first + i) rfl hsz (by rw [hw]; rfl) (by rw [hw]; exact hlf) fun q _ _ _ => rfl
      have hstep := unlinked_step_of (U := { S with DB := toDB (unlinkLoop dbA memFixed (L.first + i)) })
        hl hd hx hxpre hinv fun links hlf hnd hpos hlinks =>
          have r := hspec links hlf hnd hpos hlinks
          ⟨⟨_, rfl⟩, r.2.1, r.2.2⟩
      obtain ⟨lx, hlx, hndx, hmx⟩ := hinv.2.1 i.toInt hx
      simp only [hxpre, if_false] at hmx
      have hge : ∀ q ∈ lx, clausesAt S.nVars ≤ q := fun q hq => hd.ge _ q ((hmx q).mp hq)
      have hsz' := (hspec lx hlx
        (List.nodup_cons.mpr ⟨fun hm => by have := hge _ hm; simp only [clausesAt] at this; omega, hndx⟩)
        (by omega) (fun q hq => by have := hge q hq; simp only [clausesAt] at this; omega)).1
      exact ih _ (by omega) _ (i + 1) rfl hsz' (by omega) (by omega) (pre ++ [i.toInt])
        (fun v => by simp only [List.mem_append, List.mem_singleton, hpre v, hi1']; omega) hstep
  · rw [if_neg hle]
    have hgt : S.nVars < i.toInt := by
      rw [hnv]; exact Int.not_le.mp fun h => hle (Int32.le_iff_toInt_le.mpr h)
    exact ⟨hsz, pre, fun v => by rw [hpre v, inRange_iff]; omega, hinv⟩

/-- `KeepInv.add` for any result `r` of copying lemma record `j` that meets `AddClausePost`
(instead of the faithful `addClause`). -/
theorem KeepInv.add_of_post {U S' : solver} {inputs lemmas : List Record} {F : Ptr → Bool} {j : Nat}
    (hj : j < lemmas.length) (hp : KeepPre U inputs lemmas F) (h : KeepInv U inputs lemmas F S' lemmas[j].1)
    {r : solver × Ptr} (post : AddClausePost S' lemmas[j].2 lemmas[j].2.length 0 r) :
    KeepInv U inputs lemmas F r.1 (lemmas[j].1 + lemmas[j].2.length + 3) := by
  obtain ⟨j', hj', K, hpos, ⟨DB, hS'⟩, ht, hsub, hmu, hhigh, hlow, hw⟩ := h
  have hjj : j' = j := by
    rcases Nat.lt_or_ge j' lemmas.length with h' | h'
    · rw [(hp.lemmas_tile.tilePos_succ j' h').2] at hpos
      have := hp.lemmas_tile.sorted
      refine Classical.byContradiction fun hne => ?_
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have := (List.pairwise_iff_getElem.mp this) j' j h' hj hlt; omega
      · have := (List.pairwise_iff_getElem.mp this) j j' hj h' hlt; omega
    · have : j' = lemmas.length := by omega
      subst this; rw [tilePos_length] at hpos
      have := hp.lemmas_tile.bounds.2 _ (List.getElem_mem hj); omega
  subst hjj
  have hc0 := hp.lemmas_tile.clauseAt (List.getElem_mem hj)
  have hlb := hp.lemmas_tile.bounds.2 _ (List.getElem_mem hj)
  have hshape := hp.shape _ (List.getElem_mem hj)
  have hnd : lemmas[j'].2.Nodup :=
    List.Pairwise.of_map Int.natAbs (fun a b hab he => hab (by rw [he])) hshape.2.1
  have hl := hp.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hfx := hp.fixed_ge; simp only [clausesAt] at hfx
  have htb := ht.bounds
  generalize hcd : lemmas[j'].1 = c at hpos hmu hhigh hc0 hlb ⊢
  generalize hld : lemmas[j'].2 = lits at hc0 hlb hshape hnd post ⊢
  generalize hmu0 : S'.mem_used = mu at hS' ht hmu htb
  have hf : S'.first = U.first ∧ S'.mem_max = U.mem_max ∧ S'.nVars = U.nVars ∧
      S'.mem_fixed = U.mem_fixed := by rw [hS']; exact ⟨rfl, rfl, rfl, rfl⟩
  have hlit : ∀ x ∈ lits, -U.nVars ≤ x ∧ x ≤ U.nVars := fun x hx => by
    have := inRange_iff.mp (hshape.2.2 x hx); omega
  have hfirstcells : ∀ q, 10 * U.nVars + 8 ≤ q → 1 < lits.length →
      q ≠ S'.first + lits[0]! ∧ q ≠ S'.first + lits[1]! := fun q hq hl2 => by
    obtain ⟨m0, m1, -⟩ := first_two hl2 hnd
    have := hlit _ m0; have := hlit _ m1; rw [hf.1]; omega
  obtain ⟨hr2, hmu2, hlits, hterm, hbelow, habove, DB2, hr1⟩ := id post
  have hsent : S'.ld (clausesAt U.nVars - 1) = U.ld (clausesAt U.nVars - 1) :=
    hlow _ (by simp only [clausesAt]; omega) (by simp only [clausesAt]; omega)
      (Or.inr (by simp only [clausesAt]; omega))
  have hlayS : Layout S' :=
    hl.frame (by rw [hS']; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩) hsent
  rw [hmu0] at hr2 hmu2
  refine ⟨j' + 1, hj, K ++ [(mu + 2, lits)],
    by rw [← hcd, ← hld]; exact (hp.lemmas_tile.tilePos_succ j' hj).1.symm, ⟨DB2, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr1, hS']; simp [added]
  · rw [hmu2, show mu + (lits.length : CInt) + 3 = mu + 3 + lits.length by omega]
    refine (ht.frame fun s hs q hq => ?_).append ⟨fun t ht' => ?_, ?_⟩
    · have := htb.2 s hs; simp only [RecordCell] at hq
      exact post.below (by omega) (by rw [hmu0]; omega) (hfirstcells q (by omega))
    · rw [← hr2]; exact hlits t ht'
    · rw [← hr2]; exact hterm
  · rw [List.take_succ, List.getElem?_eq_getElem hj]
    simp only [Option.toList_some, List.map_append, List.map_cons, List.map_nil]
    exact hsub.append (by rw [hld]; exact List.Sublist.refl _)
  · rw [hmu2]; omega
  · intro q hq
    rw [habove q (by rw [hr2]; omega)]
    exact hhigh q (by omega)
  · intro q hq h1 h2
    rw [post.below hq (by rw [hmu0]; omega) (fun hl2 => by
      obtain ⟨m0, m1, -⟩ := first_two hl2 hnd
      have := hlit _ m0; have := hlit _ m1; rw [hf.1]; omega)]
    exact hlow q hq h1 h2
  · refine hw.addClause hlayS (fun s hs => ?_) (by rw [hmu0, hf.2.2.1]; simp only [clausesAt]; omega) post
      (by rw [hmu0]; simp [Records.all]) (by rw [hmu0]; exact hp.flip_high _ (by omega)) (fun _ _ => rfl)
      (fun x hx => by rw [hf.2.2.1]; exact hshape.2.2 x hx) hnd
    rw [hf.2.2.1, hmu0]
    rcases List.mem_append.mp hs with hs | hs
    · have := hp.inputs_bounds s hs; exact ⟨this.1, by omega⟩
    · have := htb.2 s hs; exact ⟨by simp only [clausesAt]; omega, this.2⟩

/-- `keepLemmas_spec`'s conclusion for a final state `R` (and `R`'s records end below the old
`mem_used`). -/
def KeepDone (U : solver) (inputs lemmas : List Record) (F : Ptr → Bool) (R : solver) : Prop :=
  ∃ K : List Record, (∃ DB, R = { U with DB := DB, mem_used := R.mem_used, nLemmas := K.length }) ∧
    Tiling R U.mem_fixed R.mem_used K ∧ (K.map (·.2)).Sublist (lemmas.map (·.2)) ∧
    (∀ q, 0 ≤ q → q < U.mem_fixed → (q < 8 * U.nVars + 6 ∨ 10 * U.nVars + 6 < q) → R.ld q = U.ld q) ∧
    WatchLists R ⟨inputs, K, F⟩ ∧ R.mem_used ≤ U.mem_used

/-- `keepLoop` (C:78–83) from the record at `i`: the faithful `keepLemmas_spec` for the fast
loop, with `KeepInv` as the invariant. `U = abs L s0 …` is the state after the unlinking; the
loop state `db`, `mu`, `nl` stands for `abs L { s0 with db := db, memUsed := mu, nLemmas := nl } …`.
The re-added lemmas move down (`mem_used + 2 ≤ i`), so the fast `addClause` never runs out of
memory here: its result pointer can be ignored. -/
theorem keepLoop_fast {U : solver} {inputs lemmas : List Record} {F : Ptr → Bool}
    (hp : KeepPre U inputs lemmas F) {L : Lay} {s0 : St} {M fa sl : Int}
    (hU : U = abs L s0 M fa sl) (hN : NOk L.nVars) (hmu : U.mem_used ≤ 2 ^ 30)
    (hlen : 3 * lemmas.length ≤ 2 ^ 30) (oldUsed k : Cell) (hold : oldUsed.toInt = U.mem_used) :
    ∀ (n : Nat) (db : Array Cell) (mu nl i : Cell), (U.mem_used + 3 - i.toInt).toNat = n →
      db.size ≤ 2 ^ 31 →
      KeepInv U inputs lemmas F (abs L { s0 with db := db, memUsed := mu, nLemmas := nl } M fa sl) i.toInt →
      (keepLoop L db mu nl oldUsed k i).1.size ≤ 2 ^ 31 ∧
      KeepDone U inputs lemmas F (abs L { s0 with
        db := (keepLoop L db mu nl oldUsed k i).1, memUsed := (keepLoop L db mu nl oldUsed k i).2.1,
        nLemmas := (keepLoop L db mu nl oldUsed k i).2.2 } M fa sl) := by
  have hl := hp.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hfx := hp.fixed_ge; simp only [clausesAt] at hfx
  have hUn : U.nVars = L.nVars.toInt := by rw [hU]; rfl
  have hUf : U.first = L.first.toInt := by rw [hU]; rfl
  have hNn := hN.2; rw [← hUn] at hNn
  have hnz : ∀ r ∈ lemmas, ∀ l ∈ r.2, l ≠ 0 := fun r hr l hl => (hp.shape r hr).2.2 l hl |>.1
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro db mu nl i hn' hsz hinv
  rw [keepLoop.eq_1]
  by_cases hlt : i < oldUsed
  · rw [if_pos hlt]
    have hlt' : i.toInt < U.mem_used := by rw [← hold]; exact Int32.lt_iff_toInt_lt.mp hlt
    obtain ⟨j, hj, hpos, hcl⟩ := hinv.record hp hlt'
    have hlb := hp.lemmas_tile.bounds.2 _ (List.getElem_mem hj)
    have hshape := hp.shape _ (List.getElem_mem hj)
    have hnd : lemmas[j].2.Nodup :=
      List.Pairwise.of_map Int.natAbs (fun a b hab he => hab (by rw [he])) hshape.2.1
    have hlits : ∀ l ∈ lemmas[j].2, -2 ^ 29 ≤ l ∧ l ≤ 2 ^ 29 := fun l hl' => by
      have := inRange_iff.mp (hshape.2.2 l hl'); omega
    -- the loop state, from the invariant
    have hinv0 := hinv
    obtain ⟨j', hj', K, -, ⟨DB, hTeq⟩, ht, hsub, hmuK, -, -, -⟩ := hinv0
    have hmuK' : mu.toInt + 2 ≤ i.toInt := hmuK
    have hmu0 : U.mem_fixed ≤ mu.toInt := ht.bounds.1
    have hnl : nl.toInt = K.length := congrArg solver.nLemmas hTeq
    have hKl : K.length ≤ lemmas.length := by
      have := hsub.length_le; simp only [List.length_map, List.length_take] at this; omega
    -- the scan stops at the terminator (C:79)
    have hsrc : ∀ t (h : t < lemmas[j].2.length), ldA (toDB db) (i.toInt + t) = lemmas[j].2[t] := hcl.1
    have hterm : ldA (toDB db) (i.toInt + lemmas[j].2.length) = 0 := hcl.2
    have he := countLoop_end hsz (e := i.toInt + lemmas[j].2.length) (by omega) hterm _ i 0 rfl (by omega)
      (by omega) (fun q h1 h2 => by
        have ht : (q - i.toInt).toNat < lemmas[j].2.length := by omega
        have := hsrc _ ht
        rw [show i.toInt + ((q - i.toInt).toNat : Int) = q by omega] at this
        rw [this]; exact hnz _ (List.getElem_mem hj) _ (List.getElem_mem ht))
    generalize hce : countLoop db i 0 = ce at he
    obtain ⟨count, e⟩ := ce
    dsimp only at he ⊢
    have h3 : ((3 : Cell)).toInt = 3 := rfl
    have he3 : (e + 3).toInt = lemmas[j].1 + lemmas[j].2.length + 3 := by
      rw [toInt_add (by rw [h3]; omega) (by rw [h3]; omega), h3, he, hpos]
    have hinv' : KeepInv U inputs lemmas F (abs L { s0 with db := db, memUsed := mu, nLemmas := nl } M fa sl)
        lemmas[j].1 := by rw [← hpos]; exact hinv
    by_cases hk : count < k
    · -- keep the lemma (C:80–81): `addClause` copies it down to `mem_used`
      rw [if_pos hk]
      have hsize : (e - i).toInt = lemmas[j].2.length := by rw [toInt_sub (by omega) (by omega)]; omega
      have hheads : 1 < lemmas[j].2.length → ∀ t < 2, 0 ≤ L.first.toInt + lemmas[j].2[t]! ∧
          L.first.toInt + lemmas[j].2[t]! < mu.toInt ∧ (L.first.toInt + lemmas[j].2[t]! < i.toInt ∨
            i.toInt + (e - i).toInt ≤ L.first.toInt + lemmas[j].2[t]!) := fun hl2 t ht2 => by
        have hm : lemmas[j].2[t]! ∈ lemmas[j].2 := by
          rw [getElem!_pos _ t (by omega)]; exact List.getElem_mem _
        have := inRange_iff.mp (hshape.2.2 _ hm)
        refine ⟨by omega, by omega, Or.inl (by omega)⟩
      obtain ⟨-, hmu1, hsz1, post⟩ := addClause_post (L := L) (s := { s0 with db := db, memUsed := mu, nLemmas := nl })
        (M := M) (fa := fa) (sl := sl) (src := i) (size := e - i) (Ls := lemmas[j].2) false hsz hsize
        hcl.1 (by omega) (by omega) (Or.inr ⟨(by omega : 0 ≤ mu.toInt), (by omega : mu.toInt + 2 ≤ i.toInt)⟩)
        hheads (fun hl2 => (first_two hl2 hnd).2.2.1) (by omega : 0 ≤ mu.toInt)
        (by omega : mu.toInt + (e - i).toInt + 3 ≤ 2 ^ 30) (by omega) hlits
        (by omega : 0 ≤ nl.toInt ∧ nl.toInt < 2 ^ 30)
      dsimp only at post hmu1 hsz1
      generalize hac : addClause L db mu i (e - i) = ac at post hmu1 hsz1
      obtain ⟨db1, mu1, ptr⟩ := ac
      dsimp only at post hmu1 hsz1 ⊢
      have post' : AddClausePost (abs L { s0 with db := db, memUsed := mu, nLemmas := nl } M fa sl)
          lemmas[j].2 lemmas[j].2.length 0
          (abs L { s0 with db := db1, memUsed := mu1, nLemmas := nl + 1 } M fa sl, ptr.toInt) := by
        rw [← hsize]; exact post
      have hnext := KeepInv.add_of_post hj hp hinv' post'
      rw [← he3] at hnext
      exact ih _ (by omega) db1 mu1 (nl + 1) (e + 3) rfl hsz1 hnext
    · -- drop it (C:80 fails)
      rw [if_neg hk]
      have hnext := KeepInv.drop hj hp hinv'
      rw [← he3] at hnext
      exact ih _ (by omega) db mu nl (e + 3) rfl hsz hnext
  · rw [if_neg hlt]
    dsimp only
    have hge : U.mem_used ≤ i.toInt := by
      rw [← hold]; exact Int.not_lt.mp fun h => hlt (Int32.lt_iff_toInt_lt.mpr h)
    refine ⟨hsz, ?_⟩
    obtain ⟨j, hj, K, hpos, hf, ht, hsub, hmu', -, hlow, hw⟩ := hinv
    have hjl : j = lemmas.length := by
      refine Classical.byContradiction fun hne => ?_
      have hj' : j < lemmas.length := by omega
      rw [(hp.lemmas_tile.tilePos_succ j hj').2] at hpos
      have := hp.lemmas_tile.bounds.2 _ (List.getElem_mem hj'); omega
    subst hjl
    rw [List.take_length] at hsub
    rw [tilePos_length] at hpos
    exact ⟨K, hf, ht, hsub, hlow, hw, by omega⟩

/-! ### Helpers for `reduceDB_fast` -/

/-- Reading memory does not depend on the lemma counters. -/
theorem ld_with_counters (S : solver) (m n q : Int) : ({ S with maxLemmas := m, nLemmas := n } : solver).ld q = S.ld q :=
  rfl

/-- Reading the abstraction reads the fast array. (Stated once, so that proofs do not ask the
kernel to compare abstractions of different states.) -/
theorem ld_abs_eq_ldA (L : Lay) (s : St) (M fa sl q : Int) : (abs L s M fa sl).ld q = ldA (toDB s.db) q :=
  rfl

/-- Records tiling `[a, b)` take at least 3 cells each. -/
theorem tiling_three_mul_length_le {S : solver} {a b : Ptr} {rs : List Record} (h : Tiling S a b rs) :
    a + 3 * rs.length ≤ b := by
  induction h with
  | nil p => simp
  | cons hc ht ih => simp only [List.length_cons]; omega

/-- The fast `reduceDB` (C:68–83) as its three loops. -/
theorem reduceDB_unfold (L : Lay) (s : St) (k : Cell) : reduceDB L s k = { s with
    db := (keepLoop L (unlinkAll L s.db s.memFixed (-L.nVars)) s.memFixed 0 s.memUsed k (s.memFixed + 2)).1,
    memUsed := (keepLoop L (unlinkAll L s.db s.memFixed (-L.nVars)) s.memFixed 0 s.memUsed k (s.memFixed + 2)).2.1,
    nLemmas := (keepLoop L (unlinkAll L s.db s.memFixed (-L.nVars)) s.memFixed 0 s.memUsed k (s.memFixed + 2)).2.2,
    maxLemmas := raiseLoop s.nLemmas s.maxLemmas } := rfl

end MicrosatLean.Fast.Verification
