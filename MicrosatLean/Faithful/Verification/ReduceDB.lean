import MicrosatLean.Faithful.Verification.AddRecord
import MicrosatLean.Faithful.Verification.LemmaCount
import Std.Tactic.Do

/-!
# `reduceDB` (C:68–83)

At the root, `reduceDB` raises `maxLemmas` (C:69–71), unlinks every lemma from the watch
lists (C:73–77), and copies back the lemmas with fewer than `k` literals true in the
saved phase (C:78–83). The kept lemmas keep their literal order, so `Settled` still
holds. `raiseMax`, `unlinkLemmas` and `keepLemmas` name the three phases.
-/

namespace MicrosatLean.Faithful.Verification

open Std.Do
set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- C:69–71: allow more lemmas, and restart the lemma count. -/
def raiseMax (S : solver) : solver := Id.run do
  let mut S := S
  while S.nLemmas > S.maxLemmas do
    S := { S with maxLemmas := S.maxLemmas + 300 }
  S := { S with nLemmas := 0 }
  return S

/-- C:73–77: remove the lemmas' links from every watch list. -/
def unlinkLemmas (S : solver) : solver := Id.run do
  let mut S := S
  for i in (-S.nVars)...=S.nVars do
    if i == 0 then continue
    let mut watch : Ptr := S.first + i
    while S.ld watch != END do
      if S.ld watch < S.mem_fixed then
        watch := S.ld watch
      else
        S := S.st watch (S.ld (S.ld watch))
  return S

/-- C:78–83: copy back the lemmas with fewer than `k` literals true in the saved phase. -/
def keepLemmas (S : solver) (k : CInt) : solver := Id.run do
  let mut S := S
  let old_used := S.mem_used
  S := { S with mem_used := S.mem_fixed }
  let mut i : CInt := S.mem_fixed + 2
  while i < old_used do
    let mut count : CInt := 0
    let head := i
    while S.ld i != 0 do
      let lit := S.ld i
      i := i + 1
      if (if lit > 0 then 1 else 0) == S.ld (S.model + abs lit) then
        count := count + 1
    if count < k then
      S := (addClause S head (i - head) 0).1
    i := i + 3
  return S

/-- C:74–76 for one literal `i`: walk `i`'s watch list, unlinking every lemma link. -/
def unlinkList (S : solver) (i : CInt) : solver := Id.run do
  let mut S := S
  let mut watch : Ptr := S.first + i
  while S.ld watch != END do
    if S.ld watch < S.mem_fixed then
      watch := S.ld watch
    else
      S := S.st watch (S.ld (S.ld watch))
  return S

/-- `unlinkLemmas` with its inner loop named. -/
def unlinkAll (S : solver) : solver := Id.run do
  let mut S := S
  for i in (-S.nVars)...=S.nVars do
    if i == 0 then continue
    S := unlinkList S i
  return S

theorem unlinkLemmas_eq (S : solver) : unlinkLemmas S = unlinkAll S := rfl

/-- The invariant of `unlinkList`'s loop: the links `pa` are visited (the input ones kept),
`pb` are still to visit from the cursor `w`, and only the cursor cells changed. -/
def Unlinking (S : solver) (i : CInt) (links : List Ptr) (S' : solver) (w : Ptr) : Prop :=
  ∃ pa pb, links = pa ++ pb ∧ (∃ DB, S' = { S with DB := DB }) ∧
    Path S' (S.first + i) (pa.filter (· < S.mem_fixed)) w ∧ ListFrom S' w pb ∧
    ∀ q, 0 ≤ q → q ≠ S.first + i → q ∉ pa.filter (· < S.mem_fixed) → S'.ld q = S.ld q

/-- Phase 2 for one literal (C:74–76): the list keeps exactly its links below `mem_fixed`
(the input records'), and only its head and kept link cells change. -/
theorem unlinkList_spec {S : solver} {i : CInt} {links : List Ptr}
    (hl : ListFrom S (S.first + i) links) (hnd : ((S.first + i) :: links).Nodup)
    (hpos : 0 ≤ S.first + i) (hlinks : ∀ q ∈ links, 0 ≤ q) :
    (∃ DB, unlinkList S i = { S with DB := DB }) ∧
    ListFrom (unlinkList S i) (S.first + i) (links.filter (· < S.mem_fixed)) ∧
    (∀ q, 0 ≤ q → q ≠ S.first + i → q ∉ links.filter (· < S.mem_fixed) →
      (unlinkList S i).ld q = S.ld q) := by
  generalize hR : unlinkList S i = R
  apply Id.of_wp_run_eq hR
  mvcgen [unlinkList] invariants
  · fun ⟨S', w⟩ => ULift.up (linksAfter S' w).length
  · ⇓ c => match c with
      | .inl ⟨S', w⟩ => ⌜Unlinking S i links S' w⌝
      | .inr ⟨S', w⟩ => ⌜Unlinking S i links S' w ∧ S'.ld w = END⌝
  case vc1.step.isTrue.isTrue =>
    -- an input link: keep it and move the cursor (C:76, `watch = DB + *watch`)
    rename_i b m S0' w0 hc hlt hinv
    simp only [S0', w0] at hc hlt hinv ⊢
    obtain ⟨S', w⟩ := b
    simp only at hc hlt hinv ⊢
    obtain ⟨hvar, pa, pb, hsplit, ⟨DB, hS'⟩, hpath, hlf, hcells⟩ := hinv
    simp [WhileVariant.eval, SVal.evalsTo] at hvar ⊢
    have hmf : S'.mem_fixed = S.mem_fixed := by rw [hS']
    cases pb with
    | nil => simp only [ListFrom] at hlf; simp [hlf, END] at hc
    | cons x pb' =>
      have hx : S'.ld w = x := hlf.1
      have hxl : x < S.mem_fixed := by rw [← hx, ← hmf]; exact hlt
      have hpos' : ∀ q ∈ pb', 0 ≤ q := fun q hq => hlinks q (by rw [hsplit]; simp [hq])
      rw [hvar, linksAfter_eq hlf (fun q hq => hlinks q (by rw [hsplit]; simp_all)),
        hx, linksAfter_eq hlf.2 hpos']
      refine ⟨by simp, pa ++ [x], pb', by rw [hsplit]; simp, ⟨DB, hS'⟩, ?_, hlf.2, fun q hq h1 h2 => ?_⟩
      · rw [List.filter_append]; simp only [List.filter_cons, List.filter_nil, decide_eq_true hxl,
          if_true]
        exact hpath.snoc hx
      · exact hcells q hq h1 fun hm => h2 (by rw [List.filter_append]; exact List.mem_append_left _ hm)
  case vc2.step.isTrue.isFalse =>
    -- a lemma link: unlink it (C:76, `*watch = DB[*watch]`)
    rename_i b m S0' w0 hc hlt hinv
    simp only [S0', w0] at hc hlt hinv ⊢
    obtain ⟨S', w⟩ := b
    simp only at hc hlt hinv ⊢
    obtain ⟨hvar, pa, pb, hsplit, ⟨DB, hS'⟩, hpath, hlf, hcells⟩ := hinv
    simp [WhileVariant.eval, SVal.evalsTo] at hvar ⊢
    have hmf : S'.mem_fixed = S.mem_fixed := by rw [hS']
    cases pb with
    | nil => simp only [ListFrom] at hlf; simp [hlf, END] at hc
    | cons x pb' =>
      have hx : S'.ld w = x := hlf.1
      have hxl : ¬ x < S.mem_fixed := by rw [← hx, ← hmf]; exact hlt
      have hpos' : ∀ q ∈ pb', 0 ≤ q := fun q hq => hlinks q (by rw [hsplit]; simp [hq])
      have hnd' : ((S.first + i) :: (pa ++ x :: pb')).Nodup := by rw [← hsplit]; exact hnd
      have hwin : w ∈ (S.first + i) :: pa.filter (· < S.mem_fixed) := by
        rw [hpath.end_eq]; exact List.getLast_mem _
      have hsub : ((S.first + i) :: pa.filter (· < S.mem_fixed)).Sublist ((S.first + i) :: (pa ++ x :: pb')) :=
        List.Sublist.cons₂ _ ((List.filter_sublist).trans (List.sublist_append_left _ _))
      have hndw : ((S.first + i) :: pa.filter (· < S.mem_fixed)).Nodup := hnd'.sublist hsub
      have hwpos : 0 ≤ w := by
        simp only [List.mem_cons, List.mem_filter] at hwin
        rcases hwin with rfl | ⟨hm, -⟩
        · exact hpos
        · exact hlinks w (by rw [hsplit]; simp [hm])
      have hwpb : ∀ q ∈ x :: pb', q ≠ w := fun q hq he => by
        subst he
        have hm := hsub.subset hwin
        rw [List.nodup_cons] at hnd'
        simp only [List.mem_cons] at hwin
        rcases hwin with he | hwin
        · exact hnd'.1 (by rw [← he]; simp [hq])
        · have := List.nodup_append.mp hnd'.2
          exact this.2.2 _ (List.mem_filter.mp hwin).1 _ hq rfl
      have hlf' : ListFrom (S'.st w (S'.ld x)) w pb' :=
        hlf.unlink (by rw [ld_st_self _ _ hwpos])
          (fun q hq => ld_st_of_ne _ _ hwpos (hpos' q hq) (hwpb q (by simp [hq])))
          (hnd'.sublist (by simp))
      rw [hvar, linksAfter_eq hlf (fun q hq => hlinks q (by rw [hsplit]; simp_all)), hx,
        linksAfter_eq hlf' hpos']
      obtain ⟨DB', hD⟩ := st_eq S' w (S'.ld x)
      have hfilt : (pa ++ [x]).filter (· < S.mem_fixed) = pa.filter (· < S.mem_fixed) := by
        rw [List.filter_append]; simp [hxl]
      refine ⟨by simp, pa ++ [x], pb', by rw [hsplit]; simp, ⟨DB', by rw [hD, hS']⟩, ?_, hlf',
        fun q hq h1 h2 => ?_⟩
      · rw [hfilt]
        refine hpath.frame (fun q hq hqw => ?_) hndw
        have hq' : 0 ≤ q := by
          rcases hq with rfl | hq
          · exact hpos
          · exact hlinks q (by rw [hsplit]; simp [(List.mem_filter.mp hq).1])
        exact ld_st_of_ne _ _ hwpos hq' hqw
      · rw [hfilt] at h2
        have hqw : q ≠ w := fun he => by
          subst he; simp only [List.mem_cons] at hwin
          rcases hwin with he | hm
          · exact h1 he
          · exact h2 hm
        rw [ld_st_of_ne _ _ hwpos hq hqw]
        exact hcells q hq h1 h2
  case vc3.step.isFalse =>
    rename_i b m S0' w0 hc hinv
    simp only [S0', w0] at hc hinv ⊢
    exact ⟨hinv.2, by simpa using hc⟩
  case vc4.pre =>
    exact ⟨[], links, rfl, ⟨S.DB, rfl⟩, rfl, hl, fun q _ _ _ => rfl⟩
  case vc5.post.success =>
    rename_i w0 r hinv
    obtain ⟨⟨pa, pb, hsplit, hDB, hpath, hlf, hcells⟩, hend⟩ := hinv
    cases pb with
    | cons x pb' =>
      exfalso
      have := hlf.1; rw [hend] at this
      have := hlinks x (by rw [hsplit]; simp); simp [END] at *; omega
    | nil =>
      simp only [List.append_nil] at hsplit
      rw [hsplit]
      have h1 : ListFrom r.1 (S.first + i) (pa.filter (· < S.mem_fixed) ++ []) :=
        listFrom_append.mpr ⟨r.2, hpath, hend⟩
      rw [List.append_nil] at h1
      exact ⟨hDB, h1, hcells⟩

/-- Watching an input record is watching a record. -/
theorem Watches.of_inputs {db : Records} {lit link : CInt} {f : Ptr → Bool}
    (h : Watches db.inputs lit link f) : Watches db.all lit link f := by
  obtain ⟨r, hr, h2, hw⟩ := h; exact ⟨r, List.mem_append_left _ hr, h2, hw⟩

/-- `unlinkAll`'s loop after the literals `pre`: their lists hold only input links, the
other lists are unchanged, and only list heads and links of `pre` changed. -/
def UnlinkedUpTo (S : solver) (db : Records) (pre : List CInt) (S' : solver) : Prop :=
  (∃ DB, S' = { S with DB := DB }) ∧
  (∀ lit, InRange S.nVars lit → ∃ links, ListFrom S' (S.first + lit) links ∧ links.Nodup ∧
    ∀ link, link ∈ links ↔ (if lit ∈ pre then Watches db.inputs lit link db.flip
      else Watches db.all lit link db.flip)) ∧
  (∀ q, 0 ≤ q → (∀ lit ∈ pre, q ≠ S.first + lit ∧ ¬ Watches db.all lit q db.flip) → S'.ld q = S.ld q)

/-- The facts about link cells that phase 2 uses: they lie in the record region, each
watches one literal, and they belong to input records exactly below `mem_fixed`. -/
structure LinkFacts (S : solver) (db : Records) : Prop where
  ge : ∀ lit q, Watches db.all lit q db.flip → clausesAt S.nVars ≤ q
  unique : ∀ L L' q, Watches db.all L q db.flip → Watches db.all L' q db.flip → L = L'
  input_iff : ∀ lit q, Watches db.all lit q db.flip → (Watches db.inputs lit q db.flip ↔ q < S.mem_fixed)

theorem Database.linkFacts {input : Input} {S : solver} {db : Records} (hd : Database input S db)
    (hin : db.inputs ≠ []) : LinkFacts S db :=
  ⟨fun _ _ hw => Watches.link_ge hd hw, fun _ _ _ h1 h2 => hd.watches_unique h1 h2,
    fun _ _ hw => hd.watches_input_iff hin hw⟩

/-- One literal of `unlinkAll` (C:74–76). -/
theorem unlinked_step {S : solver} {db : Records} (hl : Layout S)
    (hd : LinkFacts S db) {pre : List CInt} {x : CInt} {S' : solver}
    (hx : InRange S.nVars x) (hxpre : x ∉ pre) (h : UnlinkedUpTo S db pre S') :
    UnlinkedUpTo S db (pre ++ [x]) (unlinkList S' x) := by
  obtain ⟨⟨DB, hS'⟩, hlists, hcells⟩ := h
  have hfS : S'.first = S.first ∧ S'.mem_fixed = S.mem_fixed := by rw [hS']; exact ⟨rfl, rfl⟩
  have hn := hl.num; have hn1 := hl.nVars_pos
  have hxr := inRange_iff.mp hx
  obtain ⟨lx, hlx, hndx, hmx⟩ := hlists x hx
  simp only [hxpre, if_false] at hmx
  have hge : ∀ q ∈ lx, clausesAt S.nVars ≤ q := fun q hq => hd.ge x q ((hmx q).mp hq)
  obtain ⟨⟨DB', hU⟩, hlU, hcU⟩ := unlinkList_spec (S := S') (i := x) (links := lx)
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

/-- Phase 2 (C:73–77): every watch list keeps exactly its input links; only list heads and
input link cells change. -/
theorem unlinkAll_spec {S : solver} {db : Records} (hl : Layout S)
    (hd : LinkFacts S db) (hw : WatchLists S db) :
    UnlinkedUpTo S db ((-S.nVars)...=S.nVars).toList (unlinkAll S) := by
  have hmem : ∀ v, v ∈ ((-S.nVars)...=S.nVars).toList ↔ -S.nVars ≤ v ∧ v ≤ S.nVars := by
    intro v; simp [Std.Rcc.mem_toList_iff_mem, Std.Rcc.mem_iff]
  have hnd : ((-S.nVars)...=S.nVars).toList.Nodup := Std.Rcc.nodup_toList
  generalize hR : unlinkAll S = R
  apply Id.of_wp_run_eq hR
  mvcgen [unlinkAll] invariants
  · ⇓⟨cur, S'⟩ => ⌜UnlinkedUpTo S db cur.prefix S'⌝
  case vc1.step.isTrue =>
    rename_i pre x suff hlist S' h0 hinv
    have hx0 : x = 0 := by simpa using h0
    obtain ⟨hf, hlists, hcells⟩ := hinv
    refine ⟨hf, fun lit hlit => ?_, fun q hq hall => hcells q hq fun lit hl' => hall lit (by simp [hl'])⟩
    obtain ⟨ll, hll, hndl, hml⟩ := hlists lit hlit
    have hne : lit ≠ x := by rw [hx0]; exact hlit.1
    refine ⟨ll, hll, hndl, fun link => ?_⟩
    have e := hml link
    by_cases hp : lit ∈ pre
    · rw [if_pos (by simp [hp])]; rw [if_pos hp] at e; exact e
    · rw [if_neg (by simp [hp, hne])]; rw [if_neg hp] at e; exact e
  case vc2.step.isFalse =>
    rename_i pre x suff hlist S' h0 hinv
    have hx0 : x ≠ 0 := by simpa using h0
    have hlist' : ((-S.nVars)...=S.nVars).toList = pre ++ x :: suff := hlist
    have hxr := (hmem x).mp (by rw [hlist']; simp)
    have hxpre : x ∉ pre := by
      rw [hlist'] at hnd
      exact fun hm => (List.nodup_append.mp hnd).2.2 x hm x List.mem_cons_self rfl
    exact unlinked_step hl hd (inRange_iff.mpr ⟨hx0, hxr.1, hxr.2⟩) hxpre hinv
  case vc3.pre =>
    refine ⟨⟨S.DB, rfl⟩, fun lit hlit => ?_, fun q _ _ => rfl⟩
    obtain ⟨ll, hll, hndl, hml⟩ := hw lit hlit
    exact ⟨ll, hll, hndl, fun link => by simp [hml]⟩

/-- C:79–82 for the record whose literals start at `i`: count its literals true in the
saved phase, copy it back if fewer than `k`; returns the next record's literals. -/
def keepOne (S : solver) (i k : CInt) : solver × CInt := Id.run do
  let mut S := S
  let mut i := i
  let mut count : CInt := 0
  let head := i
  while S.ld i != 0 do
    let lit := S.ld i
    i := i + 1
    if (if lit > 0 then 1 else 0) == S.ld (S.model + abs lit) then
      count := count + 1
  if count < k then
    S := (addClause S head (i - head) 0).1
  return (S, i + 3)

/-- `keepLemmas` with its loop body named. -/
def keepAll (S : solver) (k : CInt) : solver := Id.run do
  let mut S := S
  let old_used := S.mem_used
  S := { S with mem_used := S.mem_fixed }
  let mut i : CInt := S.mem_fixed + 2
  while i < old_used do
    (S, i) := keepOne S i k
  return S


/-- What `keepLemmas` starts from (after `raiseMax` and `unlinkAll`): intact records, and
watch lists holding only the input records. -/
structure KeepPre (U : solver) (inputs lemmas : List Record) (F : Ptr → Bool) : Prop where
  layout : Layout U
  inputs_bounds : ∀ r ∈ inputs, clausesAt U.nVars + 2 ≤ r.1 ∧ r.1 + r.2.length < U.mem_fixed
  lemmas_tile : Tiling U U.mem_fixed U.mem_used lemmas
  watches : WatchLists U ⟨inputs, [], F⟩
  /-- Copied-back records are linked straight (C:62–63). -/
  flip_high : ∀ p, U.mem_fixed ≤ p → F p = false
  shape : ∀ r ∈ lemmas, r.2 ≠ [] ∧ (r.2.map Int.natAbs).Nodup ∧ ∀ l ∈ r.2, InRange U.nVars l
  fixed_ge : clausesAt U.nVars ≤ U.mem_fixed
  memory : U.mem_used ≤ U.mem_max
  nLemmas : U.nLemmas = 0

/-- `keepLemmas`'s loop after the first `j` lemma records (C:79–82): the kept ones `K` are
copied to `[mem_fixed, mem_used)` and watched; the records from `i` on are intact. -/
def KeepInv (U : solver) (inputs lemmas : List Record) (F : Ptr → Bool) (S' : solver) (i : CInt) : Prop :=
  ∃ j ≤ lemmas.length, ∃ K : List Record,
    i = tilePos lemmas U.mem_used j ∧
    (∃ DB, S' = { U with DB := DB, mem_used := S'.mem_used, nLemmas := K.length }) ∧
    Tiling S' U.mem_fixed S'.mem_used K ∧
    (K.map (·.2)).Sublist ((lemmas.take j).map (·.2)) ∧
    S'.mem_used + 2 ≤ i ∧
    (∀ q, i - 2 ≤ q → S'.ld q = U.ld q) ∧
    (∀ q, 0 ≤ q → q < U.mem_fixed → (q < 8 * U.nVars + 6 ∨ 10 * U.nVars + 6 < q) → S'.ld q = U.ld q) ∧
    WatchLists S' ⟨inputs, K, F⟩

/-- Below `mem_used`, the loop is at a lemma record. -/
theorem KeepInv.record {U S' : solver} {inputs lemmas : List Record} {F : Ptr → Bool} {i : CInt}
    (hp : KeepPre U inputs lemmas F) (h : KeepInv U inputs lemmas F S' i) (hi : i < U.mem_used) :
    ∃ j, ∃ hj : j < lemmas.length, i = lemmas[j].1 ∧ ClauseAt S' i lemmas[j].2 := by
  obtain ⟨j, hj, K, hpos, -, -, -, -, hhigh, -⟩ := h
  rcases Nat.lt_or_ge j lemmas.length with hj' | hj'
  · have := (hp.lemmas_tile.tilePos_succ j hj').2
    rw [this] at hpos
    refine ⟨j, hj', hpos, ?_⟩
    have hc := hp.lemmas_tile.clauseAt (List.getElem_mem hj')
    rw [hpos]
    exact hc.frame fun q h1 _ => hhigh q (by omega)
  · have : j = lemmas.length := by omega
    subst this; rw [tilePos_length] at hpos; omega

/-- Dropping lemma record `j` (C:80 fails): move to the next record. -/
theorem KeepInv.drop {U S' : solver} {inputs lemmas : List Record} {F : Ptr → Bool} {j : Nat} (hj : j < lemmas.length)
    (hp : KeepPre U inputs lemmas F) (h : KeepInv U inputs lemmas F S' lemmas[j].1) :
    KeepInv U inputs lemmas F S' (lemmas[j].1 + lemmas[j].2.length + 3) := by
  obtain ⟨j', hj', K, hpos, hf, ht, hsub, hmu, hhigh, hlow, hw⟩ := h
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
  refine ⟨j' + 1, hj, K, (hp.lemmas_tile.tilePos_succ j' hj).1.symm, hf, ht, ?_, by omega,
    fun q hq => hhigh q (by omega), hlow, hw⟩
  rw [List.take_succ, List.getElem?_eq_getElem hj]
  simp only [Option.toList_some, List.map_append]
  exact hsub.trans (List.sublist_append_left _ _)

/-- Keeping lemma record `j` (C:80–81): `addClause` copies it to `mem_used` and watches it. -/
theorem KeepInv.add {U S' : solver} {inputs lemmas : List Record} {F : Ptr → Bool} {j : Nat} (hj : j < lemmas.length)
    (hp : KeepPre U inputs lemmas F) (h : KeepInv U inputs lemmas F S' lemmas[j].1) :
    KeepInv U inputs lemmas F (addClause S' lemmas[j].1 lemmas[j].2.length 0).1
      (lemmas[j].1 + lemmas[j].2.length + 3) := by
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
  generalize hld : lemmas[j'].2 = lits at hc0 hlb hshape hnd ⊢
  generalize hmu0 : S'.mem_used = mu at hS' ht hmu htb
  have hf : S'.first = U.first ∧ S'.mem_max = U.mem_max ∧ S'.nVars = U.nVars ∧
      S'.mem_fixed = U.mem_fixed := by rw [hS']; exact ⟨rfl, rfl, rfl, rfl⟩
  -- the record is intact in `S'` and lies above the copy target
  have hc : ClauseAt S' c lits := hc0.frame fun q h1 _ => hhigh q (by omega)
  have hlit : ∀ x ∈ lits, -U.nVars ≤ x ∧ x ≤ U.nVars := fun x hx => by
    have := inRange_iff.mp (hshape.2.2 x hx); omega
  have hfirstcells : ∀ q, 10 * U.nVars + 8 ≤ q → 1 < lits.length →
      q ≠ S'.first + lits[0]! ∧ q ≠ S'.first + lits[1]! := fun q hq hl2 => by
    obtain ⟨m0, m1, -⟩ := first_two hl2 hnd
    have := hlit _ m0; have := hlit _ m1; rw [hf.1]; omega
  have post := addClause_spec S' lits c lits.length 0 rfl (by omega) (Or.inr ⟨by omega, by omega⟩) hc.1
    (by have := hp.memory; rw [hmu0, hf.2.1]; omega)
    (fun hl2 t ht2 => by
      have hm : lits[t]! ∈ lits := by rw [getElem!_pos lits t (by omega)]; exact List.getElem_mem _
      have := hlit _ hm
      rw [hf.1, hmu0]; omega)
    (fun hl2 => (first_two hl2 hnd).2.2.1)
  generalize hr : addClause S' c lits.length 0 = r at post
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

/-- The literal scan (C:79) of the record at `c` stops at its terminator. -/
theorem scan_end {S : solver} {c i : CInt} {lits : List CInt} (hc : ClauseAt S c lits)
    (hnz : ∀ l ∈ lits, l ≠ 0) (h1 : c ≤ i) (h2 : ∀ q, c ≤ q → q < i → S.ld q ≠ 0) :
    (S.ld i ≠ 0 → i < c + lits.length) ∧ (S.ld i = 0 → i = c + lits.length) := by
  have hle : i ≤ c + lits.length := by
    refine Classical.byContradiction fun hgt => ?_
    exact h2 (c + lits.length) (by omega) (by omega) hc.2
  constructor
  · intro hne; refine Classical.byContradiction fun hge => hne ?_
    rw [show i = c + lits.length by omega]; exact hc.2
  · intro h0; refine Classical.byContradiction fun hne => ?_
    have hlt : (i - c).toNat < lits.length := by omega
    have := hc.1 _ hlt
    rw [show c + ((i - c).toNat : CInt) = i by omega, h0] at this
    exact hnz _ (List.getElem_mem hlt) this.symm

/-- Phase 3 (C:78–83): the kept lemmas, in their old order and with their literal order,
fill `[mem_fixed, mem_used)` and are watched; nothing below `mem_fixed` changes except
watch heads. -/
theorem keepLemmas_spec {U : solver} {inputs lemmas : List Record} {F : Ptr → Bool}
    (hp : KeepPre U inputs lemmas F)
    (k : CInt) :
    ∃ K : List Record,
      (∃ DB, keepLemmas U k = { U with DB := DB, mem_used := (keepLemmas U k).mem_used, nLemmas := K.length }) ∧
      Tiling (keepLemmas U k) U.mem_fixed (keepLemmas U k).mem_used K ∧
      (K.map (·.2)).Sublist (lemmas.map (·.2)) ∧
      (∀ q, 0 ≤ q → q < U.mem_fixed → (q < 8 * U.nVars + 6 ∨ 10 * U.nVars + 6 < q) →
        (keepLemmas U k).ld q = U.ld q) ∧
      WatchLists (keepLemmas U k) ⟨inputs, K, F⟩ := by
  have hnz : ∀ r ∈ lemmas, ∀ l ∈ r.2, l ≠ 0 := fun r hr l hl => (hp.shape r hr).2.2 l hl |>.1
  generalize hR : keepLemmas U k = R
  apply Id.of_wp_run_eq hR
  mvcgen [keepLemmas]
  case inv1 => exact fun ⟨_, i⟩ => ULift.up (U.mem_used + 3 - i).toNat
  case inv2 => exact ⇓ c => match c with
    | .inl ⟨S', i⟩ => ⌜KeepInv U inputs lemmas F S' i⌝
    | .inr ⟨S', i⟩ => ⌜KeepInv U inputs lemmas F S' i ∧ U.mem_used ≤ i⌝
  case inv3 => exact fun ⟨i, _⟩ => ULift.up (U.mem_used - i).toNat
  case inv4 =>
    rename_i b _ _ _ _ _
    exact ⇓ c => match c with
      | .inl ⟨i, _⟩ => ⌜b.2 ≤ i ∧ ∀ q, b.2 ≤ q → q < i → b.1.ld q ≠ 0⌝
      | .inr ⟨i, _⟩ => ⌜b.2 ≤ i ∧ (∀ q, b.2 ≤ q → q < i → b.1.ld q ≠ 0) ∧ b.1.ld i = 0⌝
  case vc1.step.isTrue.isTrue =>
    rename_i b1 _ S0 i0 hlt hout b _ i1 cnt hc lit i2 _ hin
    simp only [S0, i0, i1, i2] at hc hin hout hlt ⊢
    simp [WhileVariant.eval, SVal.evalsTo] at hin hout ⊢
    obtain ⟨hvar, hle, hcells⟩ := hin
    obtain ⟨j, hj, hpos, hcl⟩ := hout.2.record hp hlt
    have hlb := hp.lemmas_tile.bounds.2 _ (List.getElem_mem hj)
    have hnz' : b1.1.ld b.1 ≠ 0 := by simpa using hc
    have := (scan_end hcl (hnz _ (List.getElem_mem hj)) hle hcells).1 hnz'
    refine ⟨by omega, by omega, fun q h1 h2 => ?_⟩
    by_cases hq : q < b.1
    · exact hcells q h1 hq
    · rw [show q = b.1 by omega]; exact hnz'
  case vc2.step.isTrue.isFalse =>
    rename_i b1 _ S0 i0 hlt hout b _ i1 cnt hc lit i2 _ hin
    simp only [S0, i0, i1, i2] at hc hin hout hlt ⊢
    simp [WhileVariant.eval, SVal.evalsTo] at hin hout ⊢
    obtain ⟨hvar, hle, hcells⟩ := hin
    obtain ⟨j, hj, hpos, hcl⟩ := hout.2.record hp hlt
    have hlb := hp.lemmas_tile.bounds.2 _ (List.getElem_mem hj)
    have hnz' : b1.1.ld b.1 ≠ 0 := by simpa using hc
    have := (scan_end hcl (hnz _ (List.getElem_mem hj)) hle hcells).1 hnz'
    refine ⟨by omega, by omega, fun q h1 h2 => ?_⟩
    by_cases hq : q < b.1
    · exact hcells q h1 hq
    · rw [show q = b.1 by omega]; exact hnz'
  case vc3.step.isFalse =>
    rename_i b1 _ S0 i0 hlt hout b _ i1 cnt hc hin
    simp only [S0, i0, i1] at hc hin hout hlt ⊢
    obtain ⟨-, hle, hcells⟩ := hin
    exact ⟨hle, hcells, by simpa using hc⟩
  case vc4.step.isTrue.pre =>
    rename_i b1 _ S0 i0 hlt hout
    exact ⟨Int.le_refl _, fun q h1 h2 => absurd h2 (by omega)⟩
  case vc5.step.isTrue.post.success.isTrue =>
    rename_i b1 _ S0 i0 hlt hout r i1 cnt jp hk hin
    simp only [S0, i0, i1, jp] at hk hin hout hlt ⊢
    simp [WhileVariant.eval, SVal.evalsTo] at hout ⊢
    obtain ⟨hle, hcells, hzero⟩ := hin
    obtain ⟨j, hj, hpos, hcl⟩ := hout.2.record hp hlt
    have hend := (scan_end hcl (hnz _ (List.getElem_mem hj)) hle hcells).2 hzero
    have key := KeepInv.add hj hp (by rw [← hpos]; exact hout.2)
    rw [← hpos] at key
    rw [show r.1 - b1.2 = (lemmas[j].2.length : CInt) by omega, hend]
    refine ⟨by omega, ?_⟩
    rw [hpos] at key ⊢; exact key
  case vc6.step.isTrue.post.success.isFalse =>
    rename_i b1 _ S0 i0 hlt hout r i1 cnt jp hk hin
    simp only [S0, i0, i1, jp] at hk hin hout hlt ⊢
    simp [WhileVariant.eval, SVal.evalsTo] at hout ⊢
    obtain ⟨hle, hcells, hzero⟩ := hin
    obtain ⟨j, hj, hpos, hcl⟩ := hout.2.record hp hlt
    have hend := (scan_end hcl (hnz _ (List.getElem_mem hj)) hle hcells).2 hzero
    have key := KeepInv.drop hj hp (by rw [← hpos]; exact hout.2)
    rw [hend]
    refine ⟨by omega, ?_⟩
    rw [hpos]; exact key
  case vc7.step.isFalse =>
    rename_i b1 _ S0 i0 hlt hout
    simp only [S0, i0] at hlt hout ⊢
    exact ⟨hout.2, by omega⟩
  case vc8.pre =>
    rename_i S0 i0
    simp only [S0, i0]
    refine ⟨0, Nat.zero_le _, [], by rw [hp.lemmas_tile.tilePos_zero], ⟨U.DB, by simp [hp.nLemmas]⟩,
      Tiling.nil _, List.nil_sublist _, Int.le_refl _, fun q _ => rfl, fun q _ _ _ => rfl, fun lit hl => ?_⟩
    obtain ⟨links, h1, h2, h3⟩ := hp.watches lit hl
    exact ⟨links, h1.frame fun _ _ => rfl, h2, h3⟩
  case vc9.post.success =>
    rename_i S0 i0 r hinv
    obtain ⟨⟨j, hj, K, hpos, hf, ht, hsub, hmu, -, hlow, hw⟩, hend⟩ := hinv
    have hjl : j = lemmas.length := by
      refine Classical.byContradiction fun hne => ?_
      have hj' : j < lemmas.length := by omega
      rw [(hp.lemmas_tile.tilePos_succ j hj').2] at hpos
      have := hp.lemmas_tile.bounds.2 _ (List.getElem_mem hj'); omega
    subst hjl
    rw [List.take_length] at hsub
    exact ⟨K, hf, ht, hsub, hlow, hw⟩

/-- `reduceDB` is its three phases in order. -/
theorem reduceDB_eq (S : solver) (k : CInt) : reduceDB S k = keepLemmas (unlinkLemmas (raiseMax S)) k :=
  rfl

/-- Phase 1: `maxLemmas` rises past its old value (the loop runs at least once, since
`nLemmas > maxLemmas` when `reduceDB` is called), and `nLemmas` restarts at 0. -/
theorem raiseMax_spec (S : solver) (more : S.maxLemmas < S.nLemmas) :
    ∃ m, raiseMax S = { S with maxLemmas := m, nLemmas := 0 } ∧ S.maxLemmas < m := by
  generalize hR : raiseMax S = R
  apply Id.of_wp_run_eq hR
  mvcgen [raiseMax] invariants
  · fun S' => ULift.up (S'.nLemmas - S'.maxLemmas).toNat
  · ⇓ c => match c with
      | .inl S' => ⌜S' = { S with maxLemmas := S'.maxLemmas } ∧ S.maxLemmas ≤ S'.maxLemmas⌝
      | .inr S' => ⌜S' = { S with maxLemmas := S'.maxLemmas } ∧ S.nLemmas ≤ S'.maxLemmas⌝
  case vc1.step.isTrue =>
    rename_i S' m hc hinv
    obtain ⟨hvar, hS', hle⟩ := hinv
    simp [WhileVariant.eval, SVal.evalsTo] at hvar ⊢
    have hc' : S'.maxLemmas < S'.nLemmas := hc
    have hn : S'.nLemmas = S.nLemmas := by rw [hS']
    refine ⟨by omega, ?_, by omega⟩
    rw [hS']; simp
  case vc2.step.isFalse =>
    rename_i S' m hc hinv
    obtain ⟨hvar, hS', hle⟩ := hinv
    have hn : S'.nLemmas = S.nLemmas := by rw [hS']
    exact ⟨hS', by simp at hc; omega⟩
  case vc3 => constructor <;> simp
  case vc4 =>
    rename_i S' S'' hinv
    obtain ⟨hS', hle⟩ := hinv
    refine ⟨S'.maxLemmas, ?_, by omega⟩
    show ({ S' with nLemmas := 0 } : solver) = _
    apply solver.ext <;> (try rw [hS']) <;> rfl

/-- `Settled` carries over to a state with the same trail (cells below `first` and trail
fields), at the root, and a new database whose records reuse old literal lists. Used for
`reduceDB`, which only changes the record region and the watch heads. -/
theorem Settled.rebuild {input : Input} {S R : solver} {db db' : Records} {vs : List CInt}
    (h : Settled input S db vs) (root : trailLen S = forcedPos S) (hs : SameShape S R)
    (hf : R.forced = S.forced ∧ R.processed = S.processed ∧ R.assigned = S.assigned ∧
      R.head = S.head ∧ R.mem_max = S.mem_max)
    (hml : 0 ≤ R.maxLemmas)
    (low : ∀ q, 0 ≤ q → q < 8 * S.nVars + 6 → R.ld q = S.ld q)
    (sent : R.ld (clausesAt S.nVars - 1) = S.ld (clausesAt S.nVars - 1))
    (hdb : Database input R db') (hw : WatchLists R db')
    (hsub : ∀ r ∈ db'.all, ∃ r0 ∈ db.all, r0.2 = r.2) :
    Settled input R db' vs := by
  have core := h.core; have hl := core.layout; have hn := hl.num; have ht := core.trail
  have hn1 := hl.nVars_pos
  have hlen := ht.len_le
  have hA := ht.assigned_le; have hP := ht.processed_le; have hF := ht.forced_le
  obtain ⟨hFo, hPr, hAs, hH, hMM⟩ := hf
  have htl : trailLen R = trailLen S := by simp only [trailLen, hAs, hs.falseStack]
  have hfp : forcedPos R = forcedPos S := by simp only [forcedPos, hFo, hs.falseStack]
  have hpp : processedPos R = processedPos S := by simp only [processedPos, hPr, hs.falseStack]
  have hlen' : (S.assigned - S.falseStack).toNat ≤ S.nVars.toNat := hlen
  have htr : ∀ i < trailLen S, trailAt R i = trailAt S i := fun i hi => by
    simp only [trailLen] at hi
    simp only [trailAt, hs.falseStack]; exact low _ (by omega) (by omega)
  have hflag : ∀ lit, -S.nVars ≤ lit → lit ≤ S.nVars → flag R lit = flag S lit := fun lit h1 h2 => by
    simp only [flag, hs.false]; exact low _ (by omega) (by omega)
  have hrs : ∀ lit, -S.nVars ≤ lit → lit ≤ S.nVars → reasonOf R lit = reasonOf S lit := fun lit h1 h2 => by
    simp only [reasonOf, hs.reason]
    exact low _ (by rcases abs_cases lit with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
      (by rcases abs_cases lit with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
  have hlitS : ∀ i < trailLen S, -S.nVars ≤ trailAt S i ∧ trailAt S i ≤ S.nVars := fun i hi => by
    have := inRange_iff.mp (ht.lit i hi); omega
  have hdec : ∀ i < trailLen S, (IsDecision R i ↔ IsDecision S i) := fun i hi => by
    simp only [IsDecision]; rw [htr i hi, hrs _ (hlitS i hi).1 (hlitS i hi).2]
  have hroot : ∀ i < trailLen S, (RootLevel R i ↔ RootLevel S i) := fun i hi =>
    ⟨fun h' k hk => (not_congr (hdec k (by omega))).mp (h' k hk),
     fun h' k hk => (not_congr (hdec k (by omega))).mpr (h' k hk)⟩
  have hfa : ∀ {lit : CInt} {j : Nat}, FalseAt R lit j ↔ FalseAt S lit j := by
    intro lit j
    constructor
    · rintro ⟨hj, he⟩; rw [htl] at hj; exact ⟨hj, by rw [← htr j hj]; exact he⟩
    · rintro ⟨hj, he⟩; exact ⟨by rw [htl]; exact hj, by rw [htr j hj]; exact he⟩
  have hsl : ∀ p q, q < trailLen S → (SameOrLowerLevel R p q ↔ SameOrLowerLevel S p q) := fun p q hq =>
    ⟨fun h' k h1 h2 => (not_congr (hdec k (by omega))).mp (h' k h1 h2),
     fun h' k h1 h2 => (not_congr (hdec k (by omega))).mpr (h' k h1 h2)⟩
  have htrail : Trail R := by
    refine ⟨by rw [hFo, hs.falseStack]; exact hF, by rw [hFo, hPr]; exact hP, by rw [hPr, hAs]; exact hA,
      by rw [htl, hs.nVars]; exact hlen, fun i hi => ?_, fun i hi j hj he => ?_, fun i hi hr => ?_,
      fun i hi hr => ?_, fun lit hl' hoff => ?_, fun i hi => ?_, ?_, fun i hi => ?_⟩
    · rw [htl] at hi; rw [htr i hi, hs.nVars]; exact ht.lit i hi
    · rw [htl] at hi hj; rw [htr i hi, htr j hj] at he; exact ht.distinct i hi j hj he
    · rw [htl] at hi
      rw [htr i hi, hflag _ (hlitS i hi).1 (hlitS i hi).2]; exact ht.flag_root i hi ((hroot i hi).mp hr)
    · rw [htl] at hi
      rw [htr i hi, hflag _ (hlitS i hi).1 (hlitS i hi).2]
      exact ht.flag_level i hi fun h' => hr ((hroot i hi).mpr h')
    · rw [hs.nVars] at hl'
      have := inRange_iff.mp hl'
      rw [hflag _ this.2.1 this.2.2]
      exact ht.flag_off lit hl' fun i hi he => hoff i (by rw [htl]; exact hi) (by rw [htr i hi]; exact he)
    · rw [htl] at hi
      have := hlitS i hi
      rw [htr i hi, hs.model, low _ (by rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
        (by rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)]
      exact ht.model i hi
    · rw [hflag 0 (by omega) (by omega)]; exact ht.flag_zero
    · rw [hfp] at hi
      have hfl : forcedPos S ≤ trailLen S := by omega
      exact (hroot i (by omega)).mpr (ht.forced_root i hi)
  refine ⟨⟨core.valid, by rw [hs.nVars]; exact core.nVars, by rw [hMM]; exact core.memory, hml,
    hl.frame hs sent, htrail, ?_, hdb, hw, ?_, ?_, core.order.frame hl hs hH fun q h1 h2 => low q (by omega) (by omega)⟩,
    ?_, by rw [hPr, hAs]; exact h.processed, ?_⟩
  · intro i hi hr; rw [htl] at hi; rw [htr i hi]; exact core.root i hi ((hroot i hi).mp hr)
  · intro i hi hfi; rw [htl] at hi; rw [hfp] at hfi; omega
  · intro r hr h1
    obtain ⟨r0, hr0, he⟩ := hsub r hr
    obtain ⟨i, hi, hrt, hti⟩ := core.units r0 hr0 (by rw [he]; exact h1)
    exact ⟨i, by rw [htl]; exact hi, (hroot i hi).mpr hrt, by rw [htr i hi, hti, he]⟩
  · intro r hr h2 w o hwo p hp hfa'
    obtain ⟨r0, hr0, he⟩ := hsub r hr
    rw [hpp] at hp
    obtain ⟨q, hq, hsl'⟩ := h.watched r0 hr0 (by rw [he]; exact h2) w o hwo p hp (by rw [he]; exact hfa.mp hfa')
    rw [he] at hq
    exact ⟨q, hfa.mpr hq, (hsl p q hq.1).mpr hsl'⟩
  · intro i hi hr; rw [htl] at hi; rw [hfp]; exact h.root_below i hi ((hroot i hi).mp hr)

/-- `reduceDB` keeps `Settled` (with a smaller lemma list) and raises `maxLemmas`.
It is called at the root (after `restart`) when `nLemmas > maxLemmas` (C:171). Used by
`afterConflict_spec`. -/
theorem reduceDB_spec {input : Input} {S : solver} {db : Records} {vs : List CInt} (k : CInt)
    (h : Settled input S db vs) (root : trailLen S = forcedPos S) (more : S.maxLemmas < S.nLemmas) :
    ∃ db', Settled input (reduceDB S k) db' vs ∧ S.maxLemmas < (reduceDB S k).maxLemmas ∧
      (reduceDB S k).head = S.head := by
  have core := h.core; have hd := core.database; have hl := core.layout
  have hn := hl.num; have hn1 := hl.nVars_pos
  have hml0 := core.maxLemmas
  -- there are lemmas (`nLemmas > maxLemmas ≥ 0`), hence input records
  have hlem : db.lemmas ≠ [] := fun he => by have := hd.nLemmas; rw [he] at this; simp at this; omega
  have hin : db.inputs ≠ [] := fun he => hlem (hd.no_lemmas he)
  have hst : lemmasStart S db = S.mem_fixed := by simp [lemmasStart, hin]
  have hb1 := hd.inputs_tile.bounds; have hb2 := hd.lemmas_tile.bounds
  rw [hst] at hb1 hb2
  have hmf : clausesAt S.nVars ≤ S.mem_fixed := hb1.1
  have hmf' : 10 * S.nVars + 8 ≤ S.mem_fixed := by simp only [clausesAt] at hmf; exact hmf
  rw [reduceDB_eq, unlinkLemmas_eq]
  obtain ⟨m, hraise, hm⟩ := raiseMax_spec S more
  rw [hraise]
  -- phase 2 on `S1`, which differs from `S` only in its counters
  have hl1 : Layout ({ S with maxLemmas := m, nLemmas := 0 } : solver) :=
    hl.frame ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ rfl
  have hw1 : WatchLists ({ S with maxLemmas := m, nLemmas := 0 } : solver) db := fun lit hlit => by
    obtain ⟨links, h1, h2, h3⟩ := core.watches lit hlit
    exact ⟨links, h1.frame fun _ _ => rfl, h2, h3⟩
  have hlf : LinkFacts ({ S with maxLemmas := m, nLemmas := 0 } : solver) db :=
    let h' := hd.linkFacts hin; ⟨h'.1, h'.2, h'.3⟩
  obtain ⟨⟨DB2, hU⟩, hlists, hcells⟩ := unlinkAll_spec hl1 hlf hw1
  generalize hUd : unlinkAll ({ S with maxLemmas := m, nLemmas := 0 } : solver) = U at hU hlists hcells
  -- cells outside the watch heads and links are unchanged by phase 2
  have hUS : ∀ q, 0 ≤ q → (q < 8 * S.nVars + 6 ∨ 10 * S.nVars + 6 < q) →
      (∀ lit, ¬ Watches db.all lit q db.flip) →
      U.ld q = S.ld q := fun q h0 h1 h2 => hcells q h0 fun lit hl' => by
    have := (Std.Rcc.mem_toList_iff_mem.mp hl'); simp only [Std.Rcc.mem_iff] at this
    have hb : -S.nVars ≤ lit ∧ lit ≤ S.nVars := this
    exact ⟨by show q ≠ S.first + lit; omega, h2 lit⟩
  have hUf : U.nVars = S.nVars ∧ U.mem_fixed = S.mem_fixed ∧ U.mem_used = S.mem_used ∧
      U.mem_max = S.mem_max ∧ U.nLemmas = 0 ∧ U.maxLemmas = m := by rw [hU]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hshapeU : SameShape S U := by rw [hU]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hrecU : ∀ r ∈ db.all, ∀ q, RecordCell r q → U.ld q = S.ld q := fun r hr q hq => by
    have := hd.record_ge hr; simp only [RecordCell] at hq
    exact hUS q (by simp only [clausesAt] at this; omega) (Or.inr (by simp only [clausesAt] at this; omega))
      fun lit => hd.link_not_record hr hq
  have hsentU : U.ld (clausesAt S.nVars - 1) = S.ld (clausesAt S.nVars - 1) :=
    hUS _ (by simp only [clausesAt]; omega) (Or.inr (by simp only [clausesAt]; omega))
      fun lit hw => by have := Watches.link_ge hd hw; omega
  -- inputs keep their orientation; copied-back lemmas are straight
  let F : Ptr → Bool := fun p => if p < S.mem_fixed then db.flip p else false
  have hFin : ∀ r ∈ db.inputs, F r.1 = db.flip r.1 := fun r hr => by
    have := hb1.2 r hr; simp only [F]; rw [if_pos (by omega)]
  have hpre : KeepPre U db.inputs db.lemmas F := by
    refine ⟨hl.frame hshapeU hsentU, fun r hr => ?_, ?_, fun lit hlit => ?_,
      fun p hp' => by rw [hUf.2.1] at hp'; simp only [F]; rw [if_neg (by omega)], fun r hr => ?_,
      by rw [hUf.1, hUf.2.1]; exact hmf, by rw [hUf.2.2.1, hUf.2.2.2.1]; exact core.used_le_max, hUf.2.2.2.2.1⟩
    · rw [hUf.1, hUf.2.1]; exact hb1.2 r hr
    · rw [hUf.2.1, hUf.2.2.1, ← hst]
      exact hd.lemmas_tile.frame fun r hr q hq => hrecU r (List.mem_append_right _ hr) q hq
    · rw [hUf.1] at hlit
      obtain ⟨links, h1, h2, h3⟩ := hlists lit hlit
      have hmemr : lit ∈ ((-S.nVars)...=S.nVars).toList := by
        have := inRange_iff.mp hlit
        simp only [Std.Rcc.mem_toList_iff_mem, Std.Rcc.mem_iff]; omega
      refine ⟨links, by rw [hshapeU.first]; exact h1, h2, fun link => ?_⟩
      rw [h3 link]; simp only [hmemr, if_true, records_all_inputs]
      exact (Watches.congr_flip fun r hr => (hFin r hr).symm)
    · have := hd.lemma_shape r hr; rw [hUf.1]; exact ⟨this.1, this.2.1, this.2.2⟩
  -- phase 3
  obtain ⟨K, ⟨DB3, hR⟩, htK, hsubK, hlowK, hwK⟩ := keepLemmas_spec hpre k
  generalize hRd : keepLemmas U k = R at hR htK hlowK hwK
  have hRf : R.nVars = S.nVars ∧ R.mem_fixed = S.mem_fixed ∧ R.nLemmas = K.length ∧ R.maxLemmas = m ∧
      R.forced = S.forced ∧ R.processed = S.processed ∧ R.assigned = S.assigned ∧ R.head = S.head ∧
      R.mem_max = S.mem_max := by
    rw [hR, hU]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hshapeR : SameShape S R := by rw [hR, hU]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hRS : ∀ q, 0 ≤ q → q < S.mem_fixed → (q < 8 * S.nVars + 6 ∨ 10 * S.nVars + 6 < q) →
      (∀ lit, ¬ Watches db.all lit q db.flip) → R.ld q = S.ld q := fun q h0 h1 h2 h3 => by
    rw [hlowK q h0 (by rw [hUf.2.1]; exact h1) (by rw [hUf.1]; exact h2)]; exact hUS q h0 h2 h3
  -- the kept lemmas reuse old literal lists
  have hK : ∀ r ∈ K, ∃ r0 ∈ db.lemmas, r0.2 = r.2 := fun r hr => by
    have := hsubK.subset (List.mem_map_of_mem (f := (·.2)) hr)
    obtain ⟨r0, hr0, he⟩ := List.mem_map.mp this
    exact ⟨r0, hr0, he⟩
  have hdb : Database input R ⟨db.inputs, K, F⟩ := by
    have hstR : lemmasStart R ⟨db.inputs, K, F⟩ = S.mem_fixed := by simp [lemmasStart, hin, hRf.2.1]
    refine ⟨?_, ?_, hd.inputs_length, hd.inputs_perm, hd.inputs_nonempty, fun he => absurd he hin,
      by rw [hRf.2.2.1], fun r hr => ?_, fun r hr => ?_, ?_⟩
    · rw [hstR, hshapeR.nVars]
      have := hd.inputs_tile; rw [hst] at this
      exact this.frame fun r hr q hq => by
        have hrb := hb1.2 r hr; simp only [RecordCell] at hq
        exact hRS q (by simp only [clausesAt] at hrb; omega) (by omega)
          (Or.inr (by simp only [clausesAt] at hrb; omega)) fun lit => hd.link_not_record
          (List.mem_append_left _ hr) hq
    · rw [hstR]; rw [hUf.2.1] at htK; exact htK
    · obtain ⟨r0, hr0, he⟩ := hK r hr; rw [hRf.1, ← he]; exact hd.lemma_shape r0 hr0
    · obtain ⟨r0, hr0, he⟩ := hK r hr; rw [← he]; exact hd.lemma_entailed r0 hr0
    · have hp : (db.lemmas.map (·.2)).Pairwise (fun a b => ¬ a.Perm b) := by
        rw [List.pairwise_map]; exact hd.lemma_distinct
      have := hp.sublist hsubK
      rw [List.pairwise_map] at this; exact this
  refine ⟨⟨db.inputs, K, F⟩, h.rebuild root hshapeR ⟨hRf.2.2.2.2.1, hRf.2.2.2.2.2.1, hRf.2.2.2.2.2.2.1,
      hRf.2.2.2.2.2.2.2.1, hRf.2.2.2.2.2.2.2.2⟩ (by rw [hRf.2.2.2.1]; omega)
      (fun q h0 h1 => hRS q h0 (by omega) (Or.inl h1) fun lit hw => by
        have := Watches.link_ge hd hw; simp only [clausesAt] at this; omega)
      (hRS _ (by simp only [clausesAt]; omega) (by simp only [clausesAt]; omega)
        (Or.inr (by simp only [clausesAt]; omega)) fun lit hw => by have := Watches.link_ge hd hw; omega)
      hdb hwK fun r hr => ?_, by rw [hRf.2.2.2.1]; exact hm, hRf.2.2.2.2.2.2.2.1⟩
  rcases List.mem_append.mp hr with hr | hr
  · exact ⟨r, List.mem_append_left _ hr, rfl⟩
  · obtain ⟨r0, hr0, he⟩ := hK r hr; exact ⟨r0, List.mem_append_right _ hr0, he⟩

end MicrosatLean.Faithful.Verification
