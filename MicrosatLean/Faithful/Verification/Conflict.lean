import MicrosatLean.Faithful.Verification.AnalyzeLoop

/-!
# A conflict below the root (C:155–158)

The visited clause is false and `forced` is not set: `analyze` learns a lemma and
backjumps, and `propagate` assigns the lemma's asserting literal (setting `forced` for a
unit lemma) and leaves the watch loop.
-/

namespace MicrosatLean.Faithful.Verification

/-- `A`'s trail is `T`'s cut at position `B`, with the same reasons and `forced`. -/
structure TrailCut (T A : solver) (B : Nat) : Prop where
  len : trailLen A = B
  le : B ≤ trailLen T
  at_eq : ∀ i < B, trailAt A i = trailAt T i
  reason_eq : ∀ i < B, reasonOf A (trailAt T i) = reasonOf T (trailAt T i)
  forced : forcedPos A = forcedPos T

section
variable {T A : solver} {B : Nat}

/-- Decisions below the cut are `T`'s. -/
theorem TrailCut.isDecision (h : TrailCut T A B) {i : Nat} (hi : i < B) :
    IsDecision A i ↔ IsDecision T i := by
  simp only [IsDecision, h.at_eq i hi, h.reason_eq i hi]

/-- Root positions below the cut are `T`'s. -/
theorem TrailCut.rootLevel (h : TrailCut T A B) {i : Nat} (hi : i < B) :
    RootLevel A i ↔ RootLevel T i :=
  ⟨fun h' k hk => (not_congr (h.isDecision (by omega))).mp (h' k hk),
   fun h' k hk => (not_congr (h.isDecision (by omega))).mpr (h' k hk)⟩

/-- `A`'s false literals are `T`'s below the cut. -/
theorem TrailCut.falseAt (h : TrailCut T A B) {l : CInt} {j : Nat} :
    FalseAt A l j ↔ FalseAt T l j ∧ j < B := by
  have := h.le
  constructor
  · rintro ⟨hj, he⟩
    rw [h.len] at hj
    exact ⟨⟨by omega, by rw [← h.at_eq j hj]; exact he⟩, hj⟩
  · rintro ⟨⟨_, he⟩, hj⟩
    exact ⟨by rw [h.len]; exact hj, by rw [h.at_eq j hj]; exact he⟩

/-- Levels below the cut are `T`'s. -/
theorem TrailCut.sameLevel (h : TrailCut T A B) {p q : Nat} (hq : q < B) :
    SameOrLowerLevel A p q ↔ SameOrLowerLevel T p q :=
  ⟨fun h' k h1 h2 => (not_congr (h.isDecision (by omega))).mp (h' k h1 h2),
   fun h' k h1 h2 => (not_congr (h.isDecision (by omega))).mpr (h' k h1 h2)⟩

/-- Reasons below the cut stay. -/
theorem TrailCut.reasons {db : Records} (h : TrailCut T A B) (hr : Reasons T db) : Reasons A db := by
  have := h.le
  intro i hi hfi hrn
  rw [h.len] at hi
  rw [h.forced] at hfi
  rw [h.at_eq i hi, h.reason_eq i hi] at hrn ⊢
  obtain ⟨s, hs, e1, e2, e3, e4⟩ := hr i (by omega) hfi hrn
  refine ⟨s, hs, e1, e2, fun l hl => ?_, fun hnr => ?_⟩
  · obtain ⟨j, hj, hfa⟩ := e3 l hl
    exact ⟨j, hj, h.falseAt.mpr ⟨hfa, by omega⟩⟩
  · obtain ⟨l, hl, j, hj, hfa, hsl⟩ := e4 fun h' => hnr ((h.rootLevel hi).mpr h')
    exact ⟨l, hl, j, hj, h.falseAt.mpr ⟨hfa, by omega⟩, (h.sameLevel hi).mpr hsl⟩

/-- Root literals below the cut stay entailed. -/
theorem TrailCut.root {input : Input} (h : TrailCut T A B) (hr : RootEntailed input T) :
    RootEntailed input A := by
  have := h.le
  intro i hi hroot
  rw [h.len] at hi
  rw [h.at_eq i hi]
  exact hr i (by omega) ((h.rootLevel hi).mp hroot)

/-- True units stay true when the root is below the cut. -/
theorem TrailCut.units {db : Records} (h : TrailCut T A B) (hu : UnitsTrue T db)
    (hb : ∀ i < trailLen T, RootLevel T i → i < B) : UnitsTrue A db := by
  intro s hs h1
  obtain ⟨i, hi, hroot, he⟩ := hu s hs h1
  have hiB := hb i hi hroot
  exact ⟨i, by rw [h.len]; exact hiB, (h.rootLevel hiB).mpr hroot, by rw [h.at_eq i hiB]; exact he⟩

/-- A cut followed by a change above the trail arrays is a cut. -/
theorem TrailCut.low {A2 : solver} (h : TrailCut T A B) (hlow : LowSame A A2) (ht : Trail A)
    (hl : Layout A) : TrailCut T A2 B := by
  have hlen := h.len
  refine ⟨by rw [hlow.trailLen ht hl, hlen], h.le, fun i hi => ?_, fun i hi => ?_,
    by rw [hlow.forcedPos ht hl, h.forced]⟩
  · rw [hlow.trailAt ht hl (by omega), h.at_eq i hi]
  · have := inRange_iff.mp (ht.lit i (by omega))
    rw [h.at_eq i hi] at this
    rw [hlow.reasonOf ht hl this.2.1 this.2.2, h.reason_eq i hi]

end

/-- The state `analyzeCore` leaves: `T`'s trail cut at `B`, with `T`'s layout, records,
watch lists and counters. -/
theorem Analyzed.state {input : Input} {T : solver} {db : Records} {vs : List CInt} {A : solver}
    {size : CInt} {L vs' : List CInt} {B : Nat} (h : Analyzed input T db A size L vs' B)
    (core : Core input T db vs) :
    TrailCut T A B ∧ SameShape T A ∧ Layout A ∧ Trail A ∧ Database input A db ∧ WatchLists A db ∧
    A.mem_used = T.mem_used ∧ A.mem_max = T.mem_max ∧ A.nLemmas = T.nLemmas ∧
    A.maxLemmas = T.maxLemmas ∧ A.processed = T.falseStack + B := by
  obtain ⟨DB, hh, hr, nc, fa, sl, hS⟩ := h.fields
  have ht := core.trail; have hl := core.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hcut := h.cut
  have hshape : SameShape T A := by rw [hS]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hfst : A.falseStack = T.falseStack := by rw [hS]
  have hforced : A.forced = T.forced := by rw [hS]
  have hasg : A.assigned = T.falseStack + B := by rw [hS]
  have hproc : A.processed = T.falseStack + B := by rw [hS]
  have hlen : trailLen A = B := by simp only [trailLen, hasg, hfst]; omega
  have hfp : forcedPos A = forcedPos T := by simp only [forcedPos, hforced, hfst]
  have cut : TrailCut T A B := ⟨hlen, by omega, h.trail_eq, h.reason_eq, hfp⟩
  have hfle : forcedPos T ≤ B := hcut.2.1
  have htr : Trail A := by
    have h1 := ht.forced_le; have h3 := ht.len_le
    refine ⟨by rw [hforced, hfst]; exact h1, ?_, by rw [hproc, hasg]; exact Int.le_refl _, ?_, fun i hi => ?_,
      fun i hi j hj he => ?_, fun i hi hr => ?_, fun i hi hr => ?_, fun lit hlit hoff => ?_,
      fun i hi => ?_, h.flag_zero, fun i hi => ?_⟩
    · rw [hforced, hproc]; simp only [forcedPos] at hfle; omega
    · rw [hlen, hshape.nVars]; have : B < trailLen T := hcut.1; omega
    · rw [hlen] at hi; rw [h.trail_eq i hi, hshape.nVars]; exact ht.lit i (by omega)
    · rw [hlen] at hi hj; rw [h.trail_eq i hi, h.trail_eq j hj] at he
      exact ht.distinct i (by omega) j (by omega) he
    · rw [hlen] at hi; rw [h.trail_eq i hi]; exact h.flag_root i hi ((cut.rootLevel hi).mp hr)
    · rw [hlen] at hi; rw [h.trail_eq i hi]
      exact h.flag_level i hi fun h' => hr ((cut.rootLevel hi).mpr h')
    · rw [hshape.nVars] at hlit; rw [hlen] at hoff
      exact h.flags_off lit hlit fun i hi he => hoff i hi (by rw [h.trail_eq i hi]; exact he)
    · rw [hlen] at hi; rw [h.trail_eq i hi, h.model_eq i hi]; exact ht.model i (by omega)
    · rw [hfp] at hi; exact (cut.rootLevel (by omega)).mpr (ht.forced_root i hi)
  refine ⟨cut, hshape, hl.frame hshape (h.high _ (by simp only [clausesAt]; omega)), htr,
    core.database.frame hshape (by rw [hS]) (by rw [hS]) (by rw [hS])
      fun q hq => h.high q (by simp only [clausesAt] at hq; omega),
    core.watches.frame hl core.database hshape h.high, by rw [hS], by rw [hS], by rw [hS], by rw [hS],
    hproc⟩

/-- `addClause` stores the learned lemma after the records (C:130): the database gains it as
its last lemma, watched by its first two literals; the trail arrays are untouched. -/
theorem Analyzed.add {input : Input} {T : solver} {db : Records} {vs : List CInt} {A : solver}
    {size : CInt} {L vs' : List CInt} {B : Nat} (h : Analyzed input T db A size L vs' B)
    (core : Core input T db vs) (hin : db.inputs ≠ []) :
    ∃ db'' : Records, db''.all = db.all ++ [((addClause A A.buffer size 0).2, L)] ∧
      0 ≤ (addClause A A.buffer size 0).2 ∧
      LowSame A (addClause A A.buffer size 0).1 ∧ Layout (addClause A A.buffer size 0).1 ∧
      Database input (addClause A A.buffer size 0).1 db'' ∧
      WatchLists (addClause A A.buffer size 0).1 db'' ∧
      (addClause A A.buffer size 0).1.ld (addClause A A.buffer size 0).2 = L[0]! ∧
      ((addClause A A.buffer size 0).1.ld ((addClause A A.buffer size 0).2 + 1) = 0 ↔ L.length = 1) ∧
      (addClause A A.buffer size 0).1.nLemmas = A.nLemmas + 1 ∧
      (addClause A A.buffer size 0).1.maxLemmas = A.maxLemmas ∧
      (addClause A A.buffer size 0).1.mem_max = A.mem_max ∧
      (addClause A A.buffer size 0).1.head = A.head := by
  obtain ⟨-, hshape, hlA, -, hdA, hwA, hmu, hmax, -, -, -⟩ := h.state core
  have hl := core.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hnA := hlA.num; have hsn := hshape.nVars
  have hd := core.database
  have hsize := h.size_eq
  have hnd : L.Nodup := List.Pairwise.of_map Int.natAbs (fun a b hab he => hab (by rw [he])) h.shape.1
  have hlitA : ∀ l ∈ L, InRange A.nVars l := fun l hl' => by rw [hsn]; exact h.shape.2 l hl'
  have hlenL := clause_length_le h.shape.1 h.shape.2
  have hpos : 0 < L.length := List.length_pos_iff.mpr h.nonempty
  have hu : clausesAt A.nVars ≤ A.mem_used := by
    have b1 := hdA.inputs_tile.bounds; have b2 := hdA.lemmas_tile.bounds; omega
  have hu' : 10 * A.nVars + 8 ≤ A.mem_used := hu
  have hmem : A.mem_used + size + 3 ≤ A.mem_max := by
    have hsz := lemmas_size_le hl.nVars_pos (L := db.lemmas ++ [(0, L)])
      (fun s hs => by
        rcases List.mem_append.mp hs with hs | hs
        · exact ⟨(hd.lemma_shape s hs).2.1, (hd.lemma_shape s hs).2.2⟩
        · simp only [List.mem_singleton] at hs; subst hs; exact h.shape)
      (List.pairwise_append.mpr ⟨hd.lemma_distinct, List.pairwise_singleton _ _, fun a ha b hb => by
        simp only [List.mem_singleton] at hb; subst hb; exact h.new a (List.mem_append_right _ ha)⟩)
    simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil] at hsz
    have hm := core.memory
    simp only [memoryBound] at hm
    rw [← core.nVars] at hm
    have := core.used_le_bound
    rw [hmu, hmax, hsize]; omega
  have hheads : 1 < L.length → ∀ i < 2, 0 ≤ A.first + L[i]! ∧ A.first + L[i]! < A.mem_used ∧
      (A.first + L[i]! < A.buffer ∨ A.buffer + size ≤ A.first + L[i]!) := fun h2 i hi => by
    have hm : L[i]! ∈ L := by rw [getElem!_pos L i (by omega)]; exact List.getElem_mem _
    have := inRange_iff.mp (hlitA _ hm)
    omega
  have hhd : ∀ q, (q < 8 * A.nVars + 6 ∨ 10 * A.nVars + 7 ≤ q) → 1 < L.length →
      q ≠ A.first + L[0]! ∧ q ≠ A.first + L[1]! :=
    fun q hq h2 => by
      have m0 := inRange_iff.mp (hlitA _ (first_two h2 hnd).1)
      have m1 := inRange_iff.mp (hlitA _ (first_two h2 hnd).2.1)
      omega
  have post := addClause_spec A L A.buffer size 0 hsize (by omega) (Or.inl (by omega))
    h.buffer_eq hmem hheads fun h2 => (first_two h2 hnd).2.2.1
  generalize hRd : addClause A A.buffer size 0 = R at post ⊢
  obtain ⟨hr2, -, hlits, hterm, -, -, DB, hR⟩ := id post
  have hshape2 := post.shape
  have hlow : LowSame A R.1 := ⟨hshape2, by rw [hR]; rfl, by rw [hR]; rfl, by rw [hR]; rfl,
    fun q h0 h1 => post.below h0 (by omega) (hhd q (Or.inl h1))⟩
  have hdb := hdA.addLemma (fun p => if p = A.mem_used + 2 then false else db.flip p) hlA post hsize hin
    ⟨h.nonempty, h.shape.1, hlitA⟩ h.entailed fun s hs => h.new s (List.mem_append_right _ hs)
  have hall : (⟨db.inputs, db.lemmas ++ [(A.mem_used + 2, L)],
      fun p => if p = A.mem_used + 2 then false else db.flip p⟩ : Records).all =
      db.all ++ [(A.mem_used + 2, L)] := by simp [Records.all]
  have hwl := hwA.addClause hlA (fun s hs => hdA.record_ge hs) hu post hall (by simp)
    (fun s hs => by have := hdA.record_ge hs; simp [show s.1 ≠ A.mem_used + 2 by omega]) hlitA hnd
  refine ⟨_, by rw [hall, hr2], by omega, hlow,
    hlA.frame hshape2 (post.below (by simp only [clausesAt]; omega) (by simp only [clausesAt]; omega)
      (hhd _ (Or.inr (by simp only [clausesAt]; omega)))), hdb, hwl, ?_, ?_,
    by rw [hR]; simp [added], by rw [hR]; rfl, by rw [hR]; rfl, by rw [hR]; rfl⟩
  · rw [getElem!_pos L 0 hpos]; simpa using hlits 0 hpos
  · constructor
    · intro h0
      refine Classical.byContradiction fun hne => ?_
      have h2 : 1 < L.length := by omega
      have := hlits 1 h2
      rw [show R.2 + ((1 : Nat) : CInt) = R.2 + 1 by omega] at this
      rw [this] at h0
      exact (inRange_iff.mp (hlitA _ (List.getElem_mem h2))).1 h0
    · intro h1
      have := hterm
      rw [hsize, h1] at this
      simpa using this

/-- After the analysis, `addClause` and `assign` (C:130, C:157–158): the learned lemma is
stored, its asserting literal is pushed at the cut `B`, and the outer invariant of
`propagate` holds with `B` processed. -/
theorem Analyzed.learn {input : Input} {T : solver} {db : Records} {vs : List CInt} {P : Nat}
    {A : solver} {size : CInt} {L vs' : List CInt} {B : Nat} (h : Analyzed input T db A size L vs' B)
    (hBP : B ≤ P) (core : Core input T db vs) (hmode : PMode T 0 P) (hin : db.inputs ≠ [])
    (hwatched : ∀ s ∈ db.all, 2 ≤ s.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
      ∀ p < P, FalseAt T s.2[w]! p → ∃ q, FalseAt T (- s.2[o]!) q ∧ SameOrLowerLevel T p q)
    {f' : CInt}
    (hf' : f' ≠ 0 ↔ (addClause A A.buffer size 0).1.ld ((addClause A A.buffer size 0).2 + 1) = 0) :
    ∃ db'', Core input (assign (addClause A A.buffer size 0).1 (addClause A A.buffer size 0).2 f') db'' vs' ∧
      WatchedTrue (assign (addClause A A.buffer size 0).1 (addClause A A.buffer size 0).2 f') db'' ∧
      PMode (assign (addClause A A.buffer size 0).1 (addClause A A.buffer size 0).2 f') f'
        (processedPos (assign (addClause A A.buffer size 0).1 (addClause A A.buffer size 0).2 f')) ∧
      (assign (addClause A A.buffer size 0).1 (addClause A A.buffer size 0).2 f').nLemmas = T.nLemmas + 1 ∧
      (assign (addClause A A.buffer size 0).1 (addClause A A.buffer size 0).2 f').maxLemmas =
        T.maxLemmas := by
  obtain ⟨cut, hshape, hlA, htA, -, -, -, hmax, hnlA, hmlA, hproc⟩ := h.state core
  obtain ⟨db'', hall, hptr, hlow, hl2, hd2, hw2, hld0, hld1, hnl2, hml2, hmm2, hhd2⟩ := h.add core hin
  generalize hRd : addClause A A.buffer size 0 = R at *
  have ht := core.trail
  have cut2 := cut.low hlow htA hlA
  have ht2 := hlow.trail htA hlA
  have hcut := h.cut
  have hlen2 : trailLen R.1 = B := cut2.len
  have hpos : 0 < L.length := List.length_pos_iff.mpr h.nonempty
  have hL0 : L[0]! ∈ L := by rw [getElem!_pos L 0 hpos]; exact List.getElem_mem _
  have hL0r := inRange_iff.mp (h.shape.2 _ hL0)
  have hsn : R.1.nVars = T.nVars := by rw [hlow.shape.nVars, hshape.nVars]
  obtain ⟨U, hU1, hU2, hU3⟩ := h.asserting
  have hfresh : Fresh R.1 (-L[0]!) := ⟨hl2, ht2,
    inRange_iff.mpr ⟨by omega, by rw [hsn]; omega, by rw [hsn]; omega⟩, fun i hi he => by
      rw [hlen2] at hi
      rw [cut2.at_eq i hi, abs_neg', ← hU3] at he
      have := ht.distinct i (by omega) U hU2 he
      omega⟩
  have hpush : Push R.1 (assign R.1 R.2 f') (-L[0]!) (if f' != 0 then IMPLIED else 1) (1 + R.2) := by
    have := assign_push hl2 ht2 (c := R.2) (f := f') hptr (by rw [hld0, hsn]; exact h.shape.2 _ hL0)
    rw [hld0] at this; exact this
  generalize hFd : assign R.1 R.2 f' = F at *
  obtain ⟨-, hF2, hP2, -, -, -, hN2, hM2, hMM2⟩ := hpush.keeps
  have hrv : (1 + R.2 : CInt) ≠ 0 := by omega
  have hlenF : trailLen F = B + 1 := by rw [hpush.trailLen_eq hfresh, hlen2]
  have hdecF : ∀ k < B, (IsDecision F k ↔ IsDecision T k) := fun k hk => by
    rw [hpush.isDecision_lt hfresh (by rw [hlen2]; exact hk), cut2.isDecision hk]
  have hrootT : ∀ i < trailLen T, RootLevel T i → i < forcedPos T := by
    rcases hmode.1 with ⟨h0, -⟩ | ⟨-, h', -⟩
    · exact absurd rfl h0
    · exact h'
  have hunit : (∀ k < B, ¬ IsDecision T k) ↔ L.length = 1 := by
    constructor
    · intro hk
      refine Classical.byContradiction fun hne => ?_
      obtain ⟨D, -, hD, hDd⟩ := (h.second (by omega)).2
      exact hk D hD hDd
    · intro h1 k hk
      exact h.unit h1 k hk k (Nat.le_refl _)
  have htop : RootLevel F B ↔ L.length = 1 := by
    rw [← hlen2, hpush.rootLevel_top hfresh, hlen2, ← hunit]
    constructor
    · rintro ⟨hk, -⟩ k hkB; exact (not_congr (cut2.isDecision hkB)).mp (hk k hkB)
    · intro hk; exact ⟨fun k hkB => (not_congr (cut2.isDecision hkB)).mpr (hk k hkB), hrv⟩
  have hf'' : f' ≠ 0 ↔ L.length = 1 := hf'.trans hld1
  have htag : (RootLevel F (trailLen R.1) → (if f' != 0 then IMPLIED else 1) = IMPLIED) ∧
      (¬ RootLevel F (trailLen R.1) → (if f' != 0 then IMPLIED else 1) = 1) := by
    rw [hlen2, htop]
    constructor
    · intro h1; have := hf''.mpr h1; simp [this]
    · intro h1; have : f' = 0 := Classical.byContradiction fun h0 => h1 (hf''.mp h0); simp [this]
  have hfpF : forcedPos F = forcedPos T := by
    rw [← cut2.forced]; simp only [forcedPos, hF2, hpush.shape.falseStack]
  have hppF : processedPos F = B := by
    simp only [processedPos, hP2, hpush.shape.falseStack, hlow.processed, hlow.shape.falseStack, hproc,
      hshape.falseStack]
    omega
  obtain ⟨hlF, hdF, hwF, hoF⟩ := hpush.frames hfresh hd2 hw2 (hlow.order htA hlA h.order hhd2)
  have hreas2 : Reasons R.1 db'' := fun i hi hfi hrn => by
    obtain ⟨s, hs, rest⟩ := cut2.reasons core.reasons i hi hfi hrn
    exact ⟨s, by rw [hall]; exact List.mem_append_left _ hs, rest⟩
  have hmem : (R.2, L) ∈ db''.all := by rw [hall]; simp
  have core2 : Core input F db'' vs' := by
    refine ⟨core.valid, by rw [hpush.shape.nVars, hsn]; exact core.nVars,
      by rw [hMM2, hmm2, hmax]; exact core.memory, by rw [hM2, hml2, hmlA]; exact core.maxLemmas, hlF,
      hpush.trail hfresh htag, hpush.rootEntailed hfresh (cut2.root core.root) fun hr => ?_, hdF, hwF,
      hpush.reasons hfresh hreas2 fun _ _ => ?_, ?_, hoF⟩
    · rw [hlen2, htop] at hr
      rw [Int.neg_neg]
      have : [L[0]!] = L := by obtain ⟨a, rfl⟩ := List.length_eq_one_iff.mp hr; simp
      rw [this]; exact h.entailed
    · refine ⟨(R.2, L), hmem, rfl, ?_, fun l hl' => ?_, fun hnr => ?_⟩
      · rw [Int.neg_neg]; show L[0]? = some L[0]!
        rw [getElem!_pos L 0 hpos]; exact List.getElem?_eq_getElem hpos
      · rw [List.drop_one] at hl'
        obtain ⟨j, hj, he⟩ := h.rest_false l hl'
        exact ⟨j, by rw [hlen2]; exact hj, cut2.falseAt.mpr ⟨⟨by omega, he⟩, hj⟩⟩
      · rw [hlen2, htop] at hnr
        obtain ⟨⟨j1, hj1, he, hnd⟩, -⟩ := h.second (by omega)
        refine ⟨L[1]!, ?_, j1, by rw [hlen2]; exact hj1, cut2.falseAt.mpr ⟨⟨by omega, he⟩, hj1⟩,
          fun k h1 h3 => ?_⟩
        · rw [getElem!_pos L 1 (by omega)]; exact List.mem_iff_getElem.mpr ⟨0, by simp; omega, by simp⟩
        · rw [hlen2] at h3; exact (not_congr (cut2.isDecision h3)).mpr (hnd k h1 h3)
    · intro s hs h1
      rw [hall] at hs
      rcases List.mem_append.mp hs with hs | hs
      · obtain ⟨i, hi, hroot, he⟩ := cut2.units core.units
          (fun i hi hr => by have := hrootT i hi hr; omega) s hs h1
        exact ⟨i, by rw [hlenF]; rw [hlen2] at hi; omega, (hpush.rootLevel_lt hfresh hi).mpr hroot,
          by rw [hpush.trailAt_lt hfresh hi]; exact he⟩
      · simp only [List.mem_singleton] at hs; subst hs
        exact ⟨trailLen R.1, by rw [hlenF, hlen2]; omega, by rw [hlen2]; exact htop.mpr h1,
          hpush.trailAt_top hfresh⟩
  have hfaT : ∀ {x : CInt} {j : Nat}, j < B → FalseAt F x j → FalseAt T x j := fun hj hfa =>
    (cut2.falseAt.mp ⟨by rw [hlen2]; exact hj,
      by rw [← hpush.trailAt_lt hfresh (by rw [hlen2]; exact hj)]; exact hfa.2⟩).1
  have hfaF : ∀ {x : CInt} {j : Nat}, j < B → FalseAt T x j → FalseAt F x j := fun hj hfa =>
    hpush.falseAt_lt hfresh (cut2.falseAt.mpr ⟨hfa, hj⟩)
  have hwt : WatchedTrue F db'' := by
    intro s hs h2 w o hwo p hp hfa
    rw [hppF] at hp
    rw [hall] at hs
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨q, hq, hsl⟩ := hwatched s hs h2 w o hwo p (by omega) (hfaT hp hfa)
      have hqB : q < B := Classical.byContradiction fun hge => hsl B (by omega) (by omega) hcut.2.2
      exact ⟨q, hfaF hqB hq, fun k h1 h3 => (not_congr (hdecF k (by omega))).mpr (hsl k h1 h3)⟩
    · simp only [List.mem_singleton] at hs; subst hs
      have hfT := hfaT hp hfa
      rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exfalso
        have := ht.distinct p hfT.1 U hU2 (by rw [hfT.2, hU3])
        omega
      · obtain ⟨⟨j1, hj1, he, hnd⟩, -⟩ := h.second h2
        have hpj : p = j1 := ht.distinct p hfT.1 j1 (by omega) (by rw [hfT.2, he])
        subst hpj
        refine ⟨trailLen R.1, ⟨by rw [hlenF, hlen2]; omega, hpush.trailAt_top hfresh⟩, fun k h1 h3 => ?_⟩
        rcases Nat.lt_or_ge k (trailLen R.1) with hk | hk
        · rw [hlen2] at hk; exact (not_congr (hdecF k hk)).mpr (hnd k h1 hk)
        · have : k = trailLen R.1 := by omega
          subst this; exact (not_congr (hpush.isDecision_top hfresh)).mpr hrv
  have hpm : PMode F f' (processedPos F) := by
    rw [hppF]
    refine ⟨?_, fun k hk1 hk2 => absurd hk2 (by rw [hlenF]; omega)⟩
    by_cases hu : L.length = 1
    · refine Or.inl ⟨hf''.mpr hu, fun i hi => ?_⟩
      rw [hlenF] at hi
      rcases Nat.lt_or_ge i B with hiB | hiB
      · exact (hpush.rootLevel_lt hfresh (by rw [hlen2]; exact hiB)).mpr
          ((cut2.rootLevel hiB).mpr (h.unit hu i hiB))
      · rw [show i = B by omega]; exact htop.mpr hu
    · refine Or.inr ⟨Classical.byContradiction fun hne => hu (hf''.mp hne), fun i hi hr => ?_, fun _ => ?_⟩
      · rw [hfpF]; rw [hlenF] at hi
        rcases Nat.lt_or_ge i B with hiB | hiB
        · exact hrootT i (by omega) ((cut2.rootLevel hiB).mp
            ((hpush.rootLevel_lt hfresh (by rw [hlen2]; exact hiB)).mp hr))
        · rw [show i = B by omega] at hr; exact absurd (htop.mp hr) hu
      · obtain ⟨D, hD1, hD2, hD3⟩ := (h.second (by omega)).2
        exact ⟨D, by rw [hfpF]; exact hD1, by omega, (hdecF D hD2).mpr hD3⟩
  exact ⟨db'', core2, hwt, hpm, by rw [hN2, hnl2, hnlA], by rw [hM2, hml2, hmlA]⟩

/-- Below `P`, the watched-literal invariant holds once the visited record is rearranged
(C:142, C:150): `lit` is false only at `P`, and the other watched literal is not false below
`P`, or `-lit` would be on the trail. -/
theorem Visit.conflict_watched {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S)) :
    ∀ s ∈ (db.update c (unitLits r lit) (decide (S.ld w = c - 2))).all, 2 ≤ s.2.length →
      ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) → ∀ p < P, FalseAt (Ss.st (c + 1) lit) s.2[w]! p →
        ∃ q, FalseAt (Ss.st (c + 1) lit) (- s.2[o]!) q ∧ SameOrLowerLevel (Ss.st (c + 1) lit) p q := by
  obtain ⟨-, hlow, -, -, -⟩ := hv.unit_core hc hSs
  generalize hTd : Ss.st (c + 1) lit = T at *
  have ht := hv.core.trail; have hl := hv.core.layout
  have hold := hv.unit_hold hc (T := T) (fun h' => Or.inl ((hlow.falseAt ht hl).mp h'))
    (fun h' => (hlow.falseAt ht hl).mpr h') fun p q hq h' => (hlow.sameLevel ht hl hq).mpr h'
  have hlitr := inRange_iff.mp (ht.lit _ hv.hP); rw [hv.hlit] at hlitr
  intro s hs h2 w0 o hwo p hp hfa
  rw [Records.update_all] at hs
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
  by_cases hsc : s0.1 = c
  · simp only [hsc, ↓reduceIte] at hfa
    exfalso
    rw [hlow.falseAt ht hl] at hfa
    rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- the other watched literal false below `P` would put `-lit` on the trail
      obtain ⟨a, b, tl, hr2, hab, -, -⟩ := hv.slot
      have key : ∃ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) ∧ r.2[w]! = otherLit r lit ∧ r.2[o]! = lit := by
        by_cases ha : a = lit
        · exact ⟨1, 0, Or.inr ⟨rfl, rfl⟩, by simp [otherLit, hr2, ha], by simp [hr2, ha]⟩
        · exact ⟨0, 1, Or.inl ⟨rfl, rfl⟩, by simp [otherLit, hr2, ha], by simp [hr2, hab.resolve_left ha]⟩
      obtain ⟨w1, o1, hwo1, hw1, ho1⟩ := key
      have hfa' : FalseAt S r.2[w1]! p := ⟨hfa.1, by rw [hw1]; simpa [unitLits] using hfa.2⟩
      obtain ⟨q, hq, -⟩ := hv.watched r hv.hr hv.h2 w1 o1 hwo1 p (by rw [hv.hpp]; omega) hfa'
        fun hpP => absurd hpP (by omega)
      rw [ho1] at hq
      have hqP := ht.distinct q hq.1 P hv.hP (by rw [hq.2, hv.hlit, abs_neg'])
      have e := hq.2
      rw [hqP, hv.hlit] at e
      omega
    · have e : trailAt S p = lit := by simpa [unitLits] using hfa.2
      have := ht.distinct p hfa.1 P hv.hP (by rw [e, hv.hlit])
      omega
  · simp only [hsc, ↓reduceIte] at h2 hfa ⊢
    exact hold s0 hs0 hsc h2 w0 o hwo p (by omega) hfa fun hpP => absurd hpP (by omega)

/-- C:155–158: after a conflict below the root, `analyze` and the assignment of the lemma
give back the outer invariant of `propagate`, with one more lemma. `f'` is the flag C
computes: set exactly when the lemma is a unit (`lemma[1] == 0`, C:157). -/
theorem Visit.conflict_step {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S)) (hf : f = 0)
    (hfalse : ∀ l ∈ r.2, ∃ j < trailLen S, trailAt S j = l) {f' : CInt}
    (hf' : f' ≠ 0 ↔ (analyze (Ss.st (c + 1) lit) c).1.ld ((analyze (Ss.st (c + 1) lit) c).2 + 1) = 0) :
    OutInv input S0 vs0 (assign (analyze (Ss.st (c + 1) lit) c).1 (analyze (Ss.st (c + 1) lit) c).2 f') f' ∧
    S.nLemmas < (assign (analyze (Ss.st (c + 1) lit) c).1 (analyze (Ss.st (c + 1) lit) c).2 f').nLemmas := by
  subst hf
  obtain ⟨core', hlow, -, hnl, hml⟩ := hv.unit_core hc hSs
  obtain ⟨-, hperm, -, -⟩ := hv.unit_cells hc hSs
  have hwat := hv.conflict_watched hc hSs
  generalize hTd : Ss.st (c + 1) lit = T at *
  have ht := hv.core.trail; have hl := hv.core.layout
  have hmemr : (c, unitLits r lit) ∈ (db.update c (unitLits r lit) (decide (S.ld w = c - 2))).all := by
    rw [Records.update_all]; exact List.mem_map.mpr ⟨r, hv.hr, by simp [hc]⟩
  have hin : (db.update c (unitLits r lit) (decide (S.ld w = c - 2))).inputs ≠ [] := fun he => by
    have hm := hmemr
    rw [Records.all, he, core'.database.no_lemmas he] at hm
    simp at hm
  have hmode : PMode T 0 P := hlow.pmode ht hl hv.pmode
  obtain ⟨L, vs', B, han, hBP⟩ := analyzeCore_spec (P := P) (lit := lit) core' hmemr
    (fun l hl' => by
      obtain ⟨j, hj, he⟩ := hfalse l (hperm.mem_iff.mp hl')
      exact ⟨j, by rw [hlow.trailLen ht hl]; exact hj, by rw [hlow.trailAt ht hl hj]; exact he⟩)
    (by simp [unitLits]) (by rw [hlow.trailLen ht hl]; exact hv.hP)
    (by rw [hlow.trailAt ht hl hv.hP]; exact hv.hlit) hmode hwat
  rw [analyze_eq] at hf' ⊢
  obtain ⟨db'', core2, hwt, hpm, hnl2, hml2⟩ := han.learn hBP core' hmode hin hwat hf'
  have hrel := hv.rel
  refine ⟨⟨db'', vs', core2, hwt, hpm, by rw [hml2, hml]; exact hrel.1, Or.inr ?_⟩, ?_⟩
  · rw [hnl2, hnl]; rcases hrel.2 with ⟨h1, -⟩ | h1 <;> omega
  · rw [hnl2, hnl]; omega

end MicrosatLean.Faithful.Verification
