import MicrosatLean.Fast.Verification.Inv

/-!
# Learning a lemma stored by any `addClause` (C:130, C:157–158)

The faithful `Analyzed.add` and `Analyzed.learn` (`Conflict.lean`) are stated about the
faithful `addClause A A.buffer size 0`. Their proofs only use its postcondition
`AddClausePost`, which the fast `addClause` also meets (`addClause_post`). `analyzed_add` and
`analyzed_learn` are those proofs for any result `R` with that postcondition. (They live in the
faithful namespace so that the copied proofs read as the originals.)
-/

namespace MicrosatLean.Faithful.Verification.FastLearn

open MicrosatLean.Faithful.Verification

/-- `addClause` stores the learned lemma after the records (C:130): the database gains it as
its last lemma, watched by its first two literals; the trail arrays are untouched. -/
theorem analyzed_add {input : Input} {T : solver} {db : Records} {vs : List CInt} {A : solver}
    {size : CInt} {L vs' : List CInt} {B : Nat} (h : Analyzed input T db A size L vs' B)
    (core : Core input T db vs) (hin : db.inputs ≠ []) {R : solver × Ptr}
    (post : AddClausePost A L size 0 R) :
    ∃ db'' : Records, db''.all = db.all ++ [(R.2, L)] ∧
      0 ≤ R.2 ∧
      LowSame A R.1 ∧ Layout R.1 ∧
      Database input R.1 db'' ∧
      WatchLists R.1 db'' ∧
      R.1.ld R.2 = L[0]! ∧
      (R.1.ld (R.2 + 1) = 0 ↔ L.length = 1) ∧
      R.1.nLemmas = A.nLemmas + 1 ∧
      R.1.maxLemmas = A.maxLemmas ∧
      R.1.mem_max = A.mem_max ∧
      R.1.head = A.head := by
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
  have hhd : ∀ q, (q < 8 * A.nVars + 6 ∨ 10 * A.nVars + 7 ≤ q) → 1 < L.length →
      q ≠ A.first + L[0]! ∧ q ≠ A.first + L[1]! :=
    fun q hq h2 => by
      have m0 := inRange_iff.mp (hlitA _ (first_two h2 hnd).1)
      have m1 := inRange_iff.mp (hlitA _ (first_two h2 hnd).2.1)
      omega
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
theorem analyzed_learn {input : Input} {T : solver} {db : Records} {vs : List CInt} {P : Nat}
    {A : solver} {size : CInt} {L vs' : List CInt} {B : Nat} (h : Analyzed input T db A size L vs' B)
    (hBP : B ≤ P) (core : Core input T db vs) (hmode : PMode T 0 P) (hin : db.inputs ≠ [])
    {R : solver × Ptr} (post : AddClausePost A L size 0 R)
    (hwatched : ∀ s ∈ db.all, 2 ≤ s.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
      ∀ p < P, FalseAt T s.2[w]! p → ∃ q, FalseAt T (- s.2[o]!) q ∧ SameOrLowerLevel T p q)
    {f' : CInt}
    (hf' : f' ≠ 0 ↔ R.1.ld (R.2 + 1) = 0) :
    ∃ db'', Core input (assign R.1 R.2 f') db'' vs' ∧
      WatchedTrue (assign R.1 R.2 f') db'' ∧
      PMode (assign R.1 R.2 f') f'
        (processedPos (assign R.1 R.2 f')) ∧
      (assign R.1 R.2 f').nLemmas = T.nLemmas + 1 ∧
      (assign R.1 R.2 f').maxLemmas =
        T.maxLemmas := by
  obtain ⟨cut, hshape, hlA, htA, -, -, -, hmax, hnlA, hmlA, hproc⟩ := h.state core
  obtain ⟨db'', hall, hptr, hlow, hl2, hd2, hw2, hld0, hld1, hnl2, hml2, hmm2, hhd2⟩ := analyzed_add h core hin post
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


end MicrosatLean.Faithful.Verification.FastLearn
