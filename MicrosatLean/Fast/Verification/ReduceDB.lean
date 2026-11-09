import MicrosatLean.Fast.Verification.ReduceDBLoops

/-!
# `reduceDB` of the fast port (C:68–83)

`reduceDB_fast` is the faithful `reduceDB_spec` for the fast `reduceDB`. Its proof is the
faithful one, with the three faithful phases replaced by the fast loops' contracts
(`ReduceDBLoops.lean`): `raiseLoop_spec`, `unlinkAll_fast` and `keepLoop_fast`.
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast
set_option linter.deprecated false

/-- `reduceDB` after a restart (the trail is the root) when there are more lemmas than
`maxLemmas`: `Settled` holds again with the same order, `maxLemmas` grew, `head` is kept.
The re-added lemmas move down, so memory never runs out here. -/
theorem reduceDB_fast {input : Input} {L : Lay} {s : St} {fa sl : Int} {db : Records} {vs : List Int}
    (k : Cell) (hB : Bounds L s) (h : Settled input (abs L s (memoryBound input) fa sl) db vs)
    (root : trailLen (abs L s (memoryBound input) fa sl) = forcedPos (abs L s (memoryBound input) fa sl))
    (more : s.maxLemmas.toInt < s.nLemmas.toInt) :
    Bounds L (reduceDB L s k) ∧
      ∃ db', Settled input (abs L (reduceDB L s k) (memoryBound input) fa sl) db' vs ∧
        s.maxLemmas.toInt < (reduceDB L s k).maxLemmas.toInt ∧ (reduceDB L s k).head = s.head := by
  rw [reduceDB_unfold]
  generalize hM : memoryBound input = M at h root ⊢
  -- the faithful state before `reduceDB`
  have hSf : (abs L s M fa sl).DB = toDB s.db ∧ (abs L s M fa sl).nVars = L.nVars.toInt ∧
      (abs L s M fa sl).first = L.first.toInt ∧ (abs L s M fa sl).mem_fixed = s.memFixed.toInt ∧
      (abs L s M fa sl).mem_used = s.memUsed.toInt ∧ (abs L s M fa sl).maxLemmas = s.maxLemmas.toInt ∧
      (abs L s M fa sl).nLemmas = s.nLemmas.toInt := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  generalize hS : abs L s M fa sl = S at h root hSf
  obtain ⟨hSDB, hSn, hSfirst, hSmf, hSmu, hSml, hSnl⟩ := hSf
  have core := h.core; have hd := core.database; have hl := core.layout
  have hn := hl.num; have hn1 := hl.nVars_pos
  have hml0 := core.maxLemmas
  have hN := hB.nVars
  have hmu := hB.memUsed
  -- there are lemmas (`nLemmas > maxLemmas ≥ 0`), hence input records
  have hlem : db.lemmas ≠ [] := fun he => by have := hd.nLemmas; rw [he] at this; simp at this; omega
  have hin : db.inputs ≠ [] := fun he => hlem (hd.no_lemmas he)
  have hst : lemmasStart S db = S.mem_fixed := by simp [lemmasStart, hin]
  have hb1 := hd.inputs_tile.bounds; have hb2 := hd.lemmas_tile.bounds
  rw [hst] at hb1 hb2
  have hmf : clausesAt S.nVars ≤ S.mem_fixed := hb1.1
  have hmf' : 10 * S.nVars + 8 ≤ S.mem_fixed := by simp only [clausesAt] at hmf; exact hmf
  -- at most `2^30 / 3` lemmas: each record takes at least 3 cells below `mem_used ≤ 2^30`
  have hlen : S.mem_fixed + 3 * db.lemmas.length ≤ S.mem_used := by
    have := tiling_three_mul_length_le hd.lemmas_tile; rw [hst] at this; exact this
  have hnl := hd.nLemmas
  -- phase 1 (C:69–71)
  obtain ⟨hm1, hm2, hm3⟩ := raiseLoop_spec s.nLemmas (by omega) _ s.maxLemmas rfl (by omega)
  generalize hm : raiseLoop s.nLemmas s.maxLemmas = m at hm1 hm2 hm3 ⊢
  -- phase 2 (C:73–77) on `S1`, which differs from `S` only in its counters
  have hl1 : Layout ({ S with maxLemmas := m.toInt, nLemmas := 0 } : solver) :=
    hl.frame ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ (ld_with_counters S _ _ _)
  have hw1 : WatchLists ({ S with maxLemmas := m.toInt, nLemmas := 0 } : solver) db := fun lit hlit => by
    obtain ⟨links, h1, h2, h3⟩ := core.watches lit hlit
    exact ⟨links, h1.frame fun q _ => ld_with_counters S _ _ q, h2, h3⟩
  have hlf : LinkFacts ({ S with maxLemmas := m.toInt, nLemmas := 0 } : solver) db :=
    let h' := hd.linkFacts hin; ⟨h'.1, h'.2, h'.3⟩
  have hneg : (-L.nVars).toInt = -S.nVars := by rw [toInt_neg (by omega), hSn]
  -- the fast array before phase 2 is `S`'s memory
  have hS1 : ∀ q, ({ ({ S with maxLemmas := m.toInt, nLemmas := 0 } : solver) with DB := toDB s.db } : solver).ld q =
      ({ S with maxLemmas := m.toInt, nLemmas := 0 } : solver).ld q := fun q => by
    rw [ld_eq_ldA, ld_eq_ldA ({ S with maxLemmas := m.toInt, nLemmas := 0 } : solver)]
    show ldA (toDB s.db) q = ldA S.DB q
    rw [hSDB]
  obtain ⟨hszU, pre, hpreM, ⟨DB2, hU⟩, hlists, hcells⟩ :=
    unlinkAll_fast (S := { S with maxLemmas := m.toInt, nLemmas := 0 }) (L := L) (memFixed := s.memFixed)
      hl1 hlf hSfirst hSn hSmf (by have := hN.2; show 10 * S.nVars + 7 ≤ 2 ^ 30; omega) _ s.db (-L.nVars) rfl
      hB.size (by rw [hneg]; exact Int.le_refl _) (by rw [hneg]; show -S.nVars ≤ S.nVars + 1; omega) []
      (fun v => by simp only [List.not_mem_nil, false_iff]; rw [hneg]; omega)
      ⟨⟨toDB s.db, rfl⟩, fun lit hlit => by
        obtain ⟨ll, hll, hndl, hml⟩ := hw1 lit hlit
        exact ⟨ll, hll.frame fun q _ => hS1 q, hndl, fun link => by simp [hml]⟩, fun q _ _ => hS1 q⟩
  generalize hUd : unlinkAll L s.db s.memFixed (-L.nVars) = dbU at hszU hU hlists hcells ⊢
  generalize hUdef : ({ ({ S with maxLemmas := m.toInt, nLemmas := 0 } : solver) with DB := toDB dbU } : solver) = U
    at hU hlists hcells
  -- cells outside the watch heads and links are unchanged by phase 2
  have hUS : ∀ q, 0 ≤ q → (q < 8 * S.nVars + 6 ∨ 10 * S.nVars + 6 < q) →
      (∀ lit, ¬ Watches db.all lit q db.flip) →
      U.ld q = S.ld q := fun q h0 h1 h2 => (hcells q h0 fun lit hl' => by
    have hb := inRange_iff.mp ((hpreM lit).mp hl')
    change lit ≠ 0 ∧ -S.nVars ≤ lit ∧ lit ≤ S.nVars at hb
    exact ⟨by show q ≠ S.first + lit; omega, h2 lit⟩).trans (ld_with_counters S _ _ q)
  have hUf : U.nVars = S.nVars ∧ U.mem_fixed = S.mem_fixed ∧ U.mem_used = S.mem_used ∧
      U.mem_max = S.mem_max ∧ U.nLemmas = 0 ∧ U.maxLemmas = m.toInt := by
    rw [← hUdef]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hshapeU : SameShape S U := by rw [← hUdef]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
      refine ⟨links, by rw [hshapeU.first]; exact h1, h2, fun link => ?_⟩
      rw [h3 link]; simp only [(hpreM lit).mpr hlit, if_true, records_all_inputs]
      exact (Watches.congr_flip fun r hr => (hFin r hr).symm)
    · have := hd.lemma_shape r hr; rw [hUf.1]; exact ⟨this.1, this.2.1, this.2.2⟩
  -- phase 3 (C:78–83)
  have hU0 : U = abs L { s with db := dbU, maxLemmas := m, nLemmas := 0 } M fa sl := by
    rw [← hUdef]; subst hS; rfl
  have h2 : ((2 : Cell)).toInt = 2 := rfl
  have hi0 : (s.memFixed + 2).toInt = s.memFixed.toInt + 2 := by
    rw [toInt_add (by rw [h2]; omega) (by rw [h2]; omega), h2]
  have hinit : KeepInv U db.inputs db.lemmas F
      (abs L { s with db := dbU, memUsed := s.memFixed, maxLemmas := m, nLemmas := 0 } M fa sl)
      (s.memFixed + 2).toInt := by
    refine ⟨0, Nat.zero_le _, [], by rw [hpre.lemmas_tile.tilePos_zero, hi0, hUf.2.1, hSmf],
      ⟨toDB dbU, by rw [hU0]; rfl⟩, ?_, List.nil_sublist _, ?_, fun q _ => ?_, fun q _ _ _ => ?_,
      fun lit hl' => ?_⟩
    · show Tiling _ U.mem_fixed s.memFixed.toInt []
      rw [hUf.2.1, hSmf]; exact Tiling.nil _
    · show s.memFixed.toInt + 2 ≤ _; omega
    · rw [ld_abs_eq_ldA, hU0, ld_abs_eq_ldA]
    · rw [ld_abs_eq_ldA, hU0, ld_abs_eq_ldA]
    · have hl'' : InRange U.nVars lit := by rw [hU0]; exact hl'
      obtain ⟨links, h1, h2, h3⟩ := hpre.watches lit hl''
      rw [hU0] at h1
      exact ⟨links, h1.frame fun q _ => by rw [ld_abs_eq_ldA, ld_abs_eq_ldA], h2, h3⟩
  obtain ⟨hszR, K, ⟨DB3, hR⟩, htK, hsubK, hlowK, hwK, hRmu⟩ :=
    keepLoop_fast hpre hU0 hN (by rw [hUf.2.2.1, hSmu]; exact hmu) (by omega) s.memUsed k
      (by rw [hUf.2.2.1, hSmu]) _ dbU s.memFixed 0 (s.memFixed + 2) rfl hszU hinit
  generalize hres : keepLoop L dbU s.memFixed 0 s.memUsed k (s.memFixed + 2) = res at hszR hR htK hlowK hwK hRmu ⊢
  have hRR : abs L { s with db := res.1, memUsed := res.2.1, nLemmas := res.2.2, maxLemmas := m } M fa sl =
      abs L { ({ s with db := dbU, maxLemmas := m, nLemmas := 0 } : St) with
        db := res.1, memUsed := res.2.1, nLemmas := res.2.2 } M fa sl := rfl
  rw [hRR]
  generalize hRd : abs L { ({ s with db := dbU, maxLemmas := m, nLemmas := 0 } : St) with
    db := res.1, memUsed := res.2.1, nLemmas := res.2.2 } M fa sl = R at hR htK hlowK hwK hRmu ⊢
  have hRmu' : R.mem_used = res.2.1.toInt := by rw [← hRd]; rfl
  have hRf : R.nVars = S.nVars ∧ R.mem_fixed = S.mem_fixed ∧ R.nLemmas = K.length ∧ R.maxLemmas = m.toInt ∧
      R.forced = S.forced ∧ R.processed = S.processed ∧ R.assigned = S.assigned ∧ R.head = S.head ∧
      R.mem_max = S.mem_max := by
    rw [hR, ← hUdef]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hshapeR : SameShape S R := by rw [hR, ← hUdef]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
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
  refine ⟨⟨hszR, hN, ?_, ?_⟩, ⟨db.inputs, K, F⟩, h.rebuild root hshapeR ⟨hRf.2.2.2.2.1, hRf.2.2.2.2.2.1,
      hRf.2.2.2.2.2.2.1, hRf.2.2.2.2.2.2.2.1, hRf.2.2.2.2.2.2.2.2⟩ (by rw [hRf.2.2.2.1]; omega)
      (fun q h0 h1 => hRS q h0 (by omega) (Or.inl h1) fun lit hw => by
        have := Watches.link_ge hd hw; simp only [clausesAt] at this; omega)
      (hRS _ (by simp only [clausesAt]; omega) (by simp only [clausesAt]; omega)
        (Or.inr (by simp only [clausesAt]; omega)) fun lit hw => by have := Watches.link_ge hd hw; omega)
      hdb hwK fun r hr => ?_, by show s.maxLemmas.toInt < m.toInt; omega, rfl⟩
  · show res.2.1.toInt ≤ 2 ^ 30
    rw [← hRmu']; rw [hUf.2.2.1] at hRmu; omega
  · show m.toInt ≤ 2 ^ 30
    omega
  · rcases List.mem_append.mp hr with hr | hr
    · exact ⟨r, List.mem_append_left _ hr, rfl⟩
    · obtain ⟨r0, hr0, he⟩ := hK r hr; exact ⟨r0, List.mem_append_right _ hr0, he⟩

end MicrosatLean.Fast.Verification
