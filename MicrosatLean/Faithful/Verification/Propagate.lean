import MicrosatLean.Faithful.Verification.Conflict
import Std.Tactic.Do

/-!
# `propagate` (C:132–158)

From the top of `solve`'s loop, `propagate` either finds a conflict at the root (the
input is unsatisfiable), or returns a `Settled` state. Without a conflict it only
extends the trail; after a conflict it has learned at least one new lemma.
-/

namespace MicrosatLean.Faithful.Verification

open Std.Do
set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- What `propagate` does from the top of `solve`'s loop: a correct UNSAT, or a `Settled`
state related to the start. -/
theorem propagate_main {input : Input} {S0 : solver} {db0 : Records} {vs0 : List CInt} {d0 : CInt}
    (core0 : Core input S0 db0 vs0) (watched0 : WatchedTrue S0 db0) (mode0 : Mode S0) :
    ((propagate S0).2 = UNSAT ∧ input.Unsat) ∨
    ((propagate S0).2 = SAT ∧ ∃ db vs, Settled input (propagate S0).1 db vs ∧ Rel S0 vs0 (propagate S0).1 vs) := by
  generalize hR : propagate S0 = R
  apply Id.of_wp_run_eq hR
  mvcgen [propagate]
  case inv1 => exact fun ⟨_, S, _⟩ => ULift.up (outMeasure S)
  case inv2 => exact ⇓ c => match c with
    | .inl ⟨ret, S, f⟩ => ⌜ret = none ∧ OutInv input S0 vs0 S f⌝
    | .inr ⟨ret, S, f⟩ => ⌜(ret = none ∧ OutInv input S0 vs0 S f ∧ S.assigned ≤ S.processed) ∨
        (∃ S', ret = some (S', UNSAT) ∧ input.Unsat)⌝
  case inv3 => exact fun ⟨_, S, _, w⟩ => ULift.up (linksAfter S w).length
  case inv4 =>
    rename_i b _ _ _ _ _ _ _ _ _
    exact ⇓ c => match c with
      | .inl ⟨ret, S, f, w⟩ => ⌜ret = none ∧
          WInv input S0 vs0 (processedPos b.2.1) (b.2.1.ld b.2.1.processed) S f w ∧
          S.nLemmas = b.2.1.nLemmas⌝
      | .inr ⟨ret, S, f, w⟩ => ⌜(ret = none ∧ OutInv input S0 vs0 S f ∧
          ((S.nLemmas = b.2.1.nLemmas ∧ processedPos S = processedPos b.2.1 + 1) ∨
            b.2.1.nLemmas < S.nLemmas)) ∨
          (∃ S', ret = some (S', UNSAT) ∧ input.Unsat)⌝
  case inv5 => exact fun ⟨_, _, i⟩ => ULift.up (S0.nVars + 3 - i).toNat
  case inv6 =>
    rename_i lit _ _ _ _ _ _ S _ _ w _ clause _ _ _ _ _
    exact ⇓ c => match c with
      | .inl ⟨S', unit, i⟩ => ⌜ScanInv (S.st (clause + 1) (S.ld (clause + 1 + 1))) (clause + 1) w lit S0.nVars S' unit i⌝
      | .inr ⟨S', unit, i⟩ => ⌜ScanInv (S.st (clause + 1) (S.ld (clause + 1 + 1))) (clause + 1) w lit S0.nVars S' unit i ∧ (unit ≠ 0 → S'.ld (clause + 1 + i) = 0)⌝
  case inv7 => exact fun ⟨_, _, i⟩ => ULift.up (S0.nVars + 3 - i).toNat
  case inv8 =>
    rename_i lit _ _ _ _ _ _ S _ _ w _ clause _ _ _ _ _
    exact ⇓ c => match c with
      | .inl ⟨S', unit, i⟩ => ⌜ScanInv (S) (clause + 1) w lit S0.nVars S' unit i⌝
      | .inr ⟨S', unit, i⟩ => ⌜ScanInv (S) (clause + 1) w lit S0.nVars S' unit i ∧ (unit ≠ 0 → S'.ld (clause + 1 + i) = 0)⌝
  case inv9 => exact fun ⟨_, _, i⟩ => ULift.up (S0.nVars + 3 - i).toNat
  case inv10 =>
    rename_i lit _ _ _ _ _ _ S _ _ w _ clause _ _ _ _ _
    exact ⇓ c => match c with
      | .inl ⟨S', unit, i⟩ => ⌜ScanInv (S.st clause (S.ld (clause + 1))) (clause) w lit S0.nVars S' unit i⌝
      | .inr ⟨S', unit, i⟩ => ⌜ScanInv (S.st clause (S.ld (clause + 1))) (clause) w lit S0.nVars S' unit i ∧ (unit ≠ 0 → S'.ld (clause + i) = 0)⌝
  case inv11 => exact fun ⟨_, _, i⟩ => ULift.up (S0.nVars + 3 - i).toNat
  case inv12 =>
    rename_i lit _ _ _ _ _ _ S _ _ w _ clause _ _ _ _ _
    exact ⇓ c => match c with
      | .inl ⟨S', unit, i⟩ => ⌜ScanInv (S) (clause) w lit S0.nVars S' unit i⌝
      | .inr ⟨S', unit, i⟩ => ⌜ScanInv (S) (clause) w lit S0.nVars S' unit i ∧ (unit ≠ 0 → S'.ld (clause + i) = 0)⌝
  -- the literal scan (C:143–152), in each of the four copies `mvcgen` makes
  case vc1.step.isTrue.isTrue | vc11.step.isTrue.isTrue | vc21.step.isTrue.isTrue |
      vc31.step.isTrue.isTrue =>
    rename_i b mb Sb s unit i hc jp hf S2 st S1 Sn hinv
    obtain ⟨hvar, hscan⟩ := hinv
    simp [WhileVariant.eval, SVal.evalsTo] at hvar hc hf
    obtain ⟨h1, h2, h3⟩ := hscan.found hc.1 hc.2 hf
    have hvar' : mb = (S0.nVars + 3 - i).toNat := hvar
    have h2' : S0.nVars + 3 - (i + 1) < S0.nVars + 3 - i := h2
    have h3' : 0 ≤ S0.nVars + 3 - (i + 1) := h3
    refine ⟨(S0.nVars + 3 - (i + 1)).toNat, ?_, by rw [hvar']; exact toNat_lt_toNat' h2' h3', h1⟩
    simp [WhileVariant.eval, SVal.evalsTo]
  case vc2.step.isTrue.isFalse | vc12.step.isTrue.isFalse | vc22.step.isTrue.isFalse |
      vc32.step.isTrue.isFalse =>
    rename_i b mb Sb s unit i hc jp hf hinv
    obtain ⟨hvar, hscan⟩ := hinv
    simp [WhileVariant.eval, SVal.evalsTo] at hvar hc hf
    obtain ⟨h1, h2, h3⟩ := hscan.skip hc.1 hc.2 hf
    have hvar' : mb = (S0.nVars + 3 - i).toNat := hvar
    have h2' : S0.nVars + 3 - (i + 1) < S0.nVars + 3 - i := h2
    have h3' : 0 ≤ S0.nVars + 3 - (i + 1) := h3
    refine ⟨(S0.nVars + 3 - (i + 1)).toNat, ?_, by rw [hvar']; exact toNat_lt_toNat' h2' h3', h1⟩
    simp [WhileVariant.eval, SVal.evalsTo]
  case vc3.step.isFalse | vc13.step.isFalse | vc23.step.isFalse | vc33.step.isFalse =>
    rename_i b mb Sb s unit i hc hinv
    refine ⟨hinv.2, fun hu => ?_⟩
    simp at hc; exact hc hu
  -- the scan starts at literal 2 of the visited clause (C:139–143)
  case vc4.step.isTrue.isTrue.isTrue.pre =>
    rename_i _ b1 mb1 s2 So fo1 hlt lit Sw w1 hout b mb s1 S s2' f w hne clause jp1 hm2 jp hl0 hinv
    simp at hinv hm2 ⊢
    obtain ⟨-, -, hw, -⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, r, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    have hN : S0.nVars = S.nVars := by rw [hv.core.nVars, core0.nVars]
    exact hv.scan_start hc hN fun q hq => by
      have := hv.core.database.record_ge hv.hr; simp only [clausesAt] at this; have := hv.core.layout.nVars_pos
      rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)]
  case vc14.step.isTrue.isTrue.isFalse.pre =>
    rename_i _ b1 mb1 s2 So fo1 hlt lit Sw w1 hout b mb s1 S s2' f w hne clause jp1 hm2 jp hl0 hinv
    simp at hinv hm2 ⊢
    obtain ⟨-, -, hw, -⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, r, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    have hN : S0.nVars = S.nVars := by rw [hv.core.nVars, core0.nVars]
    exact hv.scan_start hc hN fun q hq => rfl
  case vc24.step.isTrue.isFalse.isTrue.pre =>
    rename_i _ b1 mb1 s2 So fo1 hlt lit Sw w1 hout b mb s1 S s2' f w hne clause jp1 hm2 jp hl0 hinv
    simp at hinv hm2 ⊢
    obtain ⟨-, -, hw, -⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, r, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    have hN : S0.nVars = S.nVars := by rw [hv.core.nVars, core0.nVars]
    exact hv.scan_start hc hN fun q hq => by
      have := hv.core.database.record_ge hv.hr; simp only [clausesAt] at this; have := hv.core.layout.nVars_pos
      rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)]
  case vc34.step.isTrue.isFalse.isFalse.pre =>
    rename_i _ b1 mb1 s2 So fo1 hlt lit Sw w1 hout b mb s1 S s2' f w hne clause jp1 hm2 jp hl0 hinv
    simp at hinv hm2 ⊢
    obtain ⟨-, -, hw, -⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, r, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    have hN : S0.nVars = S.nVars := by rw [hv.core.nVars, core0.nVars]
    exact hv.scan_start hc hN fun q hq => rfl
  -- the watch loop and the outer loop (C:135–138, C:157)
  case vc41.step.isFalse =>
    rename_i b1 mb1 s2 So fo1 hlt lit Sw w1 hout b mb s1 S s f w hc hinv
    simp at hinv ⊢
    obtain ⟨-, -, hw, hn⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) (So.ld So.processed) S f w := hw
    have hend : S.ld w = END := by simpa using hc
    obtain ⟨hout', hpp⟩ := hw'.exit hend
    exact ⟨hout', Or.inl ⟨hn, hpp⟩⟩
  case vc42.step.isTrue.pre =>
    rename_i b mb s So fo hlt lit Sw w hout
    simp at hout ⊢
    obtain ⟨-, -, hout⟩ := hout
    exact ⟨WInv.init hout hlt, rfl⟩
  case vc43.step.isTrue.post.success.h_1 =>
    rename_i b mb s So fo hlt lit Sw w hout r s1 S s2 f a hr hinv
    simp at hinv ⊢
    rcases hinv with ⟨hn, -⟩ | ⟨⟨x, hx⟩, hu⟩
    · rw [hn] at hr; exact absurd hr (by simp)
    · rw [hr] at hx; exact ⟨⟨x, Option.some.inj hx⟩, hu⟩
  case vc44.step.isTrue.post.success.h_2 =>
    rename_i b mb s So fo hlt lit Sw w hout r s1 S s2 f hr hinv
    simp at hout hinv ⊢
    obtain ⟨hvar, -, hout0⟩ := hout
    have hout0' : OutInv input S0 vs0 So fo := hout0
    have hvar' : mb = outMeasure So := hvar
    obtain ⟨db, vs, core, -, -, -⟩ := hout0'
    rcases hinv with ⟨-, hout', hrel⟩ | ⟨⟨S', hS'⟩, -⟩
    · have hout'' : OutInv input S0 vs0 S f := hout'
      have hrel' : (S.nLemmas = So.nLemmas ∧ processedPos S = processedPos So + 1) ∨
          So.nLemmas < S.nLemmas := hrel
      obtain ⟨db', vs', core', -, -, -⟩ := id hout''
      have ht := core.trail; have ht' := core'.trail
      have hpp : processedPos So < trailLen So := by
        simp only [processedPos, trailLen]; have := ht.forced_le; have := ht.processed_le; omega
      have hpp' : processedPos S ≤ S.nVars.toNat := by
        have := ht'.len_le; simp only [processedPos, trailLen] at *
        have := ht'.processed_le; have := ht'.assigned_le; have := ht'.forced_le; omega
      have hlt := outMeasure_lt (core'.nVars.trans core.nVars.symm)
        (nLemmas_le_bound core'.database) (by rw [core.database.nLemmas]; omega) hpp ht.len_le hpp' hrel'
      exact ⟨by rw [hvar']; exact hlt, hout''⟩
    · rw [hS'] at hr; exact absurd hr (by simp)
  case vc45.step.isFalse =>
    rename_i b mb s So fo hc hout
    simp at hout hc ⊢
    exact ⟨hout.2.2, hc⟩
  case vc46.pre =>
    simp
    exact OutInv.init core0 watched0 mode0
  case vc47.post.success.h_1 =>
    rename_i r s S f a hr hinv
    simp at hinv
    rcases hinv with ⟨hn, -⟩ | ⟨⟨S', hS'⟩, hu⟩
    · rw [hn] at hr; exact absurd hr (by simp)
    · rw [hr] at hS'; rw [Option.some.inj hS']; exact Or.inl ⟨rfl, hu⟩
  case vc48.post.success.h_2.isTrue =>
    rename_i r s S f hr jp hf hinv
    simp at hinv
    rcases hinv with ⟨-, hout, hpa⟩ | ⟨⟨S', hS'⟩, -⟩
    · have hout' : OutInv input S0 vs0 S f := hout
      obtain ⟨db, vs, hset, hrel⟩ := hout'.post hpa
      rw [if_pos hf] at hset hrel
      exact Or.inr ⟨trivial, db, vs, hset, hrel⟩
    · rw [hS'] at hr; exact absurd hr (by simp)
  case vc49.post.success.h_2.isFalse =>
    rename_i r s S f hr jp hf hinv
    simp at hinv
    rcases hinv with ⟨-, hout, hpa⟩ | ⟨⟨S', hS'⟩, -⟩
    · have hout' : OutInv input S0 vs0 S f := hout
      obtain ⟨db, vs, hset, hrel⟩ := hout'.post hpa
      rw [if_neg hf] at hset hrel
      exact Or.inr ⟨trivial, db, vs, hset, hrel⟩
    · rw [hS'] at hr; exact absurd hr (by simp)
  case vc5.step.isTrue.isTrue.isTrue.post.success.isTrue.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hy hscan
    simp at hinv hm2 hl0 hu hy ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨L, -, -, -, -, hs⟩ := hscan.1
    have hSr : Sr = S.st (clause + 1) (S.ld (clause + 1 + 1)) := by
      rcases hs with ⟨-, h', -⟩ | ⟨h0, -⟩
      · exact h'
      · exact absurd h0 hu
    have hT : T = (S.st (clause + 1) (S.ld (clause + 1 + 1))).st (clause + 1 + 1) lit := by simp only [T]; rw [hSr]
    rw [hT] at hy
    have key := hv.true_step hc (Or.inl ⟨hl0, rfl⟩) hy
    simp only [w']
    rw [hT]
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc15.step.isTrue.isTrue.isFalse.post.success.isTrue.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hy hscan
    simp at hinv hm2 hl0 hu hy ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨L, -, -, -, -, hs⟩ := hscan.1
    have hSr : Sr = S := by
      rcases hs with ⟨-, h', -⟩ | ⟨h0, -⟩
      · exact h'
      · exact absurd h0 hu
    have hT : T = (S).st (clause + 1 + 1) lit := by simp only [T]; rw [hSr]
    rw [hT] at hy
    have key := hv.true_step hc (Or.inr ⟨hl0, rfl⟩) hy
    simp only [w']
    rw [hT]
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc25.step.isTrue.isFalse.isTrue.post.success.isTrue.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hy hscan
    simp at hinv hm2 hl0 hu hy ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨L, -, -, -, -, hs⟩ := hscan.1
    have hSr : Sr = S.st (clause) (S.ld (clause + 1)) := by
      rcases hs with ⟨-, h', -⟩ | ⟨h0, -⟩
      · exact h'
      · exact absurd h0 hu
    have hT : T = (S.st (clause) (S.ld (clause + 1))).st (clause + 1) lit := by simp only [T]; rw [hSr]
    rw [hT] at hy
    have key := hv.true_step hc (Or.inl ⟨hl0, rfl⟩) hy
    simp only [w']
    rw [hT]
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc35.step.isTrue.isFalse.isFalse.post.success.isTrue.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hy hscan
    simp at hinv hm2 hl0 hu hy ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨L, -, -, -, -, hs⟩ := hscan.1
    have hSr : Sr = S := by
      rcases hs with ⟨-, h', -⟩ | ⟨h0, -⟩
      · exact h'
      · exact absurd h0 hu
    have hT : T = (S).st (clause + 1) lit := by simp only [T]; rw [hSr]
    rw [hT] at hy
    have key := hv.true_step hc (Or.inr ⟨hl0, rfl⟩) hy
    simp only [w']
    rw [hT]
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc7.step.isTrue.isTrue.isTrue.post.success.isTrue.isFalse.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf hscan
    simp at hinv hm2 hl0 hu hny hyf hf hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S.st (clause + 1) (S.ld (clause + 1 + 1))).st (clause + 1 + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inl ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inl ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    have hroot : ∀ j < trailLen S, RootLevel S j := by
      rcases hv.pmode.1 with ⟨_, h'⟩ | ⟨h0, -⟩
      · exact h'
      · exact absurd h0 hf
    exact hv.core.unsat_of_root_conflict hv.hr fun l hl => by
      obtain ⟨j, hj, he⟩ := hall l hl; exact ⟨j, hj, hroot j hj, he⟩
  case vc17.step.isTrue.isTrue.isFalse.post.success.isTrue.isFalse.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf hscan
    simp at hinv hm2 hl0 hu hny hyf hf hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S).st (clause + 1 + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inr ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inr ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    have hroot : ∀ j < trailLen S, RootLevel S j := by
      rcases hv.pmode.1 with ⟨_, h'⟩ | ⟨h0, -⟩
      · exact h'
      · exact absurd h0 hf
    exact hv.core.unsat_of_root_conflict hv.hr fun l hl => by
      obtain ⟨j, hj, he⟩ := hall l hl; exact ⟨j, hj, hroot j hj, he⟩
  case vc27.step.isTrue.isFalse.isTrue.post.success.isTrue.isFalse.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf hscan
    simp at hinv hm2 hl0 hu hny hyf hf hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S.st (clause) (S.ld (clause + 1))).st (clause + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inl ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inl ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    have hroot : ∀ j < trailLen S, RootLevel S j := by
      rcases hv.pmode.1 with ⟨_, h'⟩ | ⟨h0, -⟩
      · exact h'
      · exact absurd h0 hf
    exact hv.core.unsat_of_root_conflict hv.hr fun l hl => by
      obtain ⟨j, hj, he⟩ := hall l hl; exact ⟨j, hj, hroot j hj, he⟩
  case vc37.step.isTrue.isFalse.isFalse.post.success.isTrue.isFalse.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf hscan
    simp at hinv hm2 hl0 hu hny hyf hf hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S).st (clause + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inr ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inr ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    have hroot : ∀ j < trailLen S, RootLevel S j := by
      rcases hv.pmode.1 with ⟨_, h'⟩ | ⟨h0, -⟩
      · exact h'
      · exact absurd h0 hf
    exact hv.core.unsat_of_root_conflict hv.hr fun l hl => by
      obtain ⟨j, hj, he⟩ := hall l hl; exact ⟨j, hj, hroot j hj, he⟩
  case vc6.step.isTrue.isTrue.isTrue.post.success.isTrue.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyz hscan
    simp at hinv hm2 hl0 hu hny hyz hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S.st (clause + 1) (S.ld (clause + 1 + 1))).st (clause + 1 + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inl ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyt : flag S (-(otherLit rr lit)) = 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hny; exact hny
    have hyf : flag S (otherLit rr lit) = 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyz; exact hyz
    have key := hv.assign_step hc (Or.inl ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyt hyf (f := f)
    simp only [w']
    rw [hT]
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc16.step.isTrue.isTrue.isFalse.post.success.isTrue.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyz hscan
    simp at hinv hm2 hl0 hu hny hyz hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S).st (clause + 1 + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inr ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyt : flag S (-(otherLit rr lit)) = 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hny; exact hny
    have hyf : flag S (otherLit rr lit) = 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyz; exact hyz
    have key := hv.assign_step hc (Or.inr ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyt hyf (f := f)
    simp only [w']
    rw [hT]
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc26.step.isTrue.isFalse.isTrue.post.success.isTrue.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyz hscan
    simp at hinv hm2 hl0 hu hny hyz hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S.st (clause) (S.ld (clause + 1))).st (clause + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inl ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyt : flag S (-(otherLit rr lit)) = 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hny; exact hny
    have hyf : flag S (otherLit rr lit) = 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyz; exact hyz
    have key := hv.assign_step hc (Or.inl ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyt hyf (f := f)
    simp only [w']
    rw [hT]
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc36.step.isTrue.isFalse.isFalse.post.success.isTrue.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyz hscan
    simp at hinv hm2 hl0 hu hny hyz hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S).st (clause + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inr ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyt : flag S (-(otherLit rr lit)) = 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hny; exact hny
    have hyf : flag S (otherLit rr lit) = 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyz; exact hyz
    have key := hv.assign_step hc (Or.inr ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyt hyf (f := f)
    simp only [w']
    rw [hT]
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc10.step.isTrue.isTrue.isTrue.post.success.isFalse =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu hscan
    simp at hinv hm2 hl0 hu hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨L, t, hL, hnz, ht2, htL, hft, hSr⟩ := hscan.1.found_end hu
    -- the scan stopped inside the record
    have htl : t < rr.2.length := by
      obtain ⟨a', b', tl', hr2, -, -, hrec⟩ := hv.slot
      have hcb := hv.core.database.record_ge hv.hr; simp only [clausesAt] at hcb
      have hn1 := hv.core.layout.nVars_pos
      refine Classical.byContradiction fun hge => ?_
      have hlen2 : 2 ≤ rr.2.length := by rw [hr2]; simp
      have := hnz rr.2.length (by omega) (by omega)
      apply this
      have hterm := hrec.2; rw [← hc] at hterm
      first
        | (simp only [st_ld_ne] at *; exact hterm)
        | (rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)]; exact hterm)
        | exact hterm
    have key := hv.found_step hc (Or.inl ⟨hl0, rfl⟩) ht2 htl hft
    rw [← hSr] at key
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc20.step.isTrue.isTrue.isFalse.post.success.isFalse =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu hscan
    simp at hinv hm2 hl0 hu hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨L, t, hL, hnz, ht2, htL, hft, hSr⟩ := hscan.1.found_end hu
    -- the scan stopped inside the record
    have htl : t < rr.2.length := by
      obtain ⟨a', b', tl', hr2, -, -, hrec⟩ := hv.slot
      have hcb := hv.core.database.record_ge hv.hr; simp only [clausesAt] at hcb
      have hn1 := hv.core.layout.nVars_pos
      refine Classical.byContradiction fun hge => ?_
      have hlen2 : 2 ≤ rr.2.length := by rw [hr2]; simp
      have := hnz rr.2.length (by omega) (by omega)
      apply this
      have hterm := hrec.2; rw [← hc] at hterm
      first
        | (simp only [st_ld_ne] at *; exact hterm)
        | (rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)]; exact hterm)
        | exact hterm
    have key := hv.found_step hc (Or.inr ⟨hl0, rfl⟩) ht2 htl hft
    rw [← hSr] at key
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc30.step.isTrue.isFalse.isTrue.post.success.isFalse =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu hscan
    simp at hinv hm2 hl0 hu hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨L, t, hL, hnz, ht2, htL, hft, hSr⟩ := hscan.1.found_end hu
    -- the scan stopped inside the record
    have htl : t < rr.2.length := by
      obtain ⟨a', b', tl', hr2, -, -, hrec⟩ := hv.slot
      have hcb := hv.core.database.record_ge hv.hr; simp only [clausesAt] at hcb
      have hn1 := hv.core.layout.nVars_pos
      refine Classical.byContradiction fun hge => ?_
      have hlen2 : 2 ≤ rr.2.length := by rw [hr2]; simp
      have := hnz rr.2.length (by omega) (by omega)
      apply this
      have hterm := hrec.2; rw [← hc] at hterm
      first
        | (simp only [st_ld_ne] at *; exact hterm)
        | (rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)]; exact hterm)
        | exact hterm
    have key := hv.found_step hc (Or.inl ⟨hl0, rfl⟩) ht2 htl hft
    rw [← hSr] at key
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc40.step.isTrue.isFalse.isFalse.post.success.isFalse =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu hscan
    simp at hinv hm2 hl0 hu hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hvar' : mb = (linksAfter S w).length := hvar
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨L, t, hL, hnz, ht2, htL, hft, hSr⟩ := hscan.1.found_end hu
    -- the scan stopped inside the record
    have htl : t < rr.2.length := by
      obtain ⟨a', b', tl', hr2, -, -, hrec⟩ := hv.slot
      have hcb := hv.core.database.record_ge hv.hr; simp only [clausesAt] at hcb
      have hn1 := hv.core.layout.nVars_pos
      refine Classical.byContradiction fun hge => ?_
      have hlen2 : 2 ≤ rr.2.length := by rw [hr2]; simp
      have := hnz rr.2.length (by omega) (by omega)
      apply this
      have hterm := hrec.2; rw [← hc] at hterm
      first
        | (simp only [st_ld_ne] at *; exact hterm)
        | (rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)]; exact hterm)
        | exact hterm
    have key := hv.found_step hc (Or.inr ⟨hl0, rfl⟩) ht2 htl hft
    rw [← hSr] at key
    exact ⟨by rw [hvar']; exact key.2.2, key.1, by rw [key.2.1, hnl']⟩
  case vc8.step.isTrue.isTrue.isTrue.post.success.isTrue.isFalse.isFalse.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf jp3 hlem hscan
    simp at hinv hm2 hl0 hu hny hyf hf hlem hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S.st (clause + 1) (S.ld (clause + 1 + 1))).st (clause + 1 + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inl ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inl ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    rw [hT] at hlem ⊢
    have key := hv.conflict_step hc (Or.inl ⟨hl0, rfl⟩) hf hall (f' := 1) (by simp; exact hlem)
    exact ⟨key.1, Or.inr (by rw [← hnl']; exact key.2)⟩
  case vc9.step.isTrue.isTrue.isTrue.post.success.isTrue.isFalse.isFalse.isFalse.isFalse =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf jp3 hlem hscan
    simp at hinv hm2 hl0 hu hny hyf hf hlem hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S.st (clause + 1) (S.ld (clause + 1 + 1))).st (clause + 1 + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inl ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inl ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    rw [hT] at hlem ⊢
    have key := hv.conflict_step hc (Or.inl ⟨hl0, rfl⟩) hf hall (f' := f) (by rw [hf]; simp; exact hlem)
    exact ⟨key.1, Or.inr (by rw [← hnl']; exact key.2)⟩
  case vc18.step.isTrue.isTrue.isFalse.post.success.isTrue.isFalse.isFalse.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf jp3 hlem hscan
    simp at hinv hm2 hl0 hu hny hyf hf hlem hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S).st (clause + 1 + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inr ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inr ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    rw [hT] at hlem ⊢
    have key := hv.conflict_step hc (Or.inr ⟨hl0, rfl⟩) hf hall (f' := 1) (by simp; exact hlem)
    exact ⟨key.1, Or.inr (by rw [← hnl']; exact key.2)⟩
  case vc19.step.isTrue.isTrue.isFalse.post.success.isTrue.isFalse.isFalse.isFalse.isFalse =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf jp3 hlem hscan
    simp at hinv hm2 hl0 hu hny hyf hf hlem hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_pos hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S).st (clause + 1 + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inr ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inr ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    rw [hT] at hlem ⊢
    have key := hv.conflict_step hc (Or.inr ⟨hl0, rfl⟩) hf hall (f' := f) (by rw [hf]; simp; exact hlem)
    exact ⟨key.1, Or.inr (by rw [← hnl']; exact key.2)⟩
  case vc28.step.isTrue.isFalse.isTrue.post.success.isTrue.isFalse.isFalse.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf jp3 hlem hscan
    simp at hinv hm2 hl0 hu hny hyf hf hlem hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S.st (clause) (S.ld (clause + 1))).st (clause + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inl ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inl ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    rw [hT] at hlem ⊢
    have key := hv.conflict_step hc (Or.inl ⟨hl0, rfl⟩) hf hall (f' := 1) (by simp; exact hlem)
    exact ⟨key.1, Or.inr (by rw [← hnl']; exact key.2)⟩
  case vc29.step.isTrue.isFalse.isTrue.post.success.isTrue.isFalse.isFalse.isFalse.isFalse =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf jp3 hlem hscan
    simp at hinv hm2 hl0 hu hny hyf hf hlem hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S.st (clause) (S.ld (clause + 1))).st (clause + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inl ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inl ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    rw [hT] at hlem ⊢
    have key := hv.conflict_step hc (Or.inl ⟨hl0, rfl⟩) hf hall (f' := f) (by rw [hf]; simp; exact hlem)
    exact ⟨key.1, Or.inr (by rw [← hnl']; exact key.2)⟩
  case vc38.step.isTrue.isFalse.isFalse.post.success.isTrue.isFalse.isFalse.isFalse.isTrue =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf jp3 hlem hscan
    simp at hinv hm2 hl0 hu hny hyf hf hlem hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S).st (clause + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inr ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inr ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    rw [hT] at hlem ⊢
    have key := hv.conflict_step hc (Or.inr ⟨hl0, rfl⟩) hf hall (f' := 1) (by simp; exact hlem)
    exact ⟨key.1, Or.inr (by rw [← hnl']; exact key.2)⟩
  case vc39.step.isTrue.isFalse.isFalse.post.success.isTrue.isFalse.isFalse.isFalse.isFalse =>
    rename_i _ b1 mb1 s3 So fo1 hlt lit Sw w2 hout b mb s2 S s1 f w hne clause jp1 hm2 jp hl0 hinv r Sr s0 unit hu T w' hny hyf hf jp3 hlem hscan
    simp at hinv hm2 hl0 hu hny hyf hf hlem hscan ⊢
    obtain ⟨hvar, -, hw, hnl⟩ := hinv
    have hw' : WInv input S0 vs0 (processedPos So) lit S f w := hw
    have hnl' : S.nLemmas = So.nLemmas := hnl
    have hne' : S.ld w ≠ END := by simpa using hne
    obtain ⟨db, vs, visited, rest, rr, hv⟩ := hw'.visit hne'
    have hc := hv.hc
    rw [if_neg hm2] at hc
    obtain ⟨hSr, L, hL, hnz, hi2, hiL, hfl, hend⟩ := hscan.1.unit_end hu hscan.2
    have hT : T = (S).st (clause + 1) lit := by simp only [T, Sr]; rw [hSr]
    obtain ⟨hTc, hTf⟩ := hv.unit_flag hc (Or.inr ⟨hl0, rfl⟩)
    have hymem : otherLit rr lit ∈ rr.2 := by
      obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
    have hyS : flag S (otherLit rr lit) ≠ 0 := by
      rw [hT, hTc, hTf _ (by omega) (by omega)] at hyf; exact hyf
    have hall := hv.scan_all_false hc (Or.inr ⟨hl0, rfl⟩) hL hnz hi2 hiL hfl hend hyS
    rw [hT] at hlem ⊢
    have key := hv.conflict_step hc (Or.inr ⟨hl0, rfl⟩) hf hall (f' := f) (by rw [hf]; simp; exact hlem)
    exact ⟨key.1, Or.inr (by rw [← hnl']; exact key.2)⟩

end MicrosatLean.Faithful.Verification

namespace MicrosatLean.Faithful.Verification

/-- What `propagate` returns, from the top of `solve`'s loop. Used by `step`'s proof. -/
theorem propagate_spec {input : Input} {S : solver} {d : CInt} (inv : Inv input S d) :
    ((propagate S).2 = UNSAT ∧ input.Unsat) ∨
    ((propagate S).2 = SAT ∧ (propagate S).1.maxLemmas = S.maxLemmas ∧
      (((propagate S).1.nLemmas = S.nLemmas ∧ trailLen S ≤ trailLen (propagate S).1 ∧
          ∃ db vs, Settled input (propagate S).1 db vs ∧ Cursor (propagate S).1 vs d) ∨
        (S.nLemmas < (propagate S).1.nLemmas ∧
          ∃ db vs, Settled input (propagate S).1 db vs))) := by
  obtain ⟨db0, vs0, core0, watched0, mode0, cursor0⟩ := inv
  rcases propagate_main (d0 := d) core0 watched0 mode0 with h | ⟨hs, db, vs, hset, hml, hrel⟩
  · exact Or.inl h
  · refine Or.inr ⟨hs, hml, ?_⟩
    rcases hrel with ⟨hn, rfl, hlen, htr⟩ | hlt
    · refine Or.inl ⟨hn, hlen, db, vs, hset, ?_⟩
      obtain ⟨k, hk, hd, before⟩ := cursor0
      refine ⟨k, hk, hd, fun j hj hjk => ?_⟩
      obtain ⟨i, hi, he⟩ := before j hj hjk
      exact ⟨i, by omega, by rw [htr i hi]; exact he⟩
    · exact Or.inr ⟨hlt, db, vs, hset⟩

end MicrosatLean.Faithful.Verification
