import MicrosatLean.Fast.Verification.Inv
import MicrosatLean.Fast.Verification.AnalyzeBuild
import MicrosatLean.Fast.Verification.AnalyzeLearn

/-!
# `analyze` of the fast port (C:102–130)

`conflict_fast` is the faithful `Visit.conflict_step` for the fast `analyze` followed by the
assignment of the lemma (`conflictNext`): either memory runs out (the lemma pointer is
negative), or the outer invariant of `propagate` holds again with one more lemma.

The proof follows `Visit.conflict_step`: `analyze_core_fast` (`AnalyzeBuild.lean`) replaces
`analyzeCore_spec`, the fast `addClause` meets `AddClausePost` (`addClause_post`), and
`analyzed_learn` (`AnalyzeLearn.lean`) is `Analyzed.learn` for that postcondition.
The helper lemmas of `Analyze*.lean` live in the namespace `AnalyzeAux` (and `FastLearn`).
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

namespace AnalyzeAux

/-- The fast `analyze` as its loops, the terminator of the buffer and `addClause` (C:102–130).
`fast` and `slow` are left unnamed. -/
theorem analyze_eq (L : Lay) (t : St) (c : Cell) :
    let R1 := bumpLoop L t.db t.head c
    let R2 := resolveLoop L R1.1 R1.2 t.assigned
    let R3 := buildLoop L R2.1 t.forced R2.2.2 0 0 false R2.2.2
    let R5 := addClause L (st (unassignLoop L R3.1 R2.2.2 R3.2.2.2) (L.buffer + R3.2.1) 0) t.memUsed L.buffer R3.2.1
    ∃ fa sl, analyze L t c = ({ t with
      db := R5.1
      memUsed := R5.2.1
      nLemmas := t.nLemmas + 1
      nConflicts := t.nConflicts + 1
      processed := R3.2.2.2
      assigned := R3.2.2.2
      head := R2.2.1
      fast := fa
      slow := sl }, R5.2.2) := by
  intro R1 R2 R3 R5
  exact ⟨_, _, rfl⟩

/-- Records tiling `[a, b)` take at least 3 cells each. -/
theorem Tiling.length_le {S : solver} {a b : Int} {rs : List Record} (h : Tiling S a b rs) :
    3 * rs.length ≤ b - a := by
  induction h with
  | nil p => simp
  | cons _ _ ih => simp only [List.length_cons]; omega

end AnalyzeAux

open AnalyzeAux

/-- C:154–158 below the root: the record `r` (at `c`) is false, `t` is the fast state at the
conflict (after C:149 placed `lit` at `clause[1]`). Used by `propLoop`'s proof. -/
theorem conflict_fast {input : Input} {S0 : solver} {vs0 : List Int} {P : Nat} {lit : Int}
    {S : solver} {f w : Int} {db : Records} {vs : List Int} {visited rest : List Int} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : Cell} (hc : c.toInt = r.1)
    {Ss : solver}
    (hSs : (S.ld c.toInt = lit ∧ Ss = S.st c.toInt (S.ld (c.toInt + 1))) ∨ (S.ld c.toInt ≠ lit ∧ Ss = S))
    (hf : f = 0) (hfalse : ∀ l ∈ r.2, ∃ j < trailLen S, trailAt S j = l)
    {L : Lay} {t : St} {fa sl : Int} (hB : Bounds L t)
    (ht : abs L t (memoryBound input) fa sl = Ss.st (c.toInt + 1) lit) :
    (analyze L t c).2.toInt < 0 ∨
      (Bounds L (conflictNext L (analyze L t c)) ∧
        ∃ fa' sl', OutInv input S0 vs0 (abs L (conflictNext L (analyze L t c)) (memoryBound input) fa' sl')
            (if ld (analyze L t c).1.db ((analyze L t c).2 + 1) == 0 then 1 else 0) ∧
          S.nLemmas < (conflictNext L (analyze L t c)).nLemmas.toInt) := by
  subst hf
  -- the faithful conflict state `T` (as in `Visit.conflict_step`)
  obtain ⟨core', hlow, -, hnl, hml⟩ := hv.unit_core hc hSs
  obtain ⟨-, hperm, -, -⟩ := hv.unit_cells hc hSs
  have hwat := hv.conflict_watched hc hSs
  generalize hTd : Ss.st (c.toInt + 1) lit = T at *
  have ht0 := hv.core.trail; have hl0 := hv.core.layout
  generalize hdbu : db.update c.toInt (unitLits r lit) (decide (S.ld w = c.toInt - 2)) = dbu at core' hwat
  have hmemr : (c.toInt, unitLits r lit) ∈ dbu.all := by
    rw [← hdbu, Records.update_all]; exact List.mem_map.mpr ⟨r, hv.hr, by simp [hc]⟩
  have hin : dbu.inputs ≠ [] := fun he => by
    have hm := hmemr
    rw [Records.all, he, core'.database.no_lemmas he] at hm
    simp at hm
  have hmode : PMode T 0 P := hlow.pmode ht0 hl0 hv.pmode
  have hP' : P < trailLen T := by rw [hlow.trailLen ht0 hl0]; exact hv.hP
  have hlitP : trailAt T P = lit := by rw [hlow.trailAt ht0 hl0 hv.hP]; exact hv.hlit
  have hfalse' : ∀ l ∈ (c.toInt, unitLits r lit).2, ∃ j < trailLen T, trailAt T j = l := fun l hl' => by
    obtain ⟨j, hj, he⟩ := hfalse l (hperm.mem_iff.mp hl')
    exact ⟨j, by rw [hlow.trailLen ht0 hl0]; exact hj, by rw [hlow.trailAt ht0 hl0 hj]; exact he⟩
  -- the last decision `D` (as in `analyzeCore_spec`)
  obtain ⟨hm1, hm2⟩ := id hmode
  rcases hm1 with ⟨h0, -⟩ | ⟨-, hroot, hdec⟩
  · exact absurd rfl h0
  obtain ⟨D0, hD0f, hD0P, hD0⟩ := hdec hP'
  obtain ⟨D, hDP, hD, hlast⟩ := last_decision ⟨D0, hD0P, hD0⟩
  have ctx : ACtx input T dbu vs D := by
    refine ⟨core', hD, ?_, by omega, fun k h1 h2 => ?_, hroot⟩
    · exact Classical.byContradiction fun hlt =>
        core'.trail.forced_root D (by omega) D (Nat.le_refl _) hD
    · rcases Nat.lt_or_ge P k with h3 | h3
      · exact hm2 k h3 h2
      · exact hlast k h1 h3
  -- `T` is the abstraction of `t`
  have hn := ctx.num
  obtain ⟨hNv1, hNv2⟩ := hB.nVars
  have hTv : T.nVars = L.nVars.toInt := by rw [← ht]; rfl
  have env : FEnv T L := ⟨⟨by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [hTv]; omega,
    by rw [← ht]; exact hB.memUsed⟩, by rw [← ht]; rfl, by rw [← ht]; rfl, by rw [← ht]; rfl⟩
  have hDB : T.DB = toDB t.db := by rw [← ht]; rfl
  have hA : T.assigned = t.assigned.toInt := by rw [← ht]; rfl
  have hH : T.head = t.head.toInt := by rw [← ht]; rfl
  have hF : T.forced = t.forced.toInt := by rw [← ht]; rfl
  obtain ⟨Ls, vs', B, han, hBD, hsz5⟩ := analyze_core_fast (L := L) ctx env hmemr hfalse'
    ⟨P, hDP, hP', by rw [hlitP]; simp [unitLits]⟩ hDP hwat hDB hB.size hA hH hF (c := c) rfl (t.nConflicts + 1).toInt
  obtain ⟨fa1, sl1, hAn⟩ := analyze_eq L t c
  generalize bumpLoop L t.db t.head c = R1 at han hsz5 hAn
  generalize resolveLoop L R1.1 R1.2 t.assigned = R2 at han hsz5 hAn
  generalize buildLoop L R2.1 t.forced R2.2.2 0 0 false R2.2.2 = R3 at han hsz5 hAn
  generalize st (unassignLoop L R3.1 R2.2.2 R3.2.2.2) (L.buffer + R3.2.1) 0 = db4 at han hsz5 hAn
  rw [hAn]
  obtain ⟨db2, head2, a2⟩ := R2
  obtain ⟨db3, size, lbd, proc⟩ := R3
  dsimp only at han hAn ⊢
  have hone : ((1 : Cell)).toInt = 1 := rfl
  have h3 : ((3 : Cell)).toInt = 3 := rfl
  have hmu : T.mem_used = t.memUsed.toInt := by rw [← ht]; rfl
  have hmuB := hB.memUsed
  -- the learned clause fits in the arrays
  have hsizeL : size.toInt = Ls.length := han.size_eq
  have hLlen : Ls.length ≤ T.nVars.toNat := clause_length_le han.shape.1 han.shape.2
  have hlitL : ∀ l ∈ Ls, InRange T.nVars l := han.shape.2
  have hmemT : 10 * T.nVars + 8 ≤ T.mem_used := by
    have b1 := core'.database.inputs_tile.bounds; have b2 := core'.database.lemmas_tile.bounds
    simp only [clausesAt] at b1 b2; omega
  have hsu : (t.memUsed + size).toInt = t.memUsed.toInt + size.toInt := toInt_add (by omega) (by omega)
  have hsu3 : (t.memUsed + size + 3).toInt = t.memUsed.toInt + size.toInt + 3 := by
    rw [toInt_add (by rw [hsu, h3]; omega) (by rw [hsu, h3]; omega), hsu, h3]
  by_cases hoom : t.memUsed + size + 3 > memMax
  · left
    have hN : (addClause L db4 t.memUsed L.buffer size).2.2 = NONE := by unfold addClause; rw [ite_eq_left hoom]
    rw [hN]; decide
  right
  have hnoom : t.memUsed.toInt + size.toInt + 3 ≤ 2 ^ 30 := by
    have : ¬ memMax.toInt < (t.memUsed + size + 3).toInt := fun h => hoom (Int32.lt_iff_toInt_lt.mpr h)
    rw [hsu3, memMax_toInt] at this; omega
  -- C:130: the fast `addClause` meets `AddClausePost`
  have hbufT := env.buffer
  have hfirstT : T.first = L.first.toInt := by rw [← ht]; rfl
  have hnl0 : T.nLemmas = t.nLemmas.toInt := by rw [← ht]; rfl
  have hnd : Ls.Nodup := List.Pairwise.of_map Int.natAbs (fun a b hab he => hab (by rw [he])) han.shape.1
  have hcnt : 0 ≤ t.nLemmas.toInt ∧ t.nLemmas.toInt < 2 ^ 30 := by
    have h1 := core'.database.nLemmas
    have h2 := Tiling.length_le core'.database.lemmas_tile
    have h3 := core'.database.inputs_tile.bounds.1
    simp only [clausesAt] at h3
    omega
  have hAeq : abs L { t with db := db4, assigned := proc, processed := proc, head := head2, nConflicts := t.nConflicts + 1 }
      (memoryBound input) fa sl =
      AS T (t.nConflicts + 1).toInt db4 proc.toInt proc.toInt head2.toInt := by rw [← ht]; rfl
  obtain ⟨hp1, hp2, hp3, hpost⟩ := addClause_post (L := L)
    (s := { t with db := db4, assigned := proc, processed := proc, head := head2, nConflicts := t.nConflicts + 1 })
    (M := memoryBound input) (fa := fa) (sl := sl) (src := L.buffer) (size := size) (Ls := Ls) false hsz5 hsizeL
    (fun i h => by rw [hAeq, ← hbufT]; exact han.buffer_eq i h) (by omega) (by omega) (Or.inl (by simp only; omega))
    (fun h2 i hi => by
      have hm : Ls[i]! ∈ Ls := by rw [getElem!_pos Ls i (by omega)]; exact List.getElem_mem _
      have := inRange_iff.mp (hlitL _ hm)
      simp only; omega)
    (fun h2 => (first_two h2 hnd).2.2.1) (by simp only; omega) (by simp only; omega) (by omega)
    (fun l hl => by have := inRange_iff.mp (hlitL l hl); omega) (by simp only; exact hcnt)
  dsimp only at hp1 hp2 hp3 hpost
  simp only [Bool.false_eq_true, ↓reduceIte] at hpost
  rw [hAeq] at hpost
  generalize addClause L db4 t.memUsed L.buffer size = AC at hp1 hp2 hp3 hpost ⊢
  obtain ⟨db5, mu5, ptr⟩ := AC
  dsimp only at hp1 hp2 hp3 hpost ⊢
  generalize hsR : ({ db := db5, memUsed := mu5, memFixed := t.memFixed, maxLemmas := t.maxLemmas, nLemmas := t.nLemmas + 1, nConflicts := t.nConflicts + 1, forced := t.forced, processed := proc, assigned := proc, head := head2, fast := t.fast, slow := t.slow } : St) = sR at hpost
  generalize hR1 : abs L sR (memoryBound input) fa sl = R1s at hpost
  have hR1DB : R1s.DB = toDB db5 := by rw [← hR1, ← hsR]; rfl
  -- C:157: the flag is set exactly for a unit lemma
  have hp1' : (ptr + 1).toInt = ptr.toInt + 1 := by
    rw [toInt_add (by rw [hone]; omega) (by rw [hone]; omega), hone]
  have hld1 : R1s.ld (ptr.toInt + 1) = (ld db5 (ptr + 1)).toInt := by
    rw [ld_sim R1s hR1DB hp3, hp1']
  have hf' : ((if (ld db5 (ptr + 1) == 0) = true then (1 : Int) else 0) ≠ 0) ↔ R1s.ld (ptr.toInt + 1) = 0 := by
    rw [hld1]
    by_cases hz : (ld db5 (ptr + 1) == 0) = true
    · rw [ite_eq_left hz, beq_cell.mp hz]; exact ⟨fun _ => rfl, fun _ => by decide⟩
    · rw [ite_eq_right hz]; exact ⟨fun h => absurd rfl h, fun h => absurd (beq_cell.mpr h) hz⟩
  obtain ⟨db'', core2, hwt, hpm, hnl2, hml2⟩ :=
    FastLearn.analyzed_learn han (by omega) core' hmode hin hpost hwat hf'
  -- the fast assignment of the lemma is the faithful one (C:158)
  have hpos : 0 < Ls.length := List.length_pos_iff.mpr han.nonempty
  have hlit0 : R1s.ld ptr.toInt = Ls[0]! := by
    have := hpost.2.2.1 0 hpos
    rw [getElem!_pos Ls 0 hpos]; simpa using this
  have hL0 := inRange_iff.mp (hlitL Ls[0]! (by rw [getElem!_pos Ls 0 hpos]; exact List.getElem_mem hpos))
  have hfls := env.ienv.fls; have hrs := env.ienv.reason
  have hptr : 0 ≤ ptr.toInt ∧ ptr.toInt < 2 ^ 30 := by omega
  obtain ⟨e6, s6⟩ := assign_sim R1s (db := db5) hR1DB hp3 (L := L) (by rw [← hR1]; rfl) (by rw [← hR1]; rfl)
    (by rw [← hR1]; rfl) (by omega) (assigned := proc) (by rw [← hR1, ← hsR]; rfl) (reason := ptr) hptr
    (by rw [hlit0]; omega) (ld db5 (ptr + 1) == 0)
  obtain ⟨DBa, hDBa⟩ := MicrosatLean.Faithful.Verification.assign_fields R1s ptr.toInt
    (if (ld db5 (ptr + 1) == 0) = true then 1 else 0)
  rw [hDBa] at e6 hwt hpm core2 hnl2 hml2
  change DBa = _ at e6
  have hprocB : proc.toInt = T.falseStack + B := by
    obtain ⟨DB', hh, rr, nn, ff, ss, hS'⟩ := han.fields
    have := congrArg solver.assigned hS'
    simpa using this
  have hBt := han.cut.1
  have hpr1 : (proc + 1).toInt = proc.toInt + 1 := by
    rw [toInt_add (by rw [hone]; omega) (by rw [hone]; omega), hone]
  have hFeq : abs L (conflictNext L (({ db := db5, memUsed := mu5, memFixed := t.memFixed, maxLemmas := t.maxLemmas, nLemmas := t.nLemmas + 1, nConflicts := t.nConflicts + 1, forced := t.forced, processed := proc, assigned := proc, head := head2, fast := fa1, slow := sl1 } : St), ptr)) (memoryBound input) fa sl =
      { R1s with DB := DBa, assigned := R1s.assigned + 1 } := by
    rw [e6, ← hR1, ← hsR]
    simp only [conflictNext, abs, hpr1]
  have hrel := hv.rel
  refine ⟨⟨s6, hB.nVars, by show mu5.toInt ≤ 2 ^ 30; omega, hB.maxLemmas⟩, fa, sl, ?_, ?_⟩
  · rw [hFeq]
    refine ⟨db'', vs', core2, hwt, hpm, by rw [hml2, hml]; exact hrel.1, Or.inr ?_⟩
    rw [hnl2, hnl]; rcases hrel.2 with ⟨h1, -⟩ | h1 <;> omega
  · show S.nLemmas < (t.nLemmas + 1).toInt
    rw [toInt_add (by rw [hone]; omega) (by rw [hone]; omega), hone]; omega

end MicrosatLean.Fast.Verification
