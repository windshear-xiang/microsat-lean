import MicrosatLean.Faithful.Verification.VisitUnit

/-!
# A visited clause that became unit (C:153–154)

When the scan finds no literal to watch and the other watched literal `y` is unassigned,
`propagate` assigns `y` with the clause as its reason.
-/

namespace MicrosatLean.Faithful.Verification

/-- `propagate`'s mode survives pushing a non-decision literal. -/
theorem Push.pmode {S T : solver} {x tag rv : CInt} (hp : Push S T x tag rv) (hf : Fresh S x)
    (hrv : rv ≠ 0) {f : CInt} {P : Nat} (hm : PMode S f P) (hP : P < trailLen S) : PMode T f P := by
  have hlen := hp.trailLen_eq hf
  have hfp : forcedPos T = forcedPos S := by simp only [forcedPos, hp.keeps.2.1, hp.shape.falseStack]
  obtain ⟨h1, h2⟩ := hm
  have hnd : ∀ k, k < trailLen T → (IsDecision T k ↔ k < trailLen S ∧ IsDecision S k) := by
    intro k hk
    rcases Nat.lt_or_ge k (trailLen S) with hk' | hk'
    · rw [hp.isDecision_lt hf hk']; exact ⟨fun h => ⟨hk', h⟩, fun h => h.2⟩
    · have : k = trailLen S := by omega
      subst this; rw [hp.isDecision_top hf]; exact ⟨fun h => absurd h hrv, fun h => absurd h.1 (by omega)⟩
  have hroot : ∀ i < trailLen T, (RootLevel T i ↔ ∀ k ≤ i, k < trailLen S → ¬ IsDecision S k) := by
    intro i hi
    constructor
    · intro h k hk hks hd; exact h k hk ((hnd k (by omega)).mpr ⟨hks, hd⟩)
    · intro h k hk hd; obtain ⟨hks, hd'⟩ := (hnd k (by omega)).mp hd; exact h k hk hks hd'
  refine ⟨?_, fun k hk1 hk2 hd => ?_⟩
  · rcases h1 with ⟨hf0, hr⟩ | ⟨hf0, hb, hd⟩
    · refine Or.inl ⟨hf0, fun i hi => (hroot i hi).mpr fun k hk hks => hr k hks k (Nat.le_refl _)⟩
    · obtain ⟨D, hD1, hD2, hD3⟩ := hd hP
      refine Or.inr ⟨hf0, fun i hi hr => ?_, fun _ => ⟨D, by rw [hfp]; exact hD1, hD2,
        (hnd D (by omega)).mpr ⟨by omega, hD3⟩⟩⟩
      rw [hfp]
      rcases Nat.lt_or_ge i (trailLen S) with hi' | hi'
      · exact hb i hi' ((hp.rootLevel_lt hf hi').mp hr)
      · exact absurd hD3 ((hroot i hi).mp hr D (by omega) (by omega))
  · obtain ⟨hks, hd'⟩ := (hnd k hk2).mp hd; exact h2 k hk1 hks hd'

/-- C:153–154: the other watched literal is unassigned, so it is assigned with the visited
clause as its reason; then the next link is visited. -/
theorem Visit.assign_step {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S))
    {L i : CInt} (hL : Ss.ld (c + L) = 0) (hnz : ∀ t, 2 ≤ t → t < L → Ss.ld (c + t) ≠ 0)
    (hi2 : 2 ≤ i) (hiL : i ≤ L) (hfl : ∀ t, 2 ≤ t → t < i → flag Ss (Ss.ld (c + t)) ≠ 0)
    (hend : Ss.ld (c + i) = 0)
    (hyt : flag S (-(otherLit r lit)) = 0) (hyf : flag S (otherLit r lit) = 0) :
    WInv input S0 vs0 P lit (assign (Ss.st (c + 1) lit) c f) f ((Ss.st (c + 1) lit).ld w) ∧
    (assign (Ss.st (c + 1) lit) c f).nLemmas = S.nLemmas ∧
    (linksAfter (assign (Ss.st (c + 1) lit) c f) ((Ss.st (c + 1) lit).ld w)).length <
      (linksAfter S w).length := by
  obtain ⟨core', hlow, hhead, hnl, hml⟩ := hv.unit_core hc hSs
  obtain ⟨hcl, hperm, hcells, DB, hTe⟩ := hv.unit_cells hc hSs
  obtain ⟨hlinks, hhd⟩ := hv.cells_ne hc
  obtain ⟨hTc, -⟩ := hv.unit_flag hc hSs
  have hrest := hv.scan_rest_false hc hSs hL hnz hi2 hiL hfl hend
  generalize hTd : Ss.st (c + 1) lit = T at *
  have ht := hv.core.trail; have hl := hv.core.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hcb := hv.core.database.record_ge hv.hr; rw [← hc] at hcb; simp only [clausesAt] at hcb
  have hP := hv.hP
  generalize hyd : otherLit r lit = y at *
  have hymem : y ∈ r.2 := by
    obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
    rw [← hyd]; simp only [otherLit, hr2]; split <;> simp
  have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
  -- `y` is unassigned
  have hfree : ∀ k < trailLen S, abs (trailAt S k) ≠ abs y := fun k hk he => by
    have hfk := ht.flag_ne_zero hk
    rcases abs_cases (trailAt S k) with ⟨_, e1⟩ | ⟨_, e1⟩ <;> rcases abs_cases y with ⟨_, e2⟩ | ⟨_, e2⟩
    all_goals first
      | (rw [show trailAt S k = y by omega] at hfk; exact hfk hyf)
      | (rw [show trailAt S k = -y by omega] at hfk; exact hfk hyt)
  have hyin : InRange T.nVars (-y) := by
    rw [hlow.shape.nVars]; exact inRange_iff.mpr ⟨by omega, by omega, by omega⟩
  have hfresh : Fresh T (-y) := ⟨core'.layout, core'.trail, hyin, fun k hk he => by
      rw [hlow.trailLen ht hl] at hk; rw [hlow.trailAt ht hl hk, abs_neg'] at he; exact hfree k hk he⟩
  have hpush : Push T (assign T c f) (-y) (if f != 0 then IMPLIED else 1) (1 + c) := by
    have := assign_push core'.layout core'.trail (c := c) (f := f) (by omega)
      (by rw [hTc, hlow.shape.nVars]; exact inRange_iff.mpr ⟨by omega, by omega, by omega⟩)
    rw [hTc] at this; exact this
  generalize hT2d : assign T c f = T2 at *
  have hlenT := hlow.trailLen ht hl
  have hlen2 := hpush.trailLen_eq hfresh
  obtain ⟨hA2, hF2, hP2, hH2, hU2, hFx2, hN2, hM2, hMM2⟩ := hpush.keeps
  have hrv : (1 + c) ≠ 0 := by omega
  -- the root: with `forced` set, the whole trail is at the root
  have hPm := hv.pmode
  have hrootTop : RootLevel T2 (trailLen T) ↔ f ≠ 0 := by
    rw [hpush.rootLevel_top hfresh]
    constructor
    · rintro ⟨hnd, -⟩ hf0
      rcases hPm.1 with ⟨hf, -⟩ | ⟨-, -, hd⟩
      · exact hf hf0
      · obtain ⟨D, -, hD, hDd⟩ := hd hv.hP
        exact hnd D (by rw [hlenT]; omega) ((hlow.isDecision ht hl (by omega)).mpr hDd)
    · intro hf0
      rcases hPm.1 with ⟨-, hr⟩ | ⟨hf, -, -⟩
      · refine ⟨fun k hk hd => ?_, hrv⟩
        rw [hlenT] at hk
        exact hr k hk k (Nat.le_refl _) ((hlow.isDecision ht hl hk).mp hd)
      · exact absurd hf hf0
  have hdb' := core'.database
  -- the visited record, now `y :: lit :: …`, is the reason
  have hmemr : (c, unitLits r lit) ∈ (db.update c (unitLits r lit) (decide (S.ld w = c - 2))).all := by
    rw [Records.update_all]; exact List.mem_map.mpr ⟨r, hv.hr, by simp [hc]⟩
  have hlitP : FalseAt T lit P := (hlow.falseAt ht hl).mpr ⟨hv.hP, hv.hlit⟩
  have hnodecT : ∀ k, P < k → k < trailLen T → ¬ IsDecision T k := fun k h1 h2 =>
    (not_congr (hlow.isDecision ht hl (by omega))).mpr (hPm.2 k h1 (by omega))
  obtain ⟨hla, hdb2, hwl2, hol2⟩ := hpush.frames hfresh hdb' core'.watches core'.order
  have core2 : Core input T2 (db.update c (unitLits r lit) (decide (S.ld w = c - 2))) vs := by
    refine ⟨core'.valid, by rw [hpush.shape.nVars]; exact core'.nVars, by rw [hMM2]; exact core'.memory,
      by rw [hM2]; exact core'.maxLemmas, hla, hpush.trail hfresh ⟨fun hr => ?_, fun hr => ?_⟩,
      hpush.rootEntailed hfresh core'.root fun hr => ?_, hdb2, hwl2,
      hpush.reasons hfresh core'.reasons fun _ _ => ?_, hpush.units hfresh core'.units, hol2⟩
    · have := hrootTop.mp hr; simp [this]
    · have : f = 0 := Classical.byContradiction fun h' => hr (hrootTop.mpr h'); simp [this]
    · -- a root unit: its other literals are false at the root
      have hf0 := hrootTop.mp hr
      have hallroot : ∀ k < trailLen S, RootLevel S k := by
        rcases hPm.1 with ⟨-, h'⟩ | ⟨h', -⟩
        · exact h'
        · exact absurd h' hf0
      rw [Int.neg_neg]
      refine Input.entails_unit (cl := r.2) (hv.core.record_entailed hv.hr)
        (fun l hl' => (inRange_iff.mp (hv.core.record_lit hv.hr hl')).1) fun l hl' hly => ?_
      obtain ⟨j, hj, he⟩ := hrest l hl' hly
      have := hv.core.root j hj (hallroot j hj); rw [he] at this; exact this
    · refine ⟨(c, unitLits r lit), hmemr, rfl, by simp [unitLits, hyd], fun l hl' => ?_, fun _ => ?_⟩
      · simp only [unitLits, List.drop_succ_cons, List.drop_zero, List.mem_cons] at hl'
        rcases hl' with rfl | hl'
        · exact ⟨P, by rw [hlenT]; exact hv.hP, hlitP⟩
        · obtain ⟨j, hj, he⟩ := hrest l (List.mem_of_mem_drop hl') fun hly => by
            have hnd := hv.core.record_nodup hv.hr
            obtain ⟨a, b, tl, hr2, hab, hne, _⟩ := hv.slot
            rw [hr2] at hl' hnd
            simp only [List.drop_succ_cons, List.drop_zero] at hl'
            rw [← hyd] at hly
            simp only [otherLit, hr2] at hly
            split at hly <;> simp_all
          exact ⟨j, by rw [hlenT]; exact hj, (hlow.falseAt ht hl).mpr ⟨hj, he⟩⟩
      · exact ⟨lit, by simp [unitLits], P, by rw [hlenT]; exact hv.hP, hlitP, hnodecT⟩
  have hpp2 : processedPos T2 = P + 1 := by
    have h1 := hlow.processedPos ht hl; rw [hv.hpp] at h1
    simp only [processedPos] at h1 ⊢; rw [hP2, hpush.shape.falseStack]; exact h1
  -- link cells and list heads are untouched
  have hhigh : ∀ q, 8 * S.nVars + 6 ≤ q → q ≠ c → q ≠ c + 1 → T2.ld q = S.ld q := fun q h1 h2 h3 => by
    have hf := hfresh.num
    have e1 := hlow.assigned; have e2 := hlow.shape.falseStack; have e3 := hlow.shape.nVars
    have e4 := hlow.shape.false; have e5 := hlow.shape.reason; have e6 := hlow.shape.model
    have hay : abs (-y) ≤ S.nVars := by rw [abs_neg']; rcases abs_cases y with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    have hay0 : 0 ≤ abs (-y) := by rw [abs_neg']; rcases abs_cases y with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    rw [hpush.same q (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact hcells q (by omega) h2 h3
  have hwx : T.ld w = S.ld w := by
    have hwin : w ∈ (S.first + lit) :: visited := by rw [hv.path.end_eq]; exact List.getLast_mem _
    rcases List.mem_cons.mp hwin with he | hm
    · rw [he]; exact hcells _ hhd.1 hhd.2.1 hhd.2.2
    · obtain ⟨h0, h1, h2⟩ := hlinks lit w ((hv.mem w).mp (by simp [hm])); exact hcells _ h0 h1 h2
  have hlinkS : ∀ q, (q = S.first + lit ∨ q ∈ visited ++ S.ld w :: rest) → T2.ld q = S.ld q := by
    intro q hq
    rcases hq with rfl | hq
    · have := inRange_iff.mp (ht.lit _ hv.hP); rw [hv.hlit] at this
      exact hhigh _ (by omega) hhd.2.1 hhd.2.2
    · obtain ⟨h0, h1, h2⟩ := hlinks lit q ((hv.mem q).mp hq)
      have := Watches.link_ge hv.core.database ((hv.mem q).mp hq); simp only [clausesAt] at this
      exact hhigh q (by omega) h1 h2
  have hlistT : ListFrom T2 (S.ld w) rest := hv.list.2.frame fun q hq => by
    rcases hq with rfl | hq
    · exact hlinkS _ (Or.inr (by simp))
    · exact hlinkS q (Or.inr (by simp [hq]))
  have hpos : ∀ q ∈ rest, 0 ≤ q := fun q hq => (hlinks lit q ((hv.mem q).mp (by simp [hq]))).1
  have hfa2 : ∀ {l : CInt} {j : Nat}, FalseAt T2 l j → FalseAt S l j ∨ j = trailLen S := by
    intro l j ⟨hj, he⟩
    rw [hlen2, hlenT] at hj
    rcases Nat.lt_or_ge j (trailLen S) with hj' | hj'
    · left; refine ⟨hj', ?_⟩; rw [← hlow.trailAt ht hl hj', ← hpush.trailAt_lt hfresh (by omega)]; exact he
    · right; omega
  have hfa2' : ∀ {l : CInt} {j : Nat}, FalseAt S l j → FalseAt T2 l j := fun h' =>
    hpush.falseAt_lt hfresh ((hlow.falseAt ht hl).mpr h')
  refine ⟨⟨_, vs, visited ++ [S.ld w], rest, core2, hpp2,
    by rw [hlen2, hlenT]; have := hv.hP; omega,
    by rw [hpush.trailAt_lt hfresh (by rw [hlenT]; exact hv.hP), hlow.trailAt ht hl hv.hP]; exact hv.hlit,
    ?_, by rw [hwx]; exact hlistT, by rw [hpush.shape.first, hlow.shape.first]; simpa using hv.nodup,
    fun link => by rw [hv.unit_watches hc, ← hv.mem, List.append_assoc, List.singleton_append], ?_,
    ?_, ?_⟩, by rw [hN2, hnl], ?_⟩
  · rw [hpush.shape.first, hlow.shape.first, hwx]
    have hpc : ∀ q, (q = S.first + lit ∨ q ∈ visited) → q ≠ w → T2.ld q = S.ld q := by
      intro q hq _
      rcases hq with rfl | hq
      · exact hlinkS _ (Or.inl rfl)
      · exact hlinkS q (Or.inr (by simp [hq]))
    refine (hv.path.frame hpc ?_).snoc ?_
    · exact hv.nodup.sublist (List.Sublist.cons₂ _ (List.sublist_append_left _ _))
    · have hwin : w ∈ (S.first + lit) :: visited := by rw [hv.path.end_eq]; exact List.getLast_mem _
      rcases List.mem_cons.mp hwin with he | hm
      · rw [he]; exact hlinkS _ (Or.inl rfl)
      · exact hlinkS w (Or.inr (by simp [hm]))
  · refine hv.unit_watched hc hpp2 ⟨trailLen T, ⟨by rw [hlen2]; omega, by rw [hyd]; exact hpush.trailAt_top hfresh⟩,
      fun k h1 h2 => ?_⟩
      (hv.unit_hold hc (fun h' => by rw [hlenT] at *; exact hfa2 h') hfa2'
        fun p q hq h' k h1 h2 => (not_congr (hpush.isDecision_lt hfresh (by rw [hlenT]; omega))).mpr
          ((not_congr (hlow.isDecision ht hl (by omega))).mpr (h' k h1 h2)))
      (fun p hp hfa => by
        rcases hfa2 hfa with h' | h'
        · exact hfree p h'.1 (by rw [h'.2, hyd])
        · have := hv.hP; omega)
      (fun p hp hfa => by
        rcases hfa2 hfa with h' | h'
        · exact ht.distinct p h'.1 P hv.hP (by rw [h'.2, hv.hlit])
        · have := hv.hP; omega)
    rcases Nat.lt_or_ge k (trailLen T) with hk | hk
    · exact (not_congr (hpush.isDecision_lt hfresh hk)).mpr (hnodecT k h1 hk)
    · have : k = trailLen T := by omega
      subst this; exact (not_congr (hpush.isDecision_top hfresh)).mpr hrv
  · exact hpush.pmode hfresh hrv (hlow.pmode ht hl hPm) (by rw [hlenT]; exact hv.hP)
  · obtain ⟨h1, h2⟩ := hv.rel
    refine ⟨by rw [hM2, hml, h1], ?_⟩
    rcases h2 with ⟨h3, h4, h5, h6⟩ | h3
    · refine Or.inl ⟨by rw [hN2, hnl, h3], h4, by rw [hlen2, hlenT]; omega, fun k hk => ?_⟩
      rw [hpush.trailAt_lt hfresh (by rw [hlenT]; omega), hlow.trailAt ht hl (by omega)]; exact h6 k hk
    · exact Or.inr (by rw [hN2, hnl]; exact h3)
  · rw [hwx, linksAfter_eq hlistT hpos, linksAfter_eq hv.list (fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (hlinks lit _ ((hv.mem _).mp (by simp))).1
      · exact hpos q hq)]
    simp

end MicrosatLean.Faithful.Verification
