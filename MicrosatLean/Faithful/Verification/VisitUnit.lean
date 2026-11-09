import MicrosatLean.Faithful.Verification.Visit
import MicrosatLean.Faithful.Verification.LowFrame

/-!
# A visited clause with no new literal to watch (C:150–151)

When the scan finds no non-false literal, `lit` is put at position 1 and the other watched
literal `y` at position 0 (C:142, C:150). The link just visited now watches position 1; the
record's other link still watches `y`.
-/

namespace MicrosatLean.Faithful.Verification

/-- The other watched literal of a record watched by `lit`. -/
def otherLit (r : Record) (lit : CInt) : CInt := if r.2[0]! = lit then r.2[1]! else r.2[0]!

/-- The record's literals after C:142 and C:150. -/
def unitLits (r : Record) (lit : CInt) : List CInt := otherLit r lit :: lit :: r.2.drop 2

/-- The visited record: its literals, `lit` among the first two, and its cells. -/
theorem Visit.slot {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt} {S : solver}
    {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) :
    ∃ a b tl, r.2 = a :: b :: tl ∧ (a = lit ∨ b = lit) ∧ a ≠ b ∧ ClauseAt S r.1 r.2 := by
  have hrec : ClauseAt S r.1 r.2 := by
    rcases List.mem_append.mp hv.hr with h' | h'
    · exact hv.core.database.inputs_tile.clauseAt h'
    · exact hv.core.database.lemmas_tile.clauseAt h'
  have hnd := hv.core.record_nodup hv.hr
  have h2 := hv.h2
  obtain ⟨a, b, tl, he⟩ : ∃ a b tl, r.2 = a :: b :: tl := by
    match h' : r.2 with
    | a :: b :: tl => exact ⟨a, b, tl, rfl⟩
    | [] => rw [h'] at h2; simp at h2
    | [_] => rw [h'] at h2; simp at h2
  refine ⟨a, b, tl, he, ?_, ?_, hrec⟩
  · have hx := hv.hx
    rw [he] at hx
    rcases hx with ⟨_, hx⟩ | ⟨_, hx⟩ <;> split at hx <;> simp at hx <;> simp [hx]
  · rw [he] at hnd; exact fun h' => (List.nodup_cons.mp hnd).1 (by rw [h']; simp)

/-- After C:142 and C:150 the record at `c` holds `unitLits`; no other cell changed. -/
theorem Visit.unit_cells {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S)) :
    ClauseAt (Ss.st (c + 1) lit) c (unitLits r lit) ∧ (unitLits r lit).Perm r.2 ∧
    (∀ q, 0 ≤ q → q ≠ c → q ≠ c + 1 → (Ss.st (c + 1) lit).ld q = S.ld q) ∧
    (∃ DB, Ss.st (c + 1) lit = { S with DB := DB }) := by
  obtain ⟨a, b, tl, hr2, hab, hne, hrec⟩ := hv.slot
  have hc0 : 0 ≤ c := by have := hv.core.database.record_ge hv.hr; have := hv.core.layout.nVars_pos
                         simp only [clausesAt] at *; omega
  have hSa : S.ld c = a := by have := hrec.1 0 (by rw [hr2]; simp); rw [← hc] at this; simpa [hr2] using this
  have hSb : S.ld (c + 1) = b := by have := hrec.1 1 (by rw [hr2]; simp); rw [← hc] at this; simpa [hr2] using this
  have hy : otherLit r lit = if a = lit then b else a := by simp [otherLit, hr2]
  -- the cells after C:142 and C:150
  have hcell : ∀ q, 0 ≤ q → (Ss.st (c + 1) lit).ld q =
      if q = c + 1 then lit else if q = c then otherLit r lit else S.ld q := by
    intro q hq
    rw [ld_st _ _ (by omega) hq, hy]
    split; rfl
    rcases hSs with ⟨h1, rfl⟩ | ⟨h1, rfl⟩
    · rw [hSa] at h1; rw [ld_st _ _ hc0 hq, if_pos h1, hSb]
    · rw [hSa] at h1; rw [if_neg h1]; split
      · rename_i he; rw [he, hSa]
      · rfl
  have hfields : ∃ DB, Ss.st (c + 1) lit = { S with DB := DB } := by
    obtain ⟨DB, hD⟩ := st_eq Ss (c + 1) lit
    refine ⟨DB, ?_⟩
    rcases hSs with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · obtain ⟨DB', hD'⟩ := st_eq S c (S.ld (c + 1)); rw [hD, hD']
    · exact hD
  refine ⟨⟨fun i hi => ?_, ?_⟩, ?_, fun q h0 h1 h2 => ?_, hfields⟩
  · have hlen : (unitLits r lit).length = r.2.length := by simp [unitLits, hr2]
    rw [hcell _ (by omega)]
    rcases i with _ | _ | i
    · rw [if_neg (by omega), if_pos (by omega)]; simp [unitLits]
    · rw [if_pos (by omega)]; simp [unitLits]
    · rw [if_neg (by omega), if_neg (by omega)]
      have := hrec.1 (i + 2) (by rw [← hlen]; exact hi)
      rw [← hc] at this
      rw [show c + ((i + 1 + 1 : Nat) : CInt) = c + ((i + 2 : Nat) : CInt) by omega, this]
      simp [unitLits, hr2]
  · have hlen : (unitLits r lit).length = r.2.length := by simp [unitLits, hr2]
    rw [hlen, hcell _ (by omega), if_neg (by rw [hr2]; simp; omega), if_neg (by rw [hr2]; simp; omega), hc]
    exact hrec.2
  · rw [show unitLits r lit = (if a = lit then b else a) :: lit :: tl by simp [unitLits, hy, hr2], hr2]
    rcases hab with h | h
    · rw [if_pos h, h]; exact List.Perm.swap _ _ _
    · rw [if_neg (fun h' => hne (h'.trans h.symm)), h]
  · rw [hcell q h0, if_neg h2, if_neg h1]

/-- What a record's own link cells watch. -/
theorem Database.watches_own {input : Input} {S : solver} {db : Records} (h : Database input S db)
    {r : Record} (hr : r ∈ db.all) (h2 : 2 ≤ r.2.length) {L : CInt} :
    (Watches db.all L (r.1 - 2) db.flip ↔ r.2[if db.flip r.1 then 1 else 0]? = some L) ∧
    (Watches db.all L (r.1 - 1) db.flip ↔ r.2[if db.flip r.1 then 0 else 1]? = some L) := by
  have key : ∀ s ∈ db.all, ∀ k, (k = s.1 - 2 ∨ k = s.1 - 1) → (k = r.1 - 2 ∨ k = r.1 - 1) → s = r := by
    intro s hs k hk1 hk2
    refine h.record_eq hs hr (Classical.byContradiction fun hne => ?_)
    rcases h.apart hs hr hne with h' | h' <;> omega
  constructor
  · constructor
    · rintro ⟨s, hs, _, hx⟩
      rcases hx with ⟨he, hx⟩ | ⟨he, hx⟩
      · have := key s hs _ (Or.inl he) (Or.inl rfl); subst this; exact hx
      · have := key s hs _ (Or.inr he) (Or.inl rfl); subst this; omega
    · intro hx; exact ⟨r, hr, h2, Or.inl ⟨rfl, hx⟩⟩
  · constructor
    · rintro ⟨s, hs, _, hx⟩
      rcases hx with ⟨he, hx⟩ | ⟨he, hx⟩
      · have := key s hs _ (Or.inl he) (Or.inr rfl); subst this; omega
      · have := key s hs _ (Or.inr he) (Or.inr rfl); subst this; exact hx
    · intro hx; exact ⟨r, hr, h2, Or.inr ⟨rfl, hx⟩⟩

/-- In the unit case the link just visited watches position 1 (`lit`) and the other link
position 0 (`y`): exactly the literals they watched before. -/
theorem Visit.unit_watches {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) (L link : CInt) :
    Watches (db.update c (unitLits r lit) (decide (S.ld w = c - 2))).all L link
      (db.update c (unitLits r lit) (decide (S.ld w = c - 2))).flip ↔ Watches db.all L link db.flip := by
  obtain ⟨a, b, tl, hr2, hab, hne, -⟩ := hv.slot
  have hd := hv.core.database
  have hown := hd.watches_own hv.hr hv.h2 (L := L)
  rw [hd.watches_update hv.hr hc.symm]
  have hlen : 2 ≤ (unitLits r lit).length := by simp [unitLits]
  have hx := hv.hx
  have hy : otherLit r lit = if a = lit then b else a := by simp [otherLit, hr2]
  rw [← hc] at hown hx
  constructor
  · rintro (⟨hw, -⟩ | ⟨-, ⟨rfl, hl⟩ | ⟨rfl, hl⟩⟩)
    · exact hw
    · refine hown.1.mpr ?_
      rw [hr2] at hx ⊢
      simp only [unitLits, hy] at hl
      cases hf : db.flip c <;> simp only [hf] at hx ⊢ <;>
        by_cases hxc : S.ld w = c - 2 <;> simp [hxc] at hl hx <;> rcases hab with rfl | rfl <;> simp_all <;> omega
    · refine hown.2.mpr ?_
      rw [hr2] at hx ⊢
      simp only [unitLits, hy] at hl
      cases hf : db.flip c <;> simp only [hf] at hx ⊢ <;>
        by_cases hxc : S.ld w = c - 2 <;> simp [hxc] at hl hx <;> rcases hab with rfl | rfl <;> simp_all <;> omega
  · intro hw
    by_cases h1 : link = c - 2
    · subst h1
      have hl := hown.1.mp hw
      refine Or.inr ⟨hlen, Or.inl ⟨rfl, ?_⟩⟩
      rw [hr2] at hx hl
      simp only [unitLits, hy]
      cases hf : db.flip c <;> simp only [hf] at hx hl <;>
        by_cases hxc : S.ld w = c - 2 <;> simp [hxc] at hl hx ⊢ <;> rcases hab with rfl | rfl <;> simp_all <;> omega
    · by_cases h2 : link = c - 1
      · subst h2
        have hl := hown.2.mp hw
        refine Or.inr ⟨hlen, Or.inr ⟨rfl, ?_⟩⟩
        rw [hr2] at hx hl
        simp only [unitLits, hy]
        cases hf : db.flip c <;> simp only [hf] at hx hl <;>
          by_cases hxc : S.ld w = c - 2 <;> simp [hxc] at hl hx ⊢ <;> rcases hab with rfl | rfl <;> simp_all <;> omega
      · exact Or.inl ⟨hw, h1, h2⟩

/-- The state after C:142 and C:150 satisfies `Core` with the visited record updated; the
trail and every cell outside the record's first two literals are unchanged. -/
theorem Visit.unit_core {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S)) :
    Core input (Ss.st (c + 1) lit) (db.update c (unitLits r lit) (decide (S.ld w = c - 2))) vs ∧
    LowSame S (Ss.st (c + 1) lit) ∧ (Ss.st (c + 1) lit).head = S.head ∧
    (Ss.st (c + 1) lit).nLemmas = S.nLemmas ∧ (Ss.st (c + 1) lit).maxLemmas = S.maxLemmas := by
  obtain ⟨hcl, hperm, hcells, DB, hT⟩ := hv.unit_cells hc hSs
  obtain ⟨a, b, tl, hr2, hab, hne, hrec⟩ := hv.slot
  generalize hTd : Ss.st (c + 1) lit = T at hcl hcells hT ⊢
  have core := hv.core; have hd := core.database; have hl := core.layout; have ht := core.trail
  have hn := hl.num; have hn1 := hl.nVars_pos
  have hcb := hd.record_ge hv.hr; rw [← hc] at hcb; simp only [clausesAt] at hcb
  have hshape : SameShape S T := by rw [hT]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have hlow : LowSame S T := ⟨hshape, by rw [hT], by rw [hT], by rw [hT], fun q h0 h1 => hcells q h0 (by omega) (by omega)⟩
  -- cells of other records and of watch lists are unchanged
  have hother : ∀ s ∈ db.all, s.1 ≠ c → ∀ q, RecordCell s q → T.ld q = S.ld q := fun s hs hsc q hq => by
    have := hd.apart hs hv.hr (by rw [← hc]; exact hsc); have := hd.record_ge hs
    simp only [RecordCell] at hq; rw [← hc] at *; simp only [clausesAt] at *
    exact hcells q (by omega) (by omega) (by omega)
  have hlinkcell : ∀ L link, Watches db.all L link db.flip → T.ld link = S.ld link := fun L link hw => by
    obtain ⟨s, hs, _, hx⟩ := hw
    have := hd.record_ge hs; simp only [clausesAt] at this
    by_cases hsr : s.1 = c
    · rcases hx with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hcells _ (by omega) (by omega) (by omega)
    · have := hd.apart hs hv.hr (by rw [← hc]; exact hsr); rw [← hc] at this
      have h2 := hv.h2
      rcases hx with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hcells _ (by omega) (by omega) (by omega)
  have hwe := hv.unit_watches hc
  -- a reason record never has `lit` first: so its literals do not move
  have hreason_same : ∀ i < trailLen S, (∃ s ∈ db.all, s.1 = c ∧ s.2[0]? = some (- trailAt S i)) →
      unitLits r lit = r.2 := by
    rintro i hi ⟨s, hs, hsc, h0⟩
    have hsr := hd.record_eq hs hv.hr (by rw [hsc, hc])
    subst hsr
    rw [hr2] at h0; simp at h0
    have hal : a ≠ lit := fun he => by
      have hP := hv.hP; have hlit := hv.hlit
      have hd2 := ht.distinct i hi _ hP (by rw [hlit, ← he, h0, abs_neg'])
      subst hd2; rw [hlit] at h0
      have := (inRange_iff.mp (ht.lit _ hP)).1; rw [hlit] at this; omega
    have hbl : b = lit := by rcases hab with h' | h'; exact absurd h' hal; exact h'
    simp [unitLits, otherLit, hr2, hal, hbl]
  refine ⟨⟨core.valid, by rw [hshape.nVars]; exact core.nVars, by rw [hT]; exact core.memory,
    by rw [hT]; exact core.maxLemmas, hl.frame hshape (hcells _ (by simp only [clausesAt]; omega)
      (by simp only [clausesAt]; omega) (by simp only [clausesAt]; omega)),
    hlow.trail ht hl, hlow.root ht hl core.root,
    hd.update _ hv.hr hc.symm hperm hcl ⟨hshape.nVars, by rw [hT], by rw [hT], by rw [hT]⟩ hother,
    ?_, ?_, ?_, hlow.order ht hl core.order (by rw [hT])⟩, hlow, by rw [hT], by rw [hT], by rw [hT]⟩
  · -- watch lists: the same physical lists, the same watchers
    intro L hL
    rw [hshape.nVars] at hL
    obtain ⟨links, hlf, hnd, hmem⟩ := core.watches L hL
    have hr' := inRange_iff.mp hL
    refine ⟨links, ?_, hnd, fun link => by rw [hmem, hwe]⟩
    rw [hshape.first]
    exact hlf.frame fun q hq => by
      rcases hq with rfl | hq
      · exact hcells _ (by omega) (by omega) (by omega)
      · exact hlinkcell L q ((hmem q).mp hq)
  · -- reasons: a reason record keeps its literals
    intro i hi hfi hrs
    rw [hlow.trailLen ht hl] at hi; rw [hlow.forcedPos ht hl] at hfi
    have hti := inRange_iff.mp (ht.lit i hi)
    rw [hlow.trailAt ht hl hi, hlow.reasonOf ht hl (by omega) (by omega)] at hrs ⊢
    obtain ⟨s, hs, e1, e2, e3, e4⟩ := core.reasons i hi hfi hrs
    refine ⟨if s.1 = c then (c, unitLits r lit) else s, by rw [Records.update_all]; exact List.mem_map_of_mem hs,
      ?_, ?_, ?_, ?_⟩
    · split
      · rename_i he; rw [e1, he]
      · exact e1
    all_goals split
    all_goals first
      | (rename_i he
         rw [hreason_same i hi ⟨s, hs, he, e2⟩, show r = s from (hd.record_eq hs hv.hr (by rw [he, hc])).symm]
         first
          | exact e2
          | (intro lit' hl'; obtain ⟨j, hj, hfa⟩ := e3 lit' hl'; exact ⟨j, hj, (hlow.falseAt ht hl).mpr hfa⟩)
          | (intro hnr
             obtain ⟨lit', hl', j, hj, hfa, hsl⟩ := e4 fun h' => hnr ((hlow.rootLevel ht hl hi).mpr h')
             exact ⟨lit', hl', j, hj, (hlow.falseAt ht hl).mpr hfa, (hlow.sameLevel ht hl hi).mpr hsl⟩))
      | exact e2
      | (intro lit' hl'; obtain ⟨j, hj, hfa⟩ := e3 lit' hl'; exact ⟨j, hj, (hlow.falseAt ht hl).mpr hfa⟩)
      | (intro hnr
         obtain ⟨lit', hl', j, hj, hfa, hsl⟩ := e4 fun h' => hnr ((hlow.rootLevel ht hl hi).mpr h')
         exact ⟨lit', hl', j, hj, (hlow.falseAt ht hl).mpr hfa, (hlow.sameLevel ht hl hi).mpr hsl⟩)
  · -- units: the visited record has two or more literals
    intro s hs h1
    rw [Records.update_all] at hs
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
    by_cases hsc : s0.1 = c
    · simp only [hsc, if_true, unitLits] at h1; simp at h1
    · simp only [hsc, if_false] at h1 ⊢
      obtain ⟨i, hi, hroot, he⟩ := core.units s0 hs0 h1
      exact ⟨i, by rw [hlow.trailLen ht hl]; exact hi, (hlow.rootLevel ht hl hi).mpr hroot,
        by rw [hlow.trailAt ht hl hi]; exact he⟩

/-- `propagate`'s mode carries over unchanged trails. -/
theorem LowSame.pmode {S T : solver} (h : LowSame S T) (ht : Trail S) (hl : Layout S) {f : CInt} {P : Nat}
    (hp : PMode S f P) : PMode T f P := by
  rw [PMode, h.trailLen ht hl, h.forcedPos ht hl]
  obtain ⟨h1, h2⟩ := hp
  refine ⟨?_, fun k hk1 hk2 => (not_congr (h.isDecision ht hl hk2)).mpr (h2 k hk1 hk2)⟩
  rcases h1 with ⟨hf, hr⟩ | ⟨hf, hb, hd⟩
  · exact Or.inl ⟨hf, fun i hi => (h.rootLevel ht hl hi).mpr (hr i hi)⟩
  · refine Or.inr ⟨hf, fun i hi hr => hb i hi ((h.rootLevel ht hl hi).mp hr), fun hP => ?_⟩
    obtain ⟨D, h1, h2, h3⟩ := hd hP
    exact ⟨D, h1, h2, (h.isDecision ht hl (by omega)).mpr h3⟩

/-- The relation to the start carries over unchanged trails. -/
theorem LowSame.rel {S T : solver} (h : LowSame S T) (ht : Trail S) (hl : Layout S) {S0 : solver}
    {vs0 vs : List CInt} (hr : Rel S0 vs0 S vs) (hm : T.maxLemmas = S.maxLemmas) (hn : T.nLemmas = S.nLemmas) :
    Rel S0 vs0 T vs := by
  obtain ⟨h1, h2⟩ := hr
  refine ⟨by rw [hm, h1], ?_⟩
  rcases h2 with ⟨h3, h4, h5, h6⟩ | h3
  · exact Or.inl ⟨by rw [hn, h3], h4, by rw [h.trailLen ht hl]; exact h5, fun i hi => by
      rw [h.trailAt ht hl (by omega)]; exact h6 i hi⟩
  · exact Or.inr (by rw [hn]; exact h3)

/-- A literal with a nonzero `false` flag is on the trail. -/
theorem Trail.onTrail_of_flag {S : solver} (ht : Trail S) {lit : CInt} (hl : InRange S.nVars lit)
    (hf : flag S lit ≠ 0) : ∃ i < trailLen S, trailAt S i = lit :=
  Classical.byContradiction fun hn => hf (ht.flag_off lit hl fun i hi he => hn ⟨i, hi, he⟩)

/-- In the unit state with `y` true (C:151, or after assigning it), the visited record meets
the watched-literal invariant: `lit` at position 1 has its true partner `y`. -/
theorem Visit.unit_watched {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {T : solver}
    (hT : processedPos T = P + 1)
    (hyt : ∃ q, FalseAt T (-(otherLit r lit)) q ∧ SameOrLowerLevel T P q)
    (hold : ∀ s ∈ db.all, s.1 ≠ c → 2 ≤ s.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
      ∀ p < P + 1, FalseAt T s.2[w]! p → (p = P → s.1 - 2 ∉ rest ∧ s.1 - 1 ∉ rest) →
        ∃ q, FalseAt T (- s.2[o]!) q ∧ SameOrLowerLevel T p q)
    (hnotfalse : ∀ p < P + 1, ¬ FalseAt T (otherLit r lit) p)
    (hlitonly : ∀ p < P + 1, FalseAt T lit p → p = P) :
    WatchedExcept T (db.update c (unitLits r lit) (decide (S.ld w = c - 2))) P rest := by
  intro s hs h2 w0 o hwo p hp hfa hex
  rw [hT] at hp
  rw [Records.update_all] at hs
  obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
  by_cases hsc : s0.1 = c
  · simp only [hsc, if_true] at h2 hfa ⊢
    rcases hwo with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact absurd hfa (hnotfalse p hp)
    · have hpP := hlitonly p hp hfa
      subst hpP
      obtain ⟨q, hq, hsl⟩ := hyt
      exact ⟨q, hq, hsl⟩
  · simp only [hsc, if_false] at h2 hfa hex ⊢
    exact hold s0 hs0 hsc h2 w0 o hwo p hp hfa hex

/-- The other records keep the watched-literal invariant in the unit state. -/
theorem Visit.unit_hold {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {T : solver}
    (hfa : ∀ {l : CInt} {j : Nat}, FalseAt T l j → FalseAt S l j ∨ (j = trailLen S))
    (hfa' : ∀ {l : CInt} {j : Nat}, FalseAt S l j → FalseAt T l j)
    (hsl : ∀ p q, q < trailLen S → SameOrLowerLevel S p q → SameOrLowerLevel T p q) :
    ∀ s ∈ db.all, s.1 ≠ c → 2 ≤ s.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
      ∀ p < P + 1, FalseAt T s.2[w]! p → (p = P → s.1 - 2 ∉ rest ∧ s.1 - 1 ∉ rest) →
        ∃ q, FalseAt T (- s.2[o]!) q ∧ SameOrLowerLevel T p q := by
  intro s hs hsc h2 w0 o hwo p hp hfa0 hex
  have hpt : p < trailLen S := by have := hv.hP; omega
  have hfaS : FalseAt S s.2[w0]! p := by
    rcases hfa hfa0 with h' | h'
    · exact h'
    · omega
  have hx := hv.hx
  have hap := hv.core.database.apart hs hv.hr (by rw [← hc]; exact hsc)
  have hrl := hv.h2
  obtain ⟨q, hq, hsl'⟩ := hv.watched s hs h2 w0 o hwo p (by rw [hv.hpp]; exact hp) hfaS fun hpP => by
    obtain ⟨n0, n1⟩ := hex hpP
    refine ⟨?_, ?_⟩ <;> simp only [List.mem_cons, not_or] <;> refine ⟨?_, by assumption⟩ <;>
      rcases hx with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;> omega
  exact ⟨q, hfa' hq, hsl p q hq.1 hsl'⟩

/-- Link cells and the list head are not literal cells of the visited record. -/
theorem Visit.cells_ne {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) :
    (∀ L link, Watches db.all L link db.flip → 0 ≤ link ∧ link ≠ c ∧ link ≠ c + 1) ∧
    (0 ≤ S.first + lit ∧ S.first + lit ≠ c ∧ S.first + lit ≠ c + 1) := by
  have hd := hv.core.database; have hl := hv.core.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hcb := hd.record_ge hv.hr; rw [← hc] at hcb; simp only [clausesAt] at hcb
  have h2 := hv.h2
  have hlit := inRange_iff.mp (hv.core.trail.lit _ hv.hP); rw [hv.hlit] at hlit
  refine ⟨fun L link hw => ?_, by omega, by omega, by omega⟩
  obtain ⟨s, hs, _, hx⟩ := hw
  have := hd.record_ge hs; simp only [clausesAt] at this
  by_cases hsr : s.1 = c
  · rcases hx with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  · have := hd.apart hs hv.hr (by rw [← hc]; exact hsr); rw [← hc] at this
    rcases hx with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega

/-- C:150–151 when the other watched literal is true: continue with the next link. -/
theorem Visit.true_step {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S))
    (hy : (Ss.st (c + 1) lit).ld ((Ss.st (c + 1) lit).false + -(Ss.st (c + 1) lit).ld c) ≠ 0) :
    WInv input S0 vs0 P lit (Ss.st (c + 1) lit) f ((Ss.st (c + 1) lit).ld w) ∧
    (Ss.st (c + 1) lit).nLemmas = S.nLemmas ∧
    (linksAfter (Ss.st (c + 1) lit) ((Ss.st (c + 1) lit).ld w)).length < (linksAfter S w).length := by
  obtain ⟨core', hlow, hhead, hnl, hml⟩ := hv.unit_core hc hSs
  obtain ⟨hcl, hperm, hcells, DB, hT⟩ := hv.unit_cells hc hSs
  obtain ⟨hlinks, hhd⟩ := hv.cells_ne hc
  generalize hTd : Ss.st (c + 1) lit = T at *
  have ht := hv.core.trail; have hl := hv.core.layout
  have hyc : T.ld c = otherLit r lit := by
    have := hcl.1 0 (by simp [unitLits]); simpa [unitLits] using this
  have hymem : otherLit r lit ∈ r.2 := by
    obtain ⟨a, b, tl, hr2, _, _, _⟩ := hv.slot
    simp only [otherLit, hr2]; split <;> simp
  have hyr := inRange_iff.mp (hv.core.record_lit hv.hr hymem)
  have hlitr := inRange_iff.mp (ht.lit _ hv.hP); rw [hv.hlit] at hlitr
  -- `y` is true: its negation is on the trail
  have hy' : flag S (-(otherLit r lit)) ≠ 0 := by
    rw [← hlow.flag ht hl (by omega) (by omega)]; simp only [flag, hlow.shape.false]
    rw [← hyc, ← hlow.shape.false]; exact hy
  obtain ⟨q, hq, hqe⟩ := ht.onTrail_of_flag (inRange_iff.mpr ⟨by omega, by omega, by omega⟩) hy'
  have hx : S.ld w ∈ visited ++ S.ld w :: rest := by simp
  have hw' := hv.mem (S.ld w)
  have hwx : T.ld w = S.ld w := by
    have hwin : w ∈ (S.first + lit) :: visited := by rw [hv.path.end_eq]; exact List.getLast_mem _
    rcases List.mem_cons.mp hwin with he | hm
    · rw [he]; exact hcells _ hhd.1 hhd.2.1 hhd.2.2
    · obtain ⟨h0, h1, h2⟩ := hlinks lit w ((hv.mem w).mp (by simp [hm])); exact hcells _ h0 h1 h2
  have hrest : ∀ q ∈ rest, T.ld q = S.ld q := fun q hq => by
    obtain ⟨h0, h1, h2⟩ := hlinks lit q ((hv.mem q).mp (by simp [hq])); exact hcells _ h0 h1 h2
  have hlistT : ListFrom T (S.ld w) rest := hv.list.2.frame fun q hq => by
    rcases hq with rfl | hq
    · obtain ⟨h0, h1, h2⟩ := hlinks lit _ ((hv.mem _).mp hx); exact hcells _ h0 h1 h2
    · exact hrest q hq
  have hpos : ∀ q ∈ rest, 0 ≤ q := fun q hq => (hlinks lit q ((hv.mem q).mp (by simp [hq]))).1
  refine ⟨⟨_, vs, visited ++ [S.ld w], rest, core', by rw [hlow.processedPos ht hl, hv.hpp],
    by rw [hlow.trailLen ht hl]; exact hv.hP, by rw [hlow.trailAt ht hl hv.hP]; exact hv.hlit, ?_,
    by rw [hwx]; exact hlistT, by rw [hlow.shape.first]; simpa using hv.nodup, fun link => ?_, ?_,
    hlow.pmode ht hl hv.pmode, hlow.rel ht hl hv.rel hml hnl⟩, hnl, ?_⟩
  · rw [hlow.shape.first, hwx]
    refine (hv.path.frame (fun q hq hqw => ?_) ?_).snoc hwx
    · rcases hq with rfl | hq
      · exact hcells _ hhd.1 hhd.2.1 hhd.2.2
      · obtain ⟨h0, h1, h2⟩ := hlinks lit q ((hv.mem q).mp (by simp [hq])); exact hcells _ h0 h1 h2
    · have := hv.nodup; exact this.sublist (List.Sublist.cons₂ _ (List.sublist_append_left _ _))
  · rw [hv.unit_watches hc, ← hv.mem, List.append_assoc, List.singleton_append]
  · refine hv.unit_watched hc (by rw [hlow.processedPos ht hl, hv.hpp])
      ⟨q, (hlow.falseAt ht hl).mpr ⟨hq, hqe⟩, (hlow.sameLevel ht hl hq).mpr fun k hk1 hk2 =>
        hv.pmode.2 k hk1 (by omega)⟩
      (hv.unit_hold hc (fun h' => Or.inl ((hlow.falseAt ht hl).mp h')) (fun h' => (hlow.falseAt ht hl).mpr h')
        fun p q hq h' => (hlow.sameLevel ht hl hq).mpr h')
      (fun p _ hfa => by
        rw [hlow.falseAt ht hl] at hfa
        have := ht.distinct p hfa.1 q hq (by rw [hfa.2, hqe, abs_neg'])
        subst this; rw [hfa.2] at hqe; omega)
      (fun p hp hfa => by
        rw [hlow.falseAt ht hl] at hfa
        exact ht.distinct p hfa.1 P hv.hP (by rw [hfa.2, hv.hlit]))
  · rw [hwx, linksAfter_eq hlistT hpos, linksAfter_eq hv.list (fun q hq => by
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (hlinks lit _ ((hv.mem _).mp hx)).1
      · exact hpos q hq)]
    simp

/-- The `false` flags are not record cells: the unit state reads them as `S` does. -/
theorem Visit.unit_flag {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S)) :
    (Ss.st (c + 1) lit).ld c = otherLit r lit ∧
    ∀ l, -S.nVars ≤ l → l ≤ S.nVars → (Ss.st (c + 1) lit).ld ((Ss.st (c + 1) lit).false + l) = flag S l := by
  obtain ⟨hcl, -, hcells, DB, hT⟩ := hv.unit_cells hc hSs
  have hn := hv.core.layout.num; have hn1 := hv.core.layout.nVars_pos
  have hcb := hv.core.database.record_ge hv.hr; rw [← hc] at hcb; simp only [clausesAt] at hcb
  refine ⟨by have := hcl.1 0 (by simp [unitLits]); simpa [unitLits] using this, fun l h1 h2 => ?_⟩
  have hf : (Ss.st (c + 1) lit).false = S.false := by rw [hT]
  rw [hf, hcells _ (by omega) (by omega) (by omega)]; rfl

/-- When the scan ends without a new literal (C:152), every literal of the visited record
from position 2 on is false; with `y` false too, the whole clause is false (C:153). -/
theorem Visit.scan_all_false {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S))
    {L i : CInt} (hL : Ss.ld (c + L) = 0) (hnz : ∀ t, 2 ≤ t → t < L → Ss.ld (c + t) ≠ 0)
    (hi2 : 2 ≤ i) (hiL : i ≤ L) (hfl : ∀ t, 2 ≤ t → t < i → flag Ss (Ss.ld (c + t)) ≠ 0)
    (hend : Ss.ld (c + i) = 0) (hy : flag S (otherLit r lit) ≠ 0) :
    ∀ l ∈ r.2, ∃ j < trailLen S, trailAt S j = l := by
  obtain ⟨a, b, tl, hr2, hab, hne, hrec⟩ := hv.slot
  have ht := hv.core.trail; have hl := hv.core.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hcb := hv.core.database.record_ge hv.hr; rw [← hc] at hcb; simp only [clausesAt] at hcb
  have hlen : (r.2.length : CInt) = (tl.length : CInt) + 2 := by rw [hr2]; simp; omega
  -- the swap at C:142 changes only cell `c`
  have hSc : ∀ q, 0 ≤ q → q ≠ c → Ss.ld q = S.ld q := fun q hq hqc => by
    rcases hSs with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rw [ld_st _ _ (by omega) hq, if_neg hqc]
    · rfl
  have hcell : ∀ t : Nat, 2 ≤ t → t < r.2.length → Ss.ld (c + t) = r.2[t]! := fun t h1 h2 => by
    rw [hSc _ (by omega) (by omega)]; have := hrec.1 t h2; rw [← hc] at this
    rw [this, getElem!_pos r.2 t h2]
  have hterm : Ss.ld (c + r.2.length) = 0 := by rw [hSc _ (by omega) (by omega), hc]; exact hrec.2
  -- the scan reached the terminator: `i` is the record's length
  have hiE : i = r.2.length := by
    refine Classical.byContradiction fun hne' => ?_
    rcases Int.lt_or_gt_of_ne hne' with hlt | hgt
    · -- a literal cell holds 0: impossible
      have := hcell i.toNat (by omega) (by omega)
      rw [show (i.toNat : CInt) = i by omega, hend] at this
      have hm : r.2[i.toNat]! ∈ r.2 := by rw [getElem!_pos r.2 _ (by omega)]; exact List.getElem_mem _
      exact (inRange_iff.mp (hv.core.record_lit hv.hr hm)).1 this.symm
    · exact hnz _ (by omega) (by omega) hterm
  have hfalse : ∀ l, InRange S.nVars l → flag S l ≠ 0 → ∃ j < trailLen S, trailAt S j = l :=
    fun l hl' hf => ht.onTrail_of_flag hl' hf
  intro l hlm
  have hlr := hv.core.record_lit hv.hr hlm
  rw [hr2] at hlm
  rcases List.mem_cons.mp hlm with rfl | hlm
  · rcases hab with rfl | rfl
    · exact ⟨P, hv.hP, hv.hlit⟩
    · refine hfalse _ hlr ?_
      have : otherLit r b = l := by simp [otherLit, hr2, hne]
      rw [← this]; exact hy
  · rcases List.mem_cons.mp hlm with rfl | hlm
    · rcases hab with rfl | rfl
      · refine hfalse _ hlr ?_
        have : otherLit r a = l := by simp [otherLit, hr2]
        rw [← this]; exact hy
      · exact ⟨P, hv.hP, hv.hlit⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hlm
      refine hfalse _ hlr ?_
      have := hfl (j + 2) (by omega) (by rw [hiE, hlen]; omega)
      have hc' := hcell (j + 2) (by omega) (by rw [hr2]; simp; omega)
      rw [show ((j + 2 : Nat) : CInt) = (j : CInt) + 2 by omega] at hc'
      rw [hc'] at this
      have hidx : r.2[j + 2]! = tl[j] := by rw [hr2]; simp [getElem!_pos, hj]
      rw [hidx] at this
      have hlr' := inRange_iff.mp hlr
      simp only [flag] at this ⊢
      rcases hSs with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · simp only [st_false] at this
        rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)] at this
        simpa using this
      · simpa using this

/-- When the scan ends without a new literal (C:152), every literal of the visited record
other than `y` is false. -/
theorem Visit.scan_rest_false {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c : CInt} (hc : c = r.1) {Ss : solver}
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S))
    {L i : CInt} (hL : Ss.ld (c + L) = 0) (hnz : ∀ t, 2 ≤ t → t < L → Ss.ld (c + t) ≠ 0)
    (hi2 : 2 ≤ i) (hiL : i ≤ L) (hfl : ∀ t, 2 ≤ t → t < i → flag Ss (Ss.ld (c + t)) ≠ 0)
    (hend : Ss.ld (c + i) = 0) :
    ∀ l ∈ r.2, l ≠ otherLit r lit → ∃ j < trailLen S, trailAt S j = l := by
  obtain ⟨a, b, tl, hr2, hab, hne, hrec⟩ := hv.slot
  have ht := hv.core.trail; have hl := hv.core.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hcb := hv.core.database.record_ge hv.hr; rw [← hc] at hcb; simp only [clausesAt] at hcb
  have hlen : (r.2.length : CInt) = (tl.length : CInt) + 2 := by rw [hr2]; simp; omega
  -- the swap at C:142 changes only cell `c`
  have hSc : ∀ q, 0 ≤ q → q ≠ c → Ss.ld q = S.ld q := fun q hq hqc => by
    rcases hSs with ⟨_, rfl⟩ | ⟨_, rfl⟩
    · rw [ld_st _ _ (by omega) hq, if_neg hqc]
    · rfl
  have hcell : ∀ t : Nat, 2 ≤ t → t < r.2.length → Ss.ld (c + t) = r.2[t]! := fun t h1 h2 => by
    rw [hSc _ (by omega) (by omega)]; have := hrec.1 t h2; rw [← hc] at this
    rw [this, getElem!_pos r.2 t h2]
  have hterm : Ss.ld (c + r.2.length) = 0 := by rw [hSc _ (by omega) (by omega), hc]; exact hrec.2
  -- the scan reached the terminator: `i` is the record's length
  have hiE : i = r.2.length := by
    refine Classical.byContradiction fun hne' => ?_
    rcases Int.lt_or_gt_of_ne hne' with hlt | hgt
    · -- a literal cell holds 0: impossible
      have := hcell i.toNat (by omega) (by omega)
      rw [show (i.toNat : CInt) = i by omega, hend] at this
      have hm : r.2[i.toNat]! ∈ r.2 := by rw [getElem!_pos r.2 _ (by omega)]; exact List.getElem_mem _
      exact (inRange_iff.mp (hv.core.record_lit hv.hr hm)).1 this.symm
    · exact hnz _ (by omega) (by omega) hterm
  have hfalse : ∀ l, InRange S.nVars l → flag S l ≠ 0 → ∃ j < trailLen S, trailAt S j = l :=
    fun l hl' hf => ht.onTrail_of_flag hl' hf
  intro l hlm hly
  have hlr := hv.core.record_lit hv.hr hlm
  rw [hr2] at hlm
  rcases List.mem_cons.mp hlm with rfl | hlm
  · rcases hab with rfl | rfl
    · exact ⟨P, hv.hP, hv.hlit⟩
    · exact absurd (by simp [otherLit, hr2, hne]) hly
  · rcases List.mem_cons.mp hlm with rfl | hlm
    · rcases hab with rfl | rfl
      · exact absurd (by simp [otherLit, hr2]) hly
      · exact ⟨P, hv.hP, hv.hlit⟩
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hlm
      refine hfalse _ hlr ?_
      have := hfl (j + 2) (by omega) (by rw [hiE, hlen]; omega)
      have hc' := hcell (j + 2) (by omega) (by rw [hr2]; simp; omega)
      rw [show ((j + 2 : Nat) : CInt) = (j : CInt) + 2 by omega] at hc'
      rw [hc'] at this
      have hidx : r.2[j + 2]! = tl[j] := by rw [hr2]; simp [getElem!_pos, hj]
      rw [hidx] at this
      have hlr' := inRange_iff.mp hlr
      simp only [flag] at this ⊢
      rcases hSs with ⟨_, rfl⟩ | ⟨_, rfl⟩
      · simp only [st_false] at this
        rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)] at this
        simpa using this
      · simpa using this

/-- A clause entailed by the input whose other literals are all false in every model
entails its remaining literal (a root unit, C:154 with `forced`). -/
theorem Input.entails_unit {input : Input} {cl : List CInt} {y : CInt} (h : input.Entails cl)
    (hnz : ∀ l ∈ cl, l ≠ 0) (hother : ∀ l ∈ cl, l ≠ y → input.Entails [-l]) : input.Entails [y] := by
  intro a ha
  obtain ⟨l, hl, ht⟩ := h a ha
  by_cases hy : l = y
  · subst hy; exact ⟨l, by simp, ht⟩
  · have hl0 := hnz l hl
    obtain ⟨l', hl', ht'⟩ := hother l hl hy a ha
    simp only [List.mem_singleton] at hl'; subst hl'
    unfold LitTrue at ht ht'
    rw [Int.natAbs_neg, ht] at ht'
    exfalso; simp at ht'; omega

/-- Every record of the database is entailed by the input. -/
theorem Core.record_entailed {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) {r : Record} (hr : r ∈ db.all) : input.Entails r.2 := by
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, hi, hp⟩ := h.database.input_perm hr
    exact fun a ha => (clauseSat_perm hp).mpr (ha _ (Array.getElem_mem hi))
  · exact h.database.lemma_entailed r hr

/-- Trail literals have a nonzero `false` flag. -/
theorem Trail.flag_ne_zero {S : solver} (ht : Trail S) {i : Nat} (hi : i < trailLen S) :
    flag S (trailAt S i) ≠ 0 := by
  by_cases hr : RootLevel S i
  · rw [ht.flag_root i hi hr]; decide
  · rw [ht.flag_level i hi hr]; decide

end MicrosatLean.Faithful.Verification
