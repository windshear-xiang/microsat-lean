import MicrosatLean.Fast.Verification.Inv

/-!
# `propagate` of the fast port (C:132–158)

The fast `propLoop` merges `propagate`'s two loops (and the conflict analysis) into one
tail-recursive function. Its proof re-proves the faithful `propagate_main` by induction:
on the outer measure `outMeasure` (`propLoop_outer`, with the watch cursor at the list's
end), and inside it on the number of links left (`propLoop_inner`, with the cursor in the
watch list). Each visited link calls the faithful per-visit lemmas (`Visit.found_step`,
`true_step`, `assign_step`, `scan_all_false`) on the abstracted states. The conflict
analysis is the statement `ConflictSpec` (proved as `conflict_fast` in `Analyze.lean`).
-/

namespace MicrosatLean.Fast.Verification

set_option linter.deprecated false

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-! ### Basics -/

/-- The fast state that `propLoop`'s arguments stand for. -/
abbrev pst (s : St) (db : Array Cell) (a p : Cell) : St := { s with db, assigned := a, processed := p }

/-- `propagate`'s `forced` flag (C:134) as a faithful value. -/
def fl (b : Bool) : Int := if b then 1 else 0

theorem fl_ne_zero (b : Bool) : fl b ≠ 0 ↔ b = true := by cases b <;> simp [fl]

/-- `PMode` reads its flag only through `f ≠ 0`. -/
theorem PMode.flag {S : solver} {f g : Int} {P : Nat} (h : PMode S f P) (hfg : f ≠ 0 ↔ g ≠ 0) :
    PMode S g P := by
  obtain ⟨h1 | h1, h2⟩ := h
  · exact ⟨Or.inl ⟨hfg.mp h1.1, h1.2⟩, h2⟩
  · exact ⟨Or.inr ⟨Classical.byContradiction fun hg => hfg.mpr hg h1.1, h1.2⟩, h2⟩

theorem OutInv.flag {input : Input} {S0 : solver} {vs0 : List Int} {S : solver} {f g : Int}
    (h : OutInv input S0 vs0 S f) (hfg : f ≠ 0 ↔ g ≠ 0) : OutInv input S0 vs0 S g := by
  obtain ⟨db, vs, core, wt, pm, rel⟩ := h
  exact ⟨db, vs, core, wt, PMode.flag pm hfg, rel⟩

/-- The end of a path is its start or one of its links. -/
theorem Path.mem_end {S : solver} {a b : Int} {xs : List Int} (h : Path S a xs b) : b = a ∨ b ∈ xs := by
  induction xs generalizing a with
  | nil => exact Or.inl h.symm
  | cons x xs ih =>
    obtain ⟨-, h2⟩ := h
    rcases ih h2 with h3 | h3
    · exact Or.inr (by simp [h3])
    · exact Or.inr (by simp [h3])

/-- The cursor of the watch loop is the list head or a link cell, and neither is a cell of
the visited record (literals and terminator). -/
theorem Visit.cursor_ne {input : Input} {S0 : solver} {vs0 : List Int} {P : Nat} {lit : Int}
    {S : solver} {f w : Int} {db : Records} {vs : List Int} {visited rest : List Int} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) :
    0 ≤ w ∧ w < S.mem_used ∧ ∀ t : Int, 0 ≤ t → t ≤ r.2.length → w ≠ r.1 + t := by
  have hd := hv.core.database; have hl := hv.core.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hcb := hd.record_ge hv.hr; simp only [clausesAt] at hcb
  have hlit := inRange_iff.mp (hv.core.trail.lit _ hv.hP); rw [hv.hlit] at hlit
  rcases Path.mem_end hv.path with he | hm
  · subst he
    refine ⟨by omega, by omega, fun t ht _ => by omega⟩
  · obtain ⟨s, hs, _, hx⟩ := (hv.mem w).mp (List.mem_append_left _ hm)
    have hsb := hd.record_ge hs; simp only [clausesAt] at hsb
    by_cases hsr : s.1 = r.1
    · rcases hx with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact ⟨by omega, by omega, fun t ht _ => by omega⟩
    · have := hd.apart hs hv.hr hsr
      rcases hx with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact ⟨by omega, by omega, fun t ht ht' => by omega⟩

/-! ### The literal scan (C:143–152) -/

/-- The fast literal scan from position `i` of the clause at `c` (terminator at `len`): it
stops at the terminator or at the first literal that is not false. -/
theorem scanLoop_spec {L : Lay} {db : Array Cell} {Ss : solver} (hDB : Ss.DB = toDB db)
    (hsz : db.size ≤ 2 ^ 31) (hfls : Ss.false = L.fls.toInt) (hf0 : 0 ≤ L.fls.toInt)
    (hf1 : L.fls.toInt ≤ 2 ^ 30) {c : Cell} {len N : Int} (hc0 : 0 ≤ c.toInt)
    (hc1 : c.toInt + len < 2 ^ 30) (hN : N ≤ 2 ^ 29)
    (hend : Ss.ld (c.toInt + len) = 0) (hnz : ∀ t, 2 ≤ t → t < len → Ss.ld (c.toInt + t) ≠ 0)
    (hlit : ∀ t, 2 ≤ t → t < len → -N ≤ Ss.ld (c.toInt + t) ∧ Ss.ld (c.toInt + t) ≤ N) :
    ∀ (n : Nat) (i : Cell), (len - i.toInt).toNat = n → 2 ≤ i.toInt → i.toInt ≤ len →
      (∀ t, 2 ≤ t → t < i.toInt → flag Ss (Ss.ld (c.toInt + t)) ≠ 0) →
      2 ≤ (scanLoop L db c i).toInt ∧ (scanLoop L db c i).toInt ≤ len ∧
      (∀ t, 2 ≤ t → t < (scanLoop L db c i).toInt → flag Ss (Ss.ld (c.toInt + t)) ≠ 0) ∧
      ((scanLoop L db c i).toInt = len ∨
        ((scanLoop L db c i).toInt < len ∧ flag Ss (Ss.ld (c.toInt + (scanLoop L db c i).toInt)) = 0)) := by
  have hone : ((1 : Cell)).toInt = 1 := rfl
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro i hn hi2 hil hfl
  rw [scanLoop.eq_1]
  have hci : (c + i).toInt = c.toInt + i.toInt := toInt_add (by omega) (by omega)
  have hx := ld_sim Ss hDB hsz (c + i)
  rw [hci] at hx
  by_cases hz : ld db (c + i) = 0
  · rw [if_pos (by simp [hz])]
    have h0 : Ss.ld (c.toInt + i.toInt) = 0 := by rw [← hx, hz]; rfl
    have hil' : i.toInt = len := by
      rcases Int.lt_or_eq_of_le hil with h | h
      · exact absurd h0 (hnz _ hi2 h)
      · exact h
    exact ⟨hi2, hil, hfl, Or.inl hil'⟩
  · rw [if_neg (by simp [hz])]
    have hne : Ss.ld (c.toInt + i.toInt) ≠ 0 := fun h => hz (Int32.toInt_inj.mp (by rw [hx, h]; rfl))
    have hil' : i.toInt < len := by
      rcases Int.lt_or_eq_of_le hil with h | h
      · exact h
      · rw [h] at hne; exact absurd hend hne
    have hb := hlit _ hi2 hil'
    have hfx : (L.fls + ld db (c + i)).toInt = Ss.false + Ss.ld (c.toInt + i.toInt) := by
      rw [toInt_add (by omega) (by omega), hx, hfls]
    have hy := ld_sim Ss hDB hsz (L.fls + ld db (c + i))
    rw [hfx] at hy
    by_cases hf : ld db (L.fls + ld db (c + i)) = 0
    · rw [if_pos (by simp [hf])]
      have h0 : flag Ss (Ss.ld (c.toInt + i.toInt)) = 0 := by unfold flag; rw [← hy, hf]; rfl
      exact ⟨hi2, hil, hfl, Or.inr ⟨hil', h0⟩⟩
    · rw [if_neg (by simp [hf])]
      have hfne : flag Ss (Ss.ld (c.toInt + i.toInt)) ≠ 0 := fun h =>
        hf (Int32.toInt_inj.mp (by unfold flag at h; rw [hy, h]; rfl))
      have hi1 : (i + 1).toInt = i.toInt + 1 := toInt_add (by omega) (by omega)
      exact ih (len - (i.toInt + 1)).toNat (by omega) (i + 1) (by rw [hi1]) (by rw [hi1]; omega)
        (by rw [hi1]; omega) (fun t h1 h2 => by
          rw [hi1] at h2
          rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h2) with h | h
          · exact hfl t h1 h
          · rw [h]; exact hfne)

/-! ### The outer measure -/

/-- The outer loop's measure decreased from `So` (before processing a literal) to `S` (after
it, or after a conflict). As in the faithful `propagate_main`. -/
theorem outMeasure_dec {input : Input} {S0 : solver} {vs0 : List Int} {So S : solver} {fo f : Int}
    (hSo : OutInv input S0 vs0 So fo) (hlt : So.processed < So.assigned) (hS : OutInv input S0 vs0 S f)
    (h : (S.nLemmas = So.nLemmas ∧ processedPos S = processedPos So + 1) ∨ So.nLemmas < S.nLemmas) :
    outMeasure S < outMeasure So := by
  obtain ⟨db, vs, core, -, -, -⟩ := hSo
  obtain ⟨db', vs', core', -, -, -⟩ := hS
  have ht := core.trail; have ht' := core'.trail
  have hpp : processedPos So < trailLen So := by
    simp only [processedPos, trailLen]; have := ht.forced_le; have := ht.processed_le; omega
  have hpp' : processedPos S ≤ S.nVars.toNat := by
    have := ht'.len_le; simp only [processedPos, trailLen] at *
    have := ht'.processed_le; have := ht'.assigned_le; have := ht'.forced_le; omega
  exact outMeasure_lt (core'.nVars.trans core.nVars.symm) (nLemmas_le_bound core'.database)
    (by rw [core.database.nLemmas]; omega) hpp ht.len_le hpp' h

/-! ### The statement -/

/-- What `propLoop` returns: out of memory, a correct UNSAT, or SAT with a `Settled` state
related to the start `S0` (as in the faithful `propagate_main`). -/
def PropOut (input : Input) (S0 : solver) (vs0 : List Int) (L : Lay) (r : St × UInt8) : Prop :=
  r.2 = OOM ∨ (r.2 = UNSAT ∧ input.Unsat) ∨
  (r.2 = SAT ∧ Bounds L r.1 ∧ ∃ fa sl db vs, Settled input (abs L r.1 (memoryBound input) fa sl) db vs ∧
    Rel S0 vs0 (abs L r.1 (memoryBound input) fa sl) vs)

/-- The statement of `conflict_fast` (`Analyze.lean`), taken as a hypothesis here. -/
def ConflictSpec : Prop :=
  ∀ {input : Input} {S0 : solver} {vs0 : List Int} {P : Nat} {lit : Int}
    {S : solver} {f w : Int} {db : Records} {vs : List Int} {visited rest : List Int} {r : Record},
    Visit input S0 vs0 P lit S f w db vs visited rest r → ∀ {c : Cell}, c.toInt = r.1 → ∀ {Ss : solver},
    ((S.ld c.toInt = lit ∧ Ss = S.st c.toInt (S.ld (c.toInt + 1))) ∨ (S.ld c.toInt ≠ lit ∧ Ss = S)) →
    f = 0 → (∀ l ∈ r.2, ∃ j < trailLen S, trailAt S j = l) →
    ∀ {L : Lay} {t : St} {fa sl : Int}, Bounds L t →
    abs L t (memoryBound input) fa sl = Ss.st (c.toInt + 1) lit →
    (analyze L t c).2.toInt < 0 ∨
      (Bounds L (conflictNext L (analyze L t c)) ∧
        ∃ fa' sl', OutInv input S0 vs0 (abs L (conflictNext L (analyze L t c)) (memoryBound input) fa' sl')
            (if ld (analyze L t c).1.db ((analyze L t c).2 + 1) == 0 then 1 else 0) ∧
          S.nLemmas < (conflictNext L (analyze L t c)).nLemmas.toInt)

/-! ### One visited link -/

/-- `st` keeps the array below `2^31` cells. -/
theorem st_size {db : Array Cell} (h : db.size ≤ 2 ^ 31) (p v : Cell) : (st db p v).size ≤ 2 ^ 31 :=
  (st_sim ({ (default : solver) with DB := toDB db } : solver) rfl h p v).2

/-- C:139–141: the link read at the cursor and the clause pointer computed from it. -/
theorem visit_clause {input : Input} {S0 : solver} {vs0 : List Int} {P : Nat} {lit : Int}
    {L : Lay} {t : St} {M fa sl : Int} {f wc : Int} {db : Records} {vs : List Int}
    {visited rest : List Int} {r : Record}
    (hv : Visit input S0 vs0 P lit (abs L t M fa sl) f wc db vs visited rest r) (hB : Bounds L t)
    {watch : Cell} (hwc : watch.toInt = wc) :
    (ld t.db watch).toInt = (abs L t M fa sl).ld wc ∧
    ((ld t.db watch).toInt = r.1 - 2 ∨ (ld t.db watch).toInt = r.1 - 1) ∧
    (if ld t.db (ld t.db watch - 1) = 0 then ld t.db watch + 2 else ld t.db watch + 1).toInt = r.1 ∧
    clausesAt (abs L t M fa sl).nVars + 2 ≤ r.1 ∧ r.1 + r.2.length < t.memUsed.toInt := by
  have hcb := hv.core.database.record_ge hv.hr
  have hmu := hB.memUsed
  have hcb' : clausesAt (abs L t M fa sl).nVars + 2 ≤ r.1 ∧ r.1 + r.2.length < t.memUsed.toInt := hcb
  have hn := hB.nVars.1
  have e1 : (abs L t M fa sl).nVars = L.nVars.toInt := rfl
  have e2 : (abs L t M fa sl).mem_used = t.memUsed.toInt := rfl
  simp only [clausesAt] at hcb
  have hw := ld_sim (abs L t M fa sl) rfl hB.size watch
  rw [hwc] at hw
  have hx : (abs L t M fa sl).ld wc = r.1 - 2 ∨ (abs L t M fa sl).ld wc = r.1 - 1 := by
    rcases hv.hx with ⟨h, _⟩ | ⟨h, _⟩
    · exact Or.inl h
    · exact Or.inr h
  have hwI : (ld t.db watch).toInt = r.1 - 2 ∨ (ld t.db watch).toInt = r.1 - 1 := by rw [hw]; exact hx
  have hone : ((1 : Cell)).toInt = 1 := rfl
  have htwo : ((2 : Cell)).toInt = 2 := rfl
  have hm1 : (ld t.db watch - 1).toInt = (ld t.db watch).toInt - 1 := toInt_sub (by omega) (by omega)
  have hp1 : (ld t.db watch + 1).toInt = (ld t.db watch).toInt + 1 := toInt_add (by omega) (by omega)
  have hp2 : (ld t.db watch + 2).toInt = (ld t.db watch).toInt + 2 := toInt_add (by omega) (by omega)
  have hl := ld_sim (abs L t M fa sl) rfl hB.size (ld t.db watch - 1)
  rw [hm1, hw] at hl
  have hc := hv.hc
  refine ⟨hw, hwI, ?_, hcb'⟩
  by_cases h0 : ld t.db (ld t.db watch - 1) = 0
  · have h0' : (abs L t M fa sl).ld ((abs L t M fa sl).ld wc + 1 - 2) = 0 := by
      rw [show (abs L t M fa sl).ld wc + 1 - 2 = (abs L t M fa sl).ld wc - 1 by omega, ← hl, h0]; rfl
    rw [if_pos h0', ← hw] at hc
    rw [if_pos h0, hp2]; omega
  · have h0' : ¬ (abs L t M fa sl).ld ((abs L t M fa sl).ld wc + 1 - 2) = 0 := fun h => h0 (Int32.toInt_inj.mp (by
      rw [hl, show (abs L t M fa sl).ld wc - 1 = (abs L t M fa sl).ld wc + 1 - 2 by omega, h]; rfl))
    rw [if_neg h0', ← hw] at hc
    rw [if_neg h0, hp1]; omega

/-- C:142: the other watched literal goes to position 0. The faithful `hSs` relation. -/
theorem swap_sim {L : Lay} {t : St} {M fa sl : Int} (hB : Bounds L t) {c lit : Cell}
    (hc0 : 0 ≤ c.toInt) (hc1 : c.toInt + 1 < 2 ^ 31) :
    (((abs L t M fa sl).ld c.toInt = lit.toInt ∧
        abs L { t with db := if ld t.db c = lit then st t.db c (ld t.db (c + 1)) else t.db } M fa sl =
          (abs L t M fa sl).st c.toInt ((abs L t M fa sl).ld (c.toInt + 1))) ∨
      ((abs L t M fa sl).ld c.toInt ≠ lit.toInt ∧
        abs L { t with db := if ld t.db c = lit then st t.db c (ld t.db (c + 1)) else t.db } M fa sl =
          abs L t M fa sl)) ∧
    (if ld t.db c = lit then st t.db c (ld t.db (c + 1)) else t.db).size ≤ 2 ^ 31 := by
  have hone : ((1 : Cell)).toInt = 1 := rfl
  have hl0 := ld_sim (abs L t M fa sl) rfl hB.size c
  have hl1 := ld_sim (abs L t M fa sl) rfl hB.size (c + 1)
  rw [toInt_add (by omega) (by omega), hone] at hl1
  by_cases h : ld t.db c = lit
  · rw [if_pos h]
    refine ⟨Or.inl ⟨by rw [← hl0, h], ?_⟩, st_size hB.size _ _⟩
    rw [abs_st L t M fa sl hB.size, hl1]
  · rw [if_neg h]
    exact ⟨Or.inr ⟨fun h' => h (Int32.toInt_inj.mp (by rw [hl0, h'])), rfl⟩, hB.size⟩

/-- After the swap (C:142), the cells other than `c` are unchanged. -/
theorem hSs_ld {S Ss : solver} {c lit : Int} (hc : 0 ≤ c)
    (hSs : (S.ld c = lit ∧ Ss = S.st c (S.ld (c + 1))) ∨ (S.ld c ≠ lit ∧ Ss = S)) {q : Int}
    (hq : 0 ≤ q) (hne : q ≠ c) : Ss.ld q = S.ld q := by
  rcases hSs with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact ld_st_of_ne _ _ hc hq hne
  · rfl


/-- C:144–150: the fast writes when the scan finds a literal to watch are the faithful
`foundState`. -/
theorem found_sim {L : Lay} {t : St} {M fa sl : Int} (hsz : t.db.size ≤ 2 ^ 31)
    {c i lit watch w : Cell} (hc0 : 0 ≤ c.toInt) (hci : c.toInt + i.toInt < 2 ^ 30) (hi2 : 2 ≤ i.toInt)
    (hwa0 : 0 ≤ watch.toInt) (hwa1 : watch.toInt ≠ c.toInt + 1) (hwa2 : watch.toInt ≠ c.toInt + i.toInt)
    (hw : (abs L t M fa sl).ld watch.toInt = w.toInt)
    (hx : -2 ^ 29 ≤ (ld t.db (c + i)).toInt ∧ (ld t.db (c + i)).toInt ≤ 2 ^ 29)
    (hfirst : 0 ≤ L.first.toInt ∧ L.first.toInt ≤ 2 ^ 30) :
    abs L { t with
        db := addWatch L (st (st (st t.db (c + 1) (ld t.db (c + i))) (c + i) lit) watch
          (ld (st (st t.db (c + 1) (ld t.db (c + i))) (c + i) lit) w)) (ld t.db (c + i)) w } M fa sl =
      foundState (abs L t M fa sl) c.toInt i.toInt watch.toInt lit.toInt := by
  have hone : ((1 : Cell)).toInt = 1 := rfl
  have hc1 : (c + 1).toInt = c.toInt + 1 := by rw [toInt_add (by omega) (by omega), hone]
  have hcI : (c + i).toInt = c.toInt + i.toInt := toInt_add (by omega) (by omega)
  have hxI := ld_sim (abs L t M fa sl) rfl hsz (c + i)
  rw [hcI] at hxI
  generalize hxd : ld t.db (c + i) = x at hx hxI ⊢
  -- the first two writes (C:145–146)
  have s1 := st_size hsz (c + 1) x
  have e1 : abs L { t with db := st t.db (c + 1) x } M fa sl =
      (abs L t M fa sl).st (c.toInt + 1) ((abs L t M fa sl).ld (c.toInt + i.toInt)) := by
    rw [← hxI, ← hc1]; exact abs_st L t M fa sl hsz _ _
  have s2 := st_size s1 (c + i) lit
  have e2 : abs L { t with db := st (st t.db (c + 1) x) (c + i) lit } M fa sl =
      ((abs L t M fa sl).st (c.toInt + 1) ((abs L t M fa sl).ld (c.toInt + i.toInt))).st
        (c.toInt + i.toInt) lit.toInt := by
    rw [← e1, ← hcI]; exact abs_st L { t with db := st t.db (c + 1) x } M fa sl s1 _ _
  generalize hS2d : ((abs L t M fa sl).st (c.toInt + 1) ((abs L t M fa sl).ld (c.toInt + i.toInt))).st
    (c.toInt + i.toInt) lit.toInt = S2 at e2
  have hS2w : S2.ld watch.toInt = w.toInt := by
    rw [← hS2d, ld_st_of_ne _ _ (by omega) hwa0 hwa2, ld_st_of_ne _ _ (by omega) hwa0 hwa1, hw]
  have hS2c : S2.ld (c.toInt + 1) = x.toInt := by
    rw [← hS2d, ld_st_of_ne _ _ (by omega) (by omega) (by omega), ld_st_self _ _ (by omega), hxI]
  -- unlink (C:147–148)
  have s3 := st_size s2 watch (ld (st (st t.db (c + 1) x) (c + i) lit) w)
  have hl4 := ld_sim S2 (by rw [← e2]; rfl) s2 w
  have e3 : abs L { t with
        db := st (st (st t.db (c + 1) x) (c + i) lit) watch (ld (st (st t.db (c + 1) x) (c + i) lit) w) }
      M fa sl = S2.st watch.toInt (S2.ld (S2.ld watch.toInt)) := by
    rw [hS2w, ← hl4, ← e2]; exact abs_st L { t with db := st (st t.db (c + 1) x) (c + i) lit } M fa sl s2 _ _
  generalize hS3d : S2.st watch.toInt (S2.ld (S2.ld watch.toInt)) = S3 at e3
  have hS3c : S3.ld (c.toInt + 1) = x.toInt := by
    rw [← hS3d, ld_st_of_ne _ _ hwa0 (by omega) (fun h => hwa1 h.symm), hS2c]
  -- the new watch (C:149)
  generalize hdb5 : st (st (st t.db (c + 1) x) (c + i) lit) watch (ld (st (st t.db (c + 1) x) (c + i) lit) w)
    = db5 at s3 e3
  have hf3 : S3.first = L.first.toInt := by rw [← e3]; rfl
  have hfx : (L.first + x).toInt = S3.first + x.toInt := by rw [toInt_add (by omega) (by omega), hf3]
  have s4 := st_size s3 w (ld db5 (L.first + x))
  have hl5 := ld_sim S3 (by rw [← e3]; rfl) s3 (L.first + x)
  rw [hfx] at hl5
  have e4 : abs L { t with db := st db5 w (ld db5 (L.first + x)) } M fa sl =
      S3.st w.toInt (S3.ld (S3.first + x.toInt)) := by
    rw [← hl5, ← e3]; exact abs_st L { t with db := db5 } M fa sl s3 _ _
  have e5 : abs L { t with db := addWatch L db5 x w } M fa sl =
      (S3.st w.toInt (S3.ld (S3.first + x.toInt))).st (S3.first + x.toInt) w.toInt := by
    rw [← e4, ← hfx]; exact abs_st L { t with db := st db5 w (ld db5 (L.first + x)) } M fa sl s4 _ _
  rw [e5]
  unfold foundState
  dsimp only
  rw [hS2d, ← hS2w, hS3d, hS3c, MicrosatLean.Faithful.addWatch]
  obtain ⟨D, hD⟩ := st_eq S3 (S2.ld watch.toInt) (S3.ld (S3.first + x.toInt))
  rw [hD]



/-- C:153: the fast `assign` of the clause at `c` (then `assigned + 1`) is the faithful one. -/
theorem assign_abs {L : Lay} {t : St} {M fa sl : Int} (hsz : t.db.size ≤ 2 ^ 31) {c : Cell}
    (forced : Bool) (hc : 0 ≤ c.toInt ∧ c.toInt < 2 ^ 30)
    (hlit : -2 ^ 29 ≤ (abs L t M fa sl).ld c.toInt ∧ (abs L t M fa sl).ld c.toInt ≤ 2 ^ 29)
    (hA : -2 ^ 30 ≤ t.assigned.toInt ∧ t.assigned.toInt < 2 ^ 30)
    (hL : 0 ≤ L.fls.toInt ∧ L.fls.toInt < 2 ^ 30 ∧ 0 ≤ L.reason.toInt ∧ L.reason.toInt < 2 ^ 30) :
    abs L { t with db := assign L t.db t.assigned c forced, assigned := t.assigned + 1 } M fa sl =
      MicrosatLean.Faithful.assign (abs L t M fa sl) c.toInt (fl forced) ∧
    (assign L t.db t.assigned c forced).size ≤ 2 ^ 31 := by
  have hone : ((1 : Cell)).toInt = 1 := rfl
  obtain ⟨hDB, hsz'⟩ := assign_sim (abs L t M fa sl) rfl hsz (L := L) rfl rfl rfl hL
    (assigned := t.assigned) rfl hc hlit forced
  refine ⟨?_, hsz'⟩
  obtain ⟨D, hD⟩ := assign_fields (abs L t M fa sl) c.toInt (fl forced)
  have hD' : D = toDB (assign L t.db t.assigned c forced) := by
    have := hDB; unfold fl at hD; rw [hD] at this; exact this
  rw [hD, hD']
  have ha : (t.assigned + 1).toInt = t.assigned.toInt + 1 := by
    rw [toInt_add (by omega) (by omega), hone]
  unfold abs; dsimp only; rw [ha]

/-! ### The watch loop -/

/-- The watch loop (C:138–158) for the literal at position `processedPos So`, by induction on
the links left; `IH` is the outer loop's statement for smaller outer measures. -/
theorem propLoop_inner (hconf : ConflictSpec) {input : Input} {S0 : solver} {vs0 : List Int}
    {L : Lay} {So : solver} {fo : Int} (hSo : OutInv input S0 vs0 So fo)
    (hlt : So.processed < So.assigned)
    (IH : ∀ (s : St) (db : Array Cell) (a p : Cell) (forced : Bool) (lit watch : Cell) (fa sl : Int),
      outMeasure (abs L (pst s db a p) (memoryBound input) fa sl) < outMeasure So →
      Bounds L (pst s db a p) → (watch.toInt < 0 ∨ ld db watch = END) →
      OutInv input S0 vs0 (abs L (pst s db a p) (memoryBound input) fa sl) (fl forced) →
      PropOut input S0 vs0 L (propLoop L s db a p forced lit watch)) :
    ∀ (m : Nat) (s : St) (db : Array Cell) (a p : Cell) (forced : Bool) (lit watch : Cell) (fa sl : Int),
      (linksAfter (abs L (pst s db a p) (memoryBound input) fa sl) watch.toInt).length = m →
      Bounds L (pst s db a p) → 0 ≤ watch.toInt →
      WInv input S0 vs0 (processedPos So) lit.toInt (abs L (pst s db a p) (memoryBound input) fa sl)
        (fl forced) watch.toInt →
      (abs L (pst s db a p) (memoryBound input) fa sl).nLemmas = So.nLemmas →
      PropOut input S0 vs0 L (propLoop L s db a p forced lit watch) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro s db a p forced lit watch fa sl hm hB hw0 hW hnl
  have hone : ((1 : Cell)).toInt = 1 := rfl
  have htwo : ((2 : Cell)).toInt = 2 := rfl
  have hsz : db.size ≤ 2 ^ 31 := hB.size
  have hmu : s.memUsed.toInt ≤ 2 ^ 30 := hB.memUsed
  -- the list ends: back to the outer loop
  by_cases hend : ld db watch = END
  · have hendI : (abs L (pst s db a p) (memoryBound input) fa sl).ld watch.toInt = MicrosatLean.Faithful.END := by
      rw [← ld_sim (abs L (pst s db a p) (memoryBound input) fa sl) rfl hB.size watch, hend]; rfl
    obtain ⟨hout, hpp⟩ := WInv.exit hW hendI
    exact IH s db a p forced lit watch fa sl (outMeasure_dec hSo hlt hout (Or.inl ⟨hnl, hpp⟩)) hB
      (Or.inr hend) hout
  have hneI : (abs L (pst s db a p) (memoryBound input) fa sl).ld watch.toInt ≠ MicrosatLean.Faithful.END :=
    fun h => hend (Int32.toInt_inj.mp (by
      rw [ld_sim (abs L (pst s db a p) (memoryBound input) fa sl) rfl hB.size watch, h]; rfl))
  obtain ⟨rdb, rvs, visited, rest, r, hv⟩ := WInv.visit hW hneI
  have hl := hv.core.layout; have hn := hl.num; have hn1 := hl.nVars_pos
  have hN := hB.nVars
  have e1 : (abs L (pst s db a p) (memoryBound input) fa sl).nVars = L.nVars.toInt := rfl
  have e2 : (abs L (pst s db a p) (memoryBound input) fa sl).false = L.fls.toInt := rfl
  have e3 : (abs L (pst s db a p) (memoryBound input) fa sl).first = L.first.toInt := rfl
  have e4 : (abs L (pst s db a p) (memoryBound input) fa sl).reason = L.reason.toInt := rfl
  obtain ⟨hwI, hwr, hcI, hcb, hce⟩ := visit_clause hv hB (watch := watch) rfl
  have hw : ¬ watch < 0 := fun h => by have := Int32.lt_iff_toInt_lt.mp h; simp at this; omega
  have heq := propLoop.eq_1 L s db a p forced lit watch
  rw [if_neg hw] at heq
  simp only [beq_iff_eq, hend, if_false] at heq
  rw [heq]; clear heq
  dsimp only [pst] at hwI hwr hcI hce
  simp only [clausesAt] at hcb
  generalize hwd : ld db watch = w at hwI hwr hcI ⊢
  generalize hcd : (if ld db (w - 1) = 0 then w + 2 else w + 1) = c at hcI ⊢
  obtain ⟨hSs, hsz1⟩ := swap_sim (t := pst s db a p) (M := memoryBound input) (fa := fa) (sl := sl) hB
    (c := c) (lit := lit) (by omega) (by omega)
  dsimp only [pst] at hSs hsz1
  generalize hdb1 : (if ld db c = lit then st db c (ld db (c + 1)) else db) = db1 at hSs hsz1 ⊢
  have hSsC := hSs
  rw [hcI] at hSs
  -- the visited record and its cells
  obtain ⟨cur0, cur1, cur⟩ := Visit.cursor_ne hv
  obtain ⟨ra, rb, rtl, hr2, -, -, hclause⟩ := Visit.slot hv
  have hlen2 : 2 ≤ r.2.length := by rw [hr2]; simp
  have hcore := hv.core
  have hrlit : ∀ t, 2 ≤ t → t < (r.2.length : Int) →
      (abs L (pst s db1 a p) (memoryBound input) fa sl).ld (r.1 + t) = r.2[t.toNat]! ∧
      -L.nVars.toInt ≤ r.2[t.toNat]! ∧ r.2[t.toNat]! ≤ L.nVars.toInt ∧ r.2[t.toNat]! ≠ 0 := by
    intro t h0 h1
    have hmem : r.2[t.toNat]! ∈ r.2 := by
      rw [getElem!_pos r.2 t.toNat (by omega)]; exact List.getElem_mem _
    have hin := inRange_iff.mp (hcore.record_lit hv.hr hmem)
    refine ⟨?_, hin.2.1, hin.2.2, hin.1⟩
    rw [hSs_ld (by omega) hSs (by omega) (by omega), getElem!_pos r.2 t.toNat (by omega),
      ← hclause.1 t.toNat (by omega)]
    congr 1; omega
  have hrend : (abs L (pst s db1 a p) (memoryBound input) fa sl).ld (r.1 + r.2.length) = 0 := by
    rw [hSs_ld (by omega) hSs (by omega) (by omega)]; exact hclause.2
  -- the scan (C:143)
  have hscan := scanLoop_spec (L := L) (db := db1) (Ss := abs L (pst s db1 a p) (memoryBound input) fa sl)
    rfl hsz1 rfl (by omega) (by omega) (c := c) (len := r.2.length) (N := L.nVars.toInt) (by omega)
    (by omega) (by omega) (by rw [hcI]; exact hrend)
    (fun t h1 h2 => by rw [hcI, (hrlit t h1 h2).1]; exact (hrlit t h1 h2).2.2.2)
    (fun t h1 h2 => by rw [hcI, (hrlit t h1 h2).1]; exact ⟨(hrlit t h1 h2).2.1, (hrlit t h1 h2).2.2.1⟩)
    _ 2 rfl (by omega) (by omega) (fun t h1 h2 => absurd h2 (by omega))
  generalize hid : scanLoop L db1 c 2 = i at hscan ⊢
  obtain ⟨hi2, hiL, hfl, hio⟩ := hscan
  rw [hcI] at hfl hio
  have hci : (c + i).toInt = r.1 + i.toInt := by rw [toInt_add (by omega) (by omega), hcI]
  have hxI := ld_sim (abs L (pst s db1 a p) (memoryBound input) fa sl) rfl hsz1 (c + i)
  rw [hci] at hxI
  have hwS : (abs L (pst s db1 a p) (memoryBound input) fa sl).ld watch.toInt = w.toInt := by
    rw [hSs_ld (by omega) hSs cur0 (by have := cur 0 (by omega) (by omega); omega), hwI]
  by_cases hx0 : ld db1 (c + i) = 0
  · -- the scan reached the terminator (C:149–158)
    rw [if_neg (by simp [hx0])]
    have hiE : i.toInt = r.2.length := by
      rcases hio with h | ⟨h, -⟩
      · exact h
      · have := hrlit i.toInt hi2 h
        exact absurd (by rw [← this.1, ← hxI, hx0]; rfl) this.2.2.2
    have hnz : ∀ t, 2 ≤ t → t < (r.2.length : Int) →
        (abs L (pst s db1 a p) (memoryBound input) fa sl).ld (r.1 + t) ≠ 0 := fun t h1 h2 => by
      rw [(hrlit t h1 h2).1]; exact (hrlit t h1 h2).2.2.2
    have hend' : (abs L (pst s db1 a p) (memoryBound input) fa sl).ld (r.1 + i.toInt) = 0 := by
      rw [hiE]; exact hrend
    have hc1 : (c + 1).toInt = r.1 + 1 := by rw [toInt_add (by omega) (by omega), hcI, hone]
    have hsz2 := st_size hsz1 (c + 1) lit
    have hT : abs L (pst s (st db1 (c + 1) lit) a p) (memoryBound input) fa sl =
        (abs L (pst s db1 a p) (memoryBound input) fa sl).st (r.1 + 1) lit.toInt := by
      rw [← hc1]; exact abs_st L (pst s db1 a p) _ fa sl hsz1 _ _
    generalize hdb2 : st db1 (c + 1) lit = db2 at hT hsz2 ⊢
    obtain ⟨hTc, hTf⟩ := Visit.unit_flag hv rfl hSs
    have hymem : otherLit r lit.toInt ∈ r.2 := by
      simp only [otherLit, hr2]; split <;> simp
    have hyr := inRange_iff.mp (hcore.record_lit hv.hr hymem)
    have hTfls : ((abs L (pst s db1 a p) (memoryBound input) fa sl).st (r.1 + 1) lit.toInt).false =
        L.fls.toInt := by rw [st_false]; rfl
    have hoI : (ld db2 c).toInt = otherLit r lit.toInt := by
      rw [ld_sim (abs L (pst s db2 a p) (memoryBound input) fa sl) rfl hsz2 c, hT, hcI, hTc]
    have hTw : ((abs L (pst s db1 a p) (memoryBound input) fa sl).st (r.1 + 1) lit.toInt).ld watch.toInt =
        w.toInt := by
      rw [ld_st_of_ne _ _ (by omega) cur0 (cur 1 (by omega) (by omega)), hwS]
    have hw0' : 0 ≤ w.toInt := by omega
    -- the flags of the other watched literal, read in `db2`
    have hyt := ld_sim (abs L (pst s db2 a p) (memoryBound input) fa sl) rfl hsz2 (L.fls - ld db2 c)
    rw [toInt_sub (by omega) (by omega), hoI, hT, show L.fls.toInt - otherLit r lit.toInt =
      ((abs L (pst s db1 a p) (memoryBound input) fa sl).st (r.1 + 1) lit.toInt).false +
        -otherLit r lit.toInt by rw [hTfls]; omega, hTf _ (by omega) (by omega)] at hyt
    have hyf := ld_sim (abs L (pst s db2 a p) (memoryBound input) fa sl) rfl hsz2 (L.fls + ld db2 c)
    rw [toInt_add (by omega) (by omega), hoI, hT, show L.fls.toInt + otherLit r lit.toInt =
      ((abs L (pst s db1 a p) (memoryBound input) fa sl).st (r.1 + 1) lit.toInt).false +
        otherLit r lit.toInt by rw [hTfls], hTf _ (by omega) (by omega)] at hyf
    have hiL' : i.toInt ≤ r.2.length := by omega
    by_cases hA : ld db2 (L.fls - ld db2 c) = 0
    · rw [if_neg (by simp [hA])]
      have hyt0 : flag (abs L (pst s db a p) (memoryBound input) fa sl) (-otherLit r lit.toInt) = 0 := by
        rw [← hyt, hA]; rfl
      by_cases hB0 : ld db2 (L.fls + ld db2 c) = 0
      · -- C:153: a new unit
        rw [if_pos hB0]
        have hyf0 : flag (abs L (pst s db a p) (memoryBound input) fa sl) (otherLit r lit.toInt) = 0 := by
          rw [← hyf, hB0]; rfl
        have key := Visit.assign_step hv rfl hSs hrend hnz hi2 hiL' hfl hend' hyt0 hyf0 (f := fl forced)
        rw [hTw] at key
        have htr := hcore.trail
        have hAa : -2 ^ 30 ≤ a.toInt ∧ a.toInt < 2 ^ 30 := by
          have h1 := htr.forced_le; have h2 := htr.processed_le; have h3 := htr.assigned_le
          have h4 := htr.len_le
          simp only [trailLen] at h4
          have : (abs L (pst s db a p) (memoryBound input) fa sl).assigned = a.toInt := rfl
          omega
        have hTcI : (abs L (pst s db2 a p) (memoryBound input) fa sl).ld c.toInt = otherLit r lit.toInt := by
          rw [hT, hcI, hTc]
        obtain ⟨hAeq, hAsz⟩ := assign_abs (L := L) (t := pst s db2 a p) (M := memoryBound input) (fa := fa)
          (sl := sl) hsz2 (c := c) forced ⟨by omega, by omega⟩ (by rw [hTcI]; omega) hAa
          ⟨by omega, by omega, by omega, by omega⟩
        have hA' : abs L (pst s (assign L db2 a c forced) (a + 1) p) (memoryBound input) fa sl =
            MicrosatLean.Faithful.assign ((abs L (pst s db1 a p) (memoryBound input) fa sl).st (r.1 + 1) lit.toInt)
              r.1 (fl forced) := by
          rw [← hT, ← hcI]; exact hAeq
        refine ih _ ?_ s (assign L db2 a c forced) (a + 1) p forced lit w fa sl rfl
          ⟨hAsz, hB.nVars, hB.memUsed, hB.maxLemmas⟩ hw0' (by rw [hA']; exact key.1)
          (by rw [hA', key.2.1]; exact hnl)
        rw [hA', ← hm]; exact key.2.2
      · rw [if_neg hB0]
        have hyS : flag (abs L (pst s db a p) (memoryBound input) fa sl) (otherLit r lit.toInt) ≠ 0 :=
          fun h => hB0 (Int32.toInt_inj.mp (by rw [hyf, h]; rfl))
        have hall := Visit.scan_all_false hv rfl hSs hrend hnz hi2 hiL' hfl hend' hyS
        cases forced
        · -- C:155–158: a conflict below the root, analyzed
          rw [if_neg (by simp)]
          have hTC : abs L (pst s db2 a p) (memoryBound input) fa sl =
              (abs L (pst s db1 a p) (memoryBound input) fa sl).st (c.toInt + 1) lit.toInt := by
            rw [hcI]; exact hT
          have hc := hconf hv hcI hSsC rfl hall (t := pst s db2 a p)
            ⟨hsz2, hB.nVars, hB.memUsed, hB.maxLemmas⟩ hTC
          have hR' : analyze L { s with db := db2, assigned := a, processed := p } c =
              analyze L (pst s db2 a p) c := rfl
          rw [hR']
          generalize analyze L (pst s db2 a p) c = R at hc ⊢
          have hz : ((0 : Cell)).toInt = 0 := rfl
          by_cases hneg : R.snd < 0
          · rw [if_pos hneg]; exact Or.inl rfl
          · rw [if_neg hneg]
            rcases hc with hneg' | ⟨hB', fa', sl', hout', hlt'⟩
            · exact absurd (Int32.lt_iff_toInt_lt.mpr (by rw [hz]; exact hneg')) hneg
            · exact IH _ _ _ _ _ _ _ fa' sl' (outMeasure_dec hSo hlt hout' (Or.inr (by rw [← hnl]; exact hlt')))
                hB' (Or.inl (by decide)) hout'
        · -- C:154: a conflict at the root
          rw [if_pos rfl]
          refine Or.inr (Or.inl ⟨rfl, ?_⟩)
          have hroot : ∀ j < trailLen (abs L (pst s db a p) (memoryBound input) fa sl),
              RootLevel (abs L (pst s db a p) (memoryBound input) fa sl) j := by
            rcases hv.pmode.1 with ⟨_, h'⟩ | ⟨h0, -⟩
            · exact h'
            · exact absurd h0 (by simp [fl])
          exact hcore.unsat_of_root_conflict hv.hr fun l hl => by
            obtain ⟨j, hj, he⟩ := hall l hl; exact ⟨j, hj, hroot j hj, he⟩
    · -- C:151: the other watched literal is true
      rw [if_pos (by simp [hA])]
      have hy : ((abs L (pst s db1 a p) (memoryBound input) fa sl).st (r.1 + 1) lit.toInt).ld
          (((abs L (pst s db1 a p) (memoryBound input) fa sl).st (r.1 + 1) lit.toInt).false +
            -((abs L (pst s db1 a p) (memoryBound input) fa sl).st (r.1 + 1) lit.toInt).ld r.1) ≠ 0 := by
        rw [hTc, hTf _ (by omega) (by omega), ← hyt]
        exact fun h => hA (Int32.toInt_inj.mp (by rw [h]; rfl))
      have key := Visit.true_step hv rfl hSs hy
      rw [hTw] at key
      refine ih _ ?_ s db2 a p forced lit w fa sl rfl ⟨hsz2, hB.nVars, hB.memUsed, hB.maxLemmas⟩ hw0'
        (by rw [hT]; exact key.1) (by rw [hT, key.2.1]; exact hnl)
      rw [hT, ← hm]; exact key.2.2
  · -- C:144–150: a literal to watch was found
    rw [if_pos (by simp [hx0])]
    have hxne : (abs L (pst s db1 a p) (memoryBound input) fa sl).ld (r.1 + i.toInt) ≠ 0 := fun h =>
      hx0 (Int32.toInt_inj.mp (by rw [hxI, h]; rfl))
    have hilt : i.toInt < r.2.length ∧ flag (abs L (pst s db1 a p) (memoryBound input) fa sl)
        ((abs L (pst s db1 a p) (memoryBound input) fa sl).ld (r.1 + i.toInt)) = 0 := by
      rcases hio with h | h
      · rw [h] at hxne; exact absurd hrend hxne
      · exact h
    have hxb := hrlit i.toInt hi2 hilt.1
    have key := Visit.found_step hv rfl hSs (t := i.toInt) hi2 hilt.1 hilt.2
    have hfs := found_sim (L := L) (t := pst s db1 a p) (M := memoryBound input) (fa := fa) (sl := sl)
      hsz1 (c := c) (i := i) (lit := lit) (watch := watch) (w := w) (by omega) (by omega) hi2 cur0
      (by rw [hcI]; exact cur 1 (by omega) (by omega)) (by rw [hcI]; exact cur i.toInt (by omega) (by omega))
      hwS (by rw [hxI, hxb.1]; omega) (by omega)
    rw [hcI] at hfs
    generalize hdb6 : addWatch L (st (st (st db1 (c + 1) (ld db1 (c + i))) (c + i) lit) watch
      (ld (st (st db1 (c + 1) (ld db1 (c + i))) (c + i) lit) w)) (ld db1 (c + i)) w = db6 at hfs ⊢
    have hfs' : abs L (pst s db6 a p) (memoryBound input) fa sl =
        foundState (abs L (pst s db1 a p) (memoryBound input) fa sl) r.1 i.toInt watch.toInt lit.toInt := hfs
    have hsz6 : db6.size ≤ 2 ^ 31 := by
      rw [← hdb6]; exact st_size (st_size (st_size (st_size (st_size hsz1 _ _) _ _) _ _) _ _) _ _
    refine ih _ ?_ s db6 a p forced lit watch fa sl rfl ⟨hsz6, hB.nVars, hB.memUsed, hB.maxLemmas⟩ hw0
      (by rw [hfs']; exact key.1) (by rw [hfs', key.2.1]; exact hnl)
    rw [hfs', ← hm]; exact key.2.2

/-! ### The outer loop -/

/-- The outer loop (C:135–157) from a call whose cursor is at the end of a list (or `NONE`),
by induction on `outMeasure`. -/
theorem propLoop_outer (hconf : ConflictSpec) {input : Input} {S0 : solver} {vs0 : List Int} {L : Lay} :
    ∀ (n : Nat) (s : St) (db : Array Cell) (a p : Cell) (forced : Bool) (lit watch : Cell) (fa sl : Int),
      outMeasure (abs L (pst s db a p) (memoryBound input) fa sl) = n →
      Bounds L (pst s db a p) → (watch.toInt < 0 ∨ ld db watch = END) →
      OutInv input S0 vs0 (abs L (pst s db a p) (memoryBound input) fa sl) (fl forced) →
      PropOut input S0 vs0 L (propLoop L s db a p forced lit watch) := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro s db a p forced lit watch fa sl hn hB hw hout
  have hz : ((0 : Cell)).toInt = 0 := rfl
  have hone : ((1 : Cell)).toInt = 1 := rfl
  have hsz : db.size ≤ 2 ^ 31 := hB.size
  have hwE : (if watch < 0 then END else ld db watch) = END := by
    rcases hw with h | h
    · rw [if_pos (Int32.lt_iff_toInt_lt.mpr (by rw [hz]; exact h))]
    · by_cases h' : watch < 0
      · rw [if_pos h']
      · rw [if_neg h', h]
  have heq := propLoop.eq_1 L s db a p forced lit watch
  simp only [hwE, beq_self_eq_true, if_true] at heq
  rw [heq]; clear heq
  obtain ⟨db0, vs, core, -, -, -⟩ := id hout
  have ht := core.trail; have hl := core.layout; have hnum := hl.num; have hN := hB.nVars
  have eA : (abs L (pst s db a p) (memoryBound input) fa sl).assigned = a.toInt := rfl
  have eP : (abs L (pst s db a p) (memoryBound input) fa sl).processed = p.toInt := rfl
  have eN : (abs L (pst s db a p) (memoryBound input) fa sl).nVars = L.nVars.toInt := rfl
  have h4 := ht.len_le
  simp only [trailLen] at h4
  have h1 := ht.forced_le; have h2 := ht.processed_le; have h3 := ht.assigned_le
  obtain ⟨hN1, hN2⟩ := hN
  have eF : (abs L (pst s db a p) (memoryBound input) fa sl).first = L.first.toInt := rfl
  by_cases hpa : p < a
  · -- C:135–138: the next literal to process
    rw [if_pos hpa]
    have hpa' : p.toInt < a.toInt := Int32.lt_iff_toInt_lt.mp hpa
    have hW := WInv.init hout (by rw [eA, eP]; exact hpa')
    have hp1 : (p + 1).toInt = p.toInt + 1 := by rw [toInt_add (by omega) (by omega), hone]
    have hlitI := ld_sim (abs L (pst s db a p) (memoryBound input) fa sl) rfl hsz p
    have hlr := inRange_iff.mp (ht.lit (processedPos (abs L (pst s db a p) (memoryBound input) fa sl))
      (by simp only [processedPos, trailLen]; omega))
    have hlr' : -L.nVars.toInt ≤ (ld db p).toInt ∧ (ld db p).toInt ≤ L.nVars.toInt := by
      rw [hlitI, ← eP, ht.ld_processed]; exact ⟨hlr.2.1, hlr.2.2⟩
    have hwI : (L.first + ld db p).toInt = (abs L (pst s db a p) (memoryBound input) fa sl).first +
        (abs L (pst s db a p) (memoryBound input) fa sl).ld (abs L (pst s db a p) (memoryBound input) fa sl).processed := by
      rw [toInt_add (by omega) (by omega), hlitI]; rfl
    have hS1 : abs L (pst s db a (p + 1)) (memoryBound input) fa sl =
        { abs L (pst s db a p) (memoryBound input) fa sl with
          processed := (abs L (pst s db a p) (memoryBound input) fa sl).processed + 1 } := by
      unfold abs; dsimp only; rw [hp1]
    have hW' : WInv input S0 vs0 (processedPos (abs L (pst s db a p) (memoryBound input) fa sl))
        (ld db p).toInt (abs L (pst s db a (p + 1)) (memoryBound input) fa sl) (fl forced)
        (L.first + ld db p).toInt := by
      rw [hwI, hlitI, hS1]; exact hW
    have hnl : (abs L (pst s db a (p + 1)) (memoryBound input) fa sl).nLemmas =
        (abs L (pst s db a p) (memoryBound input) fa sl).nLemmas := rfl
    exact propLoop_inner hconf hout (by rw [eA, eP]; exact hpa')
      (fun s' db' a' p' f' l' w' fa' sl' hlt' => ih _ (by rw [← hn]; exact hlt') s' db' a' p' f' l' w' fa' sl' rfl)
      _ s db a (p + 1) forced (ld db p) (L.first + ld db p) fa sl rfl
      ⟨hsz, hB.nVars, hB.memUsed, hB.maxLemmas⟩ (by rw [toInt_add (by omega) (by omega)]; omega) hW' hnl
  · -- C:157: no literal left
    rw [if_neg hpa]
    have hpa' : a.toInt ≤ p.toInt := Int.not_lt.mp fun h => hpa (Int32.lt_iff_toInt_lt.mpr h)
    obtain ⟨db', vs', hset, hrel⟩ := OutInv.post hout (by rw [eA, eP]; exact hpa')
    refine Or.inr (Or.inr ⟨rfl, ⟨hsz, hB.nVars, hB.memUsed, hB.maxLemmas⟩, fa, sl, db', vs', ?_⟩)
    cases forced
    · exact ⟨hset, hrel⟩
    · exact ⟨hset, hrel⟩

/-! ### `propagate` -/

/-- With an empty trail, `PMode` holds for any flag. -/
theorem PMode.empty {S : solver} (h : trailLen S = 0) (f : Int) (P : Nat) : PMode S f P := by
  refine ⟨?_, fun k _ hk => absurd hk (by omega)⟩
  by_cases hf : f = 0
  · exact Or.inr ⟨hf, fun i hi => absurd hi (by omega), fun hP => absurd hP (by omega)⟩
  · exact Or.inl ⟨hf, fun i hi => absurd hi (by omega)⟩

/-- The fast `propagate` from the top of `solve`'s loop: the faithful `propagate_spec`, with
out of memory as an outcome. -/
theorem propagate_fast (hconf : ConflictSpec) {input : Input} {L : Lay} {s : St} {fa sl d : Int}
    (hB : Bounds L s) (inv : Inv input (abs L s (memoryBound input) fa sl) d) :
    (propagate L s).2 = OOM ∨ ((propagate L s).2 = UNSAT ∧ input.Unsat) ∨
    ((propagate L s).2 = SAT ∧ Bounds L (propagate L s).1 ∧ ∃ fa' sl',
      (abs L (propagate L s).1 (memoryBound input) fa' sl').maxLemmas = s.maxLemmas.toInt ∧
      (((abs L (propagate L s).1 (memoryBound input) fa' sl').nLemmas = s.nLemmas.toInt ∧
          trailLen (abs L s (memoryBound input) fa sl) ≤
            trailLen (abs L (propagate L s).1 (memoryBound input) fa' sl') ∧
          ∃ db vs, Settled input (abs L (propagate L s).1 (memoryBound input) fa' sl') db vs ∧
            Cursor (abs L (propagate L s).1 (memoryBound input) fa' sl') vs d) ∨
        (s.nLemmas.toInt < (abs L (propagate L s).1 (memoryBound input) fa' sl').nLemmas ∧
          ∃ db vs, Settled input (abs L (propagate L s).1 (memoryBound input) fa' sl') db vs))) := by
  obtain ⟨db0, vs0, core0, watched0, mode0, cursor0⟩ := inv
  have hout := OutInv.init core0 watched0 mode0
  have ht := core0.trail; have hl := core0.layout; have hnum := hl.num
  obtain ⟨hN1, hN2⟩ := hB.nVars
  have eN : (abs L s (memoryBound input) fa sl).nVars = L.nVars.toInt := rfl
  have eR : (abs L s (memoryBound input) fa sl).reason = L.reason.toInt := rfl
  -- the flag of C:134
  have hflag : OutInv input (abs L s (memoryBound input) fa sl) vs0 (abs L s (memoryBound input) fa sl)
      (fl (ld s.db (L.reason + absC (ld s.db s.processed)) != 0)) := by
    by_cases h0 : trailLen (abs L s (memoryBound input) fa sl) = 0
    · obtain ⟨db, vs, core, wt, -, rel⟩ := hout
      exact ⟨db, vs, core, wt, PMode.empty h0 _ _, rel⟩
    · apply OutInv.flag hout
      have hlt : processedPos (abs L s (memoryBound input) fa sl) < trailLen (abs L s (memoryBound input) fa sl) := by
        rcases mode0 with ⟨hp0, -⟩ | ⟨hp1, -, -⟩ <;> omega
      have hvI := ld_sim (abs L s (memoryBound input) fa sl) rfl hB.size s.processed
      have hlr := inRange_iff.mp (ht.lit _ hlt)
      rw [← ht.ld_processed] at hlr
      have hvI' : (ld s.db s.processed).toInt = (abs L s (memoryBound input) fa sl).ld
          (abs L s (memoryBound input) fa sl).processed := hvI
      have habs := toInt_absC (a := ld s.db s.processed) (by omega)
      rw [hvI'] at habs
      have hab : 0 ≤ MicrosatLean.Faithful.abs ((abs L s (memoryBound input) fa sl).ld
          (abs L s (memoryBound input) fa sl).processed) ∧ MicrosatLean.Faithful.abs
          ((abs L s (memoryBound input) fa sl).ld (abs L s (memoryBound input) fa sl).processed) ≤ L.nVars.toInt := by
        unfold MicrosatLean.Faithful.abs; split <;> omega
      have hrI : (L.reason + absC (ld s.db s.processed)).toInt = (abs L s (memoryBound input) fa sl).reason +
          MicrosatLean.Faithful.abs ((abs L s (memoryBound input) fa sl).ld (abs L s (memoryBound input) fa sl).processed) := by
        rw [toInt_add (by omega) (by omega), habs]; rfl
      have hfI := ld_sim (abs L s (memoryBound input) fa sl) rfl hB.size (L.reason + absC (ld s.db s.processed))
      rw [hrI] at hfI
      rw [fl_ne_zero, ← hfI]
      constructor
      · intro h; simpa using fun h' => h (by rw [h']; rfl)
      · intro h h'; simp only [bne_iff_ne, ne_eq] at h; exact h (Int32.toInt_inj.mp (by rw [h']; rfl))
  have hres := propLoop_outer hconf (S0 := abs L s (memoryBound input) fa sl) (vs0 := vs0) _
    { s with db := #[] } s.db s.assigned s.processed (ld s.db (L.reason + absC (ld s.db s.processed)) != 0)
    0 NONE fa sl rfl hB (Or.inl (by decide)) hflag
  have hp : propagate L s = propLoop L { s with db := #[] } s.db s.assigned s.processed
      (ld s.db (L.reason + absC (ld s.db s.processed)) != 0) 0 NONE := rfl
  rw [hp]
  rcases hres with h | h | ⟨hs, hB', fa', sl', db, vs, hset, hml, hrel⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr ⟨hs, hB', fa', sl', hml, ?_⟩)
    rcases hrel with ⟨hn, rfl, hlen, htr⟩ | hlt
    · refine Or.inl ⟨hn, hlen, db, vs, hset, ?_⟩
      obtain ⟨k, hk, hd, before⟩ := cursor0
      refine ⟨k, hk, hd, fun j hj hjk => ?_⟩
      obtain ⟨i, hi, he⟩ := before j hj hjk
      exact ⟨i, by omega, by rw [htr i hi]; exact he⟩
    · exact Or.inr ⟨hlt, db, vs, hset⟩

end MicrosatLean.Fast.Verification
