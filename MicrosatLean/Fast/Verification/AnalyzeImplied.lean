import MicrosatLean.Fast.Verification.AnalyzeBump

/-!
# `implied` of the fast port (C:93–100)

The fast `implied` returns only the arena; its answer is the flag of the literal afterwards
(`IMPLIED` means implied). The faithful `implied` returns `(S', r)`. `fimplied_spec` is the
faithful `implied_spec`, extended: from a state that stands for `db`, the fast `implied`
returns an arena that stands for `S'`, and `r ≠ 0` exactly when the flag of the literal in
`S'` is `IMPLIED`. The proof follows `impliedLoop_post` and `implied_at`.
-/

namespace MicrosatLean.Fast.Verification.AnalyzeAux

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

section implied
variable {input : Input} {T : solver} {db : Records} {vs : List Int} {M : Nat → Prop} {D : Nat} {L : Lay}

/-- The fast part of `implied`'s contract: the fast result stands for the faithful `S'`, and the
faithful answer is the flag of the literal. -/
def FastRes (S' : solver) (r : Int) (lit : Int) (res : Option (Array Cell)) : Prop :=
  ∃ db', res = some db' ∧ S'.DB = toDB db' ∧ db'.size ≤ 2 ^ 31 ∧
    (r ≠ 0 ↔ flag S' lit = MicrosatLean.Faithful.IMPLIED)

/-- `implied` at trail position `i`, faithful and fast, for every state (the induction
hypothesis). -/
def FImpliedAt (input : Input) (T : solver) (M : Nat → Prop) (D i : Nat) (L : Lay) : Prop :=
  ∀ S (dbf : Array Cell), S.DB = toDB dbf → dbf.size ≤ 2 ^ 31 → SameLow T S → i < trailLen T →
    Cache input T S M (i + 1) → ∀ x : Cell, x.toInt = trailAt T i →
    ∃ S' r, MicrosatLean.Faithful.implied S (trailAt T i) = some (S', r) ∧ ImpliedPost input T M D S i S' r ∧
      FastRes S' r (trailAt T i) (implied L dbf x)

/-- The numbers the fast reads of `implied` need. -/
structure IEnv (T : solver) (L : Lay) : Prop where
  fls : T.false = L.fls.toInt
  reason : T.reason = L.reason.toInt
  nVars : 10 * T.nVars + 7 ≤ 2 ^ 30
  mem : T.mem_used ≤ 2 ^ 30

/-- The fast loop of `implied` (C:97–100) over the reason of position `i`, from its literal `k`:
`impliedLoop_post` with the fast loop alongside. -/
theorem fimpliedLoop_post (core : Core input T db vs) (env : IEnv T L) {i : Nat}
    (ih : ∀ j < i, FImpliedAt input T M D j L) {S : solver} (hi : i < trailLen T)
    (hc : Cache input T S M (i + 1)) (hroot : ¬ RootLevel T i) {x : Cell} (hx : x.toInt = trailAt T i)
    {r : Record} (hr : r ∈ db.all) (h0 : r.2[0]? = some (-trailAt T i))
    (hfalse : ∀ l ∈ r.2.drop 1, ∃ j < i, FalseAt T l j) {m0 j0 : Nat} (hm0 : 1 ≤ m0)
    (hlj0 : r.2[m0]? = some (trailAt T j0)) (hj0 : j0 < i) (hDj0 : D ≤ i → D ≤ j0) (t : Nat) :
    ∀ k Sk (dbk : Array Cell) (pk : Cell), k + 1 + t = r.2.length → pk.toInt = r.1 + k →
      Sk.DB = toDB dbk → dbk.size ≤ 2 ^ 31 → SameLow T Sk → (∃ DB, Sk = ({ S with DB := DB } : solver)) →
      (∀ q, 0 ≤ q → (∀ j < i, ¬ RootLevel T j → q ≠ S.false + trailAt T j) → Sk.ld q = S.ld q) →
      (∀ K, Cache input T S M K → Cache input T Sk M K) →
      (∀ j < i, flag S (trailAt T j) = MicrosatLean.Faithful.MARK → flag Sk (trailAt T j) = MicrosatLean.Faithful.MARK) →
      (∀ m l, 1 ≤ m → m ≤ k → r.2[m]? = some l → GoodBelow input T M i l) →
      (∀ E ≤ trailLen T, NoImp T S D E → NoImp T Sk D E) →
      (D ≤ i → NoImp T S D i → k < m0) →
      ∃ S' res, MicrosatLean.Faithful.impliedLoop Sk (trailAt T i) (r.1 + k) = some (S', res) ∧
        ImpliedPost input T M D S i S' res ∧ FastRes S' res (trailAt T i) (impliedLoop L dbk x pk) := by
  have hcl := core.record_clauseAt hr
  have hge := core.database.record_ge hr
  have hm0L : m0 < r.2.length := (List.getElem?_eq_some_iff.mp hlj0).1
  have hj0L : j0 < trailLen T := by omega
  have hn := core.layout.nVars_pos
  have hnum := core.layout.num
  have hN := env.nVars
  have hmu := env.mem
  have hfls := env.fls
  have hone : ((1 : Cell)).toInt = 1 := rfl
  have hxl := inRange_iff.mp (core.trail.lit i hi)
  simp only [clausesAt] at hge
  induction t with
  | zero =>
    intro k Sk dbk pk hk hpk hDBk hszk hSk hdb hfr hca hmk hgood hni hsame
    have hread : Sk.ld (r.1 + k + 1) = 0 := by
      rw [hSk.high _ (by omega), show r.1 + (k : Int) + 1 = r.1 + (r.2.length : Int) by omega]
      exact hcl.2
    have himp : Imp input T M i := Imp.of_reason core hr hi h0 fun m l h1 hl =>
      hgood m l h1 (by have := (List.getElem?_eq_some_iff.mp hl).1; omega) hl
    have hp1 : (pk + 1).toInt = r.1 + k + 1 := by rw [toInt_add (by rw [hone]; omega) (by rw [hone]; omega), hone, hpk]
    have hfread : (ld dbk (pk + 1)).toInt = 0 := by rw [← ld_toDB hDBk hszk hp1, hread]
    have hfx : (L.fls + x).toInt = Sk.false + trailAt T i := by
      rw [toInt_add (by omega) (by omega), hx, hSk.shape.false, env.fls]
    obtain ⟨e, sz⟩ := st_toDB hDBk hszk hfx implied_toInt
    rw [MicrosatLean.Faithful.impliedLoop.eq_1, hread, ite_eq_left (by decide)]
    refine ⟨_, _, rfl, ImpliedPost.write core hSk hi hroot hdb hfr hca hmk hni
      (Or.inr ⟨rfl, himp, fun ⟨h1, h2⟩ => by have := hsame h1 h2; omega⟩) (fun _ => himp)
      (fun h1 h2 => by have := hsame h1 h2; omega), ?_⟩
    have hz : (ld dbk (pk + 1) == 0) = true := beq_cell.mpr hfread
    rw [MicrosatLean.Fast.impliedLoop.eq_1, ite_eq_left hz]
    refine ⟨_, rfl, by rw [e], sz, ?_⟩
    rw [flag_after_st _ _ _ (by rw [hSk.shape.false]; omega), ite_eq_left rfl]
    decide
  | succ t iht =>
    intro k Sk dbk pk hk hpk hDBk hszk hSk hdb hfr hca hmk hgood hni hsame
    have hk1 : k + 1 < r.2.length := by omega
    have hget : r.2[k + 1]? = some r.2[k + 1] := List.getElem?_eq_getElem hk1
    obtain ⟨j, hj, hjL, hjl⟩ := hfalse r.2[k + 1]
      (List.mem_iff_getElem?.mpr ⟨k, by rw [List.getElem?_drop, Nat.add_comm]; exact hget⟩)
    rw [← hjl] at hget
    have hread : Sk.ld (r.1 + k + 1) = trailAt T j := by
      rw [hSk.high _ (by omega), show r.1 + (k : Int) + 1 = r.1 + ((k + 1 : Nat) : Int) by omega,
        hcl.1 _ hk1, hjl]
    have hl0 : trailAt T j ≠ 0 := (inRange_iff.mp (core.trail.lit j hjL)).1
    have hjr := inRange_iff.mp (core.trail.lit j hjL)
    have hptr : r.1 + (k : Int) + 1 = r.1 + ((k + 1 : Nat) : Int) := by omega
    have hcj := hca _ hc
    have hp1 : (pk + 1).toInt = r.1 + k + 1 := by rw [toInt_add (by rw [hone]; omega) (by rw [hone]; omega), hone, hpk]
    have hp1' : (pk + 1).toInt = r.1 + ((k + 1 : Nat) : Int) := by rw [hp1]; omega
    have hxj : (ld dbk (pk + 1)).toInt = trailAt T j := by rw [← ld_toDB hDBk hszk hp1, hread]
    have hfxj : (L.fls + ld dbk (pk + 1)).toInt = Sk.false + trailAt T j := by
      rw [toInt_add (by omega) (by omega), hxj, hSk.shape.false, env.fls]
    have hflj : (ld dbk (L.fls + ld dbk (pk + 1))).toInt = flag Sk (trailAt T j) := by
      rw [← ld_toDB hDBk hszk hfxj]; rfl
    rw [MicrosatLean.Faithful.impliedLoop.eq_1, hread, ite_eq_right (by simpa using hl0),
      show Sk.ld (Sk.false + trailAt T j) = flag Sk (trailAt T j) from rfl]
    have hz : ¬ ((ld dbk (pk + 1) == 0) = true) := fun h => hl0 (by rw [← hxj, beq_cell.mp h]; rfl)
    rw [MicrosatLean.Fast.impliedLoop.eq_1, ite_eq_right hz]
    by_cases hm : flag Sk (trailAt T j) = MicrosatLean.Faithful.MARK
    · rw [hm, ite_eq_right (by decide), hptr]
      have hfm : ¬ ((ld dbk (L.fls + ld dbk (pk + 1)) != MARK) = true) := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact Int32.toInt_inj.mp (by rw [hflj, hm]; rfl)
      rw [ite_eq_right hfm]
      have hM : M j := by
        by_cases hrj : RootLevel T j
        · have h6 := (hcj j (by omega)).1 hrj
          rw [hm] at h6; exact absurd h6 (by decide)
        · rcases (hcj j (by omega)).2 hrj with h | ⟨-, h⟩ | h | ⟨h, -⟩
          · rw [hm] at h; exact absurd h (by decide)
          · exact h
          · rw [hm] at h; exact absurd h (by decide)
          · rw [hm] at h; exact absurd h (by decide)
      refine iht (k + 1) Sk dbk (pk + 1) (by omega) hp1' hDBk hszk hSk hdb hfr hca hmk
        (GoodBelow.succ hgood hget fun _ _ hM' => hM' j hj hM) hni ?_
      intro h1 h2
      have := hsame h1 h2
      refine Nat.lt_of_le_of_ne (by omega) fun he => ?_
      rw [← he, hget] at hlj0
      have hjj := core.trailAt_inj hjL hj0L (Option.some.inj hlj0)
      subst hjj
      exact ((hni i (Nat.le_of_lt hi) h2) j (hDj0 h1) hj).1 hm
    · rw [ite_eq_left (xor_mark_ne_zero (Cache.vals hcj (j := j) (by omega)) hm)]
      have hfm : (ld dbk (L.fls + ld dbk (pk + 1)) != MARK) = true := by
        simp only [bne_iff_ne, ne_eq]; exact fun h => hm (by rw [← hflj, h]; rfl)
      rw [ite_eq_left hfm]
      obtain ⟨S1, r1, hcall, hpost, db1, hf1, hDB1, hsz1, hr1iff⟩ :=
        ih j hj Sk dbk hDBk hszk hSk hjL (Cache.mono hcj (by omega)) _ hxj
      rw [hcall, hf1]
      simp only [bind, Option.bind]
      obtain ⟨hS1, hdb1, hfr1, hca1, hmk1, hni1⟩ :=
        ImpliedPost.step core hSk hj hi hdb hfr hca hmk hni hm hpost
      have hS1f : S1.false = Sk.false := by obtain ⟨DB1, rfl⟩ := hpost.1; rfl
      have hfl1 : (ld db1 (L.fls + ld dbk (pk + 1))).toInt = flag S1 (trailAt T j) := by
        rw [← ld_toDB hDB1 hsz1 (Q := S1.false + trailAt T j) (by rw [hfxj, hS1f])]; rfl
      have hfx : (L.fls + x).toInt = S1.false + trailAt T i := by
        rw [toInt_add (by omega) (by omega), hx, hS1f, hSk.shape.false, env.fls]
      by_cases hr1 : r1 = 0
      · rw [ite_eq_left (by simp [hr1])]
        have hne6 : flag S1 (trailAt T j) ≠ MicrosatLean.Faithful.IMPLIED := fun h => hr1iff.mpr h hr1
        have hfi : (ld db1 (L.fls + ld dbk (pk + 1)) != IMPLIED) = true := by
          simp only [bne_iff_ne, ne_eq]; exact fun h => hne6 (by rw [← hfl1, h]; rfl)
        rw [ite_eq_left hfi]
        obtain ⟨e, sz⟩ := st_toDB hDB1 hsz1 hfx (v := 5) (V := MicrosatLean.Faithful.IMPLIED - 1) rfl
        refine ⟨_, _, rfl, ImpliedPost.write core hS1 hi hroot hdb1 hfr1 hca1 hmk1 hni1 (Or.inl rfl)
          (fun h => absurd rfl h) (fun _ _ => rfl), _, rfl, by rw [e], sz, ?_⟩
        rw [flag_after_st _ _ _ (by rw [hS1f, hSk.shape.false]; omega), ite_eq_left rfl]
        decide
      · rw [ite_eq_right (by simpa using hr1), hptr]
        have h6 : flag S1 (trailAt T j) = MicrosatLean.Faithful.IMPLIED := hr1iff.mp hr1
        have hfi : ¬ ((ld db1 (L.fls + ld dbk (pk + 1)) != IMPLIED) = true) := by
          simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact Int32.toInt_inj.mp (by rw [hfl1, h6]; rfl)
        rw [ite_eq_right hfi]
        refine iht (k + 1) S1 db1 (pk + 1) (by omega) hp1' hDB1 hsz1 hS1 hdb1 hfr1 hca1 hmk1
          (GoodBelow.succ hgood hget fun a ha hM =>
            hpost.2.2.2.2.1 hr1 a ha fun j' hj' => hM j' (by omega)) hni1 ?_
        intro h1 h2
        have := hsame h1 h2
        refine Nat.lt_of_le_of_ne (by omega) fun he => ?_
        rw [← he, hget] at hlj0
        have hjj := core.trailAt_inj hjL hj0L (Option.some.inj hlj0)
        subst hjj
        have hN := hni i (Nat.le_of_lt hi) h2
        exact hr1 (hpost.2.2.2.2.2.2 (hDj0 h1) (hN.mono (Nat.le_of_lt hj)) (hN j (hDj0 h1) hj).2)

/-- `implied_at` with the fast `implied` alongside, by strong induction on the position. -/
theorem fimplied_at (core : Core input T db vs) (env : IEnv T L) (hD : IsDecision T D) (i : Nat) :
    FImpliedAt input T M D i L := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro S dbf hDB hsz hS hi hc x hx
  have hci := hc i (by omega)
  have hn := core.layout.nVars_pos
  have hnum := core.layout.num
  have hN := env.nVars; have hmu := env.mem; have hfls := env.fls; have hrs := env.reason
  have hxl := inRange_iff.mp (core.trail.lit i hi)
  have hav : 1 ≤ MicrosatLean.Faithful.abs (trailAt T i) ∧ MicrosatLean.Faithful.abs (trailAt T i) ≤ T.nVars := by
    rcases abs_cases (trailAt T i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hfx : (L.fls + x).toInt = S.false + trailAt T i := by
    rw [toInt_add (by omega) (by omega), hx, hS.shape.false, hfls]
  have hflx : (ld dbf (L.fls + x)).toInt = flag S (trailAt T i) := by rw [← ld_toDB hDB hsz hfx]; rfl
  have hax : (absC x).toInt = MicrosatLean.Faithful.abs (trailAt T i) := by rw [toInt_absC (by omega), hx]
  have hrx : (L.reason + absC x).toInt = S.reason + MicrosatLean.Faithful.abs (trailAt T i) := by
    rw [toInt_add (by omega) (by omega), hax, hS.shape.reason, hrs]
  have hrdx := ld_toDB hDB hsz hrx
  rw [MicrosatLean.Faithful.implied.eq_1, show S.ld (S.false + trailAt T i) = flag S (trailAt T i) from rfl,
    MicrosatLean.Fast.implied.eq_1]
  by_cases hgt : flag S (trailAt T i) > MicrosatLean.Faithful.MARK
  · have hgt' : ld dbf (L.fls + x) > MARK := Int32.lt_iff_toInt_lt.mpr (by rw [hflx]; exact hgt)
    rw [ite_eq_left hgt, ite_eq_left hgt']
    refine ⟨S, _, rfl, ⟨⟨S.DB, rfl⟩, fun _ _ _ => rfl, fun _ h => h, fun _ _ h _ => h, ?_,
      fun _ _ h => h, ?_⟩, dbf, rfl, hDB, hsz, ?_⟩
    · intro hne
      by_cases hroot : RootLevel T i
      · exact Imp.of_root core hi hroot
      · rcases hci.2 hroot with h | ⟨h, -⟩ | h | ⟨-, h⟩
        · rw [h] at hgt; exact absurd hgt (by decide)
        · rw [h] at hgt; exact absurd hgt (by decide)
        · rw [h] at hne; exact absurd hne (by decide)
        · exact h
    · intro hDi _ h6
      rcases hci.2 (fun h => h D hDi hD) with h | ⟨h, -⟩ | h | ⟨h, -⟩
      · rw [h] at hgt; exact absurd hgt (by decide)
      · rw [h] at hgt; exact absurd hgt (by decide)
      · rw [h]; decide
      · exact absurd h h6
    · by_cases hroot : RootLevel T i
      · rw [hci.1 hroot]; decide
      · rcases hci.2 hroot with h | ⟨h, -⟩ | h | ⟨h, -⟩
        · rw [h] at hgt; exact absurd hgt (by decide)
        · rw [h] at hgt; exact absurd hgt (by decide)
        · rw [h]; decide
        · rw [h]; decide
  · have hgt' : ¬ (ld dbf (L.fls + x) > MARK) := fun h => hgt (by
      have := Int32.lt_iff_toInt_lt.mp h; rw [hflx] at this; exact this)
    rw [ite_eq_right hgt, ite_eq_right hgt']
    have hroot : ¬ RootLevel T i := fun h => hgt (by rw [hci.1 h]; decide)
    have hle2 : flag S (trailAt T i) ≠ MicrosatLean.Faithful.IMPLIED := fun h => hgt (by rw [h]; decide)
    by_cases hz : (S.ld (S.reason + MicrosatLean.Faithful.abs (trailAt T i)) == 0) = true
    · have hz' : (ld dbf (L.reason + absC x) == 0) = true := beq_cell.mpr (by rw [← hrdx]; simpa using hz)
      rw [ite_eq_left hz, ite_eq_left hz']
      exact ⟨S, 0, rfl, ⟨⟨S.DB, rfl⟩, fun _ _ _ => rfl, fun _ h => h, fun _ _ h _ => h,
        fun h => absurd rfl h, fun _ _ h => h, fun _ _ _ => rfl⟩, dbf, rfl, hDB, hsz,
        ⟨fun h => absurd rfl h, fun h => absurd h hle2⟩⟩
    · have hz' : ¬ ((ld dbf (L.reason + absC x) == 0) = true) := fun h => hz (by
        have := beq_cell.mp h; rw [← hrdx] at this; simpa using this)
      rw [ite_eq_right hz, ite_eq_right hz']
      obtain ⟨-, -, -, -, hre, -, -, -⟩ := core.layout.num
      have hreason : reasonOf T (trailAt T i) = S.ld (S.reason + MicrosatLean.Faithful.abs (trailAt T i)) := by
        unfold reasonOf
        rw [hS.shape.reason, hS.mid _ (by omega) (by omega)]
      have hne : reasonOf T (trailAt T i) ≠ 0 := by rw [hreason]; simpa using hz
      have hforced : forcedPos T ≤ i :=
        Nat.le_of_not_lt fun h => hroot (core.trail.forced_root i h)
      obtain ⟨r, hr, hre1, h0, hfalse, hsl⟩ := core.reasons i hi hforced hne
      obtain ⟨l0, hl0, j0, hj0, hF0, hlev⟩ := hsl hroot
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hl0
      rw [List.getElem?_drop] at hm
      have hge := core.database.record_ge hr
      simp only [clausesAt] at hge
      have hL : 0 + 1 + (r.2.length - 1) = r.2.length := by
        have := (List.getElem?_eq_some_iff.mp h0).1; omega
      have hone : ((1 : Cell)).toInt = 1 := rfl
      have hpk : (ld dbf (L.reason + absC x) - 1).toInt = r.1 + ((0 : Nat) : Int) := by
        rw [toInt_sub (by rw [hone, ← hrdx, ← hreason, hre1]; omega) (by rw [hone, ← hrdx, ← hreason, hre1]; omega),
          hone, ← hrdx, ← hreason, hre1]; omega
      rw [show S.ld (S.reason + MicrosatLean.Faithful.abs (trailAt T i)) - 1 = r.1 + ((0 : Nat) : Int) by
        rw [← hreason, hre1]; omega]
      exact fimpliedLoop_post core env ih hi hc hroot hx hr h0 hfalse (m0 := 1 + m) (by omega)
        (by rw [hm, hF0.2]) hj0 (fun hDi => Nat.le_of_not_lt fun h => hlev D h hDi hD) _ 0 S dbf _ hL hpk
        hDB hsz hS ⟨S.DB, rfl⟩ (fun _ _ _ => rfl) (fun _ h => h) (fun _ _ h => h)
        (fun _ _ h1 h2 _ => absurd h2 (by omega)) (fun _ _ h => h) (fun _ _ => by omega)

end implied

end MicrosatLean.Fast.Verification.AnalyzeAux
