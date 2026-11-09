import MicrosatLean.Fast.Verification.AnalyzeResolve

/-!
# Minimization and unassignment in the fast `analyze` (C:115–128)

`fcollect` is the collect step of the fast minimization loop (C:117–118, with the fast
`implied`); `buildLoop_step` puts every iteration of `buildLoop` in one shape, so that
`buildLoop_spec` can call the faithful `vc_build` once per iteration. `unassignLoop_spec` is
the unassign loop (C:127–128, `UInv.step`).
-/

namespace MicrosatLean.Fast.Verification.AnalyzeAux

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- C:117–118 for the literal `x`: the arena and the size after collecting it. -/
def fcollect (L : Lay) (db : Array Cell) (size x : Cell) : Array Cell × Cell :=
  if ld db (L.fls + x) == MARK then
    if ld ((implied L db x).getD #[]) (L.fls + x) != IMPLIED then
      (st ((implied L db x).getD #[]) (L.buffer + size) x, size + 1)
    else ((implied L db x).getD #[], size)
  else (db, size)

/-- One iteration of `buildLoop` (C:117–121): collect, update the backjump point, reset the
flag. (`lbd` and `flag` only feed the moving averages.) -/
theorem buildLoop_step (L : Lay) (db : Array Cell) {forced p : Cell} (size lbd : Cell) (flag : Bool)
    (processed : Cell) (h : p ≥ forced) :
    ∃ lbd' flag', buildLoop L db forced p size lbd flag processed =
      buildLoop L (st (fcollect L db size (ld db p)).1 (L.fls + ld db p) 1) forced (p - 1)
        (fcollect L db size (ld db p)).2 lbd' flag'
        (if ((ld (fcollect L db size (ld db p)).1 (L.reason + absC (ld db p)) == 0) &&
          ((fcollect L db size (ld db p)).2 == 1)) = true then p else processed) := by
  rw [buildLoop.eq_1, ite_eq_left h]
  simp only [fcollect]
  by_cases h1 : (ld db (L.fls + ld db p) == MARK) = true
  · simp only [h1, ↓reduceIte]
    by_cases h2 : (ld ((implied L db (ld db p)).getD #[]) (L.fls + ld db p) != IMPLIED) = true
    · simp only [h2, ↓reduceIte]
      by_cases h3 : (ld (st ((implied L db (ld db p)).getD #[]) (L.buffer + size) (ld db p))
          (L.reason + absC (ld db p)) == 0) = true
      · simp only [h3, ↓reduceIte, Bool.true_and]; exact ⟨_, _, rfl⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte, Bool.false_and]; exact ⟨_, _, rfl⟩
    · simp only [h2, Bool.false_eq_true, ↓reduceIte]
      by_cases h3 : (ld ((implied L db (ld db p)).getD #[]) (L.reason + absC (ld db p)) == 0) = true
      · simp only [h3, ↓reduceIte, Bool.true_and]; exact ⟨_, _, rfl⟩
      · simp only [h3, Bool.false_eq_true, ↓reduceIte, Bool.false_and]; exact ⟨_, _, rfl⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    by_cases h3 : (ld db (L.reason + absC (ld db p)) == 0) = true
    · simp only [h3, ↓reduceIte, Bool.true_and]; exact ⟨_, _, rfl⟩
    · simp only [h3, Bool.false_eq_true, ↓reduceIte, Bool.false_and]; exact ⟨_, _, rfl⟩

section loops
variable {input : Input} {T : solver} {dbr : Records} {vs : List Int} {D : Nat} {L : Lay}

/-- C:116–122: the fast minimization loop keeps `BLoop` (from the state `Sb` at `build`), and
ends below `forced`. The faithful states are `AS` with `assigned = A`, `head = H`. -/
theorem buildLoop_spec (ctx : ACtx input T dbr vs D) (env : FEnv T L) {Sb : solver} (nc A H : Int)
    {forced : Cell} (hforced : forced.toInt = T.forced) :
    ∀ (k : Nat) (db : Array Cell) (p size lbd : Cell) (fg : Bool) (processed : Cell),
      (p.toInt + 1 - T.forced).toNat = k → db.size ≤ 2 ^ 31 →
      BLoop input T D Sb (AS T nc db A processed.toInt H) size.toInt p.toInt →
      ∃ pf, BLoop input T D Sb (AS T nc (buildLoop L db forced p size lbd fg processed).1 A
          (buildLoop L db forced p size lbd fg processed).2.2.2.toInt H)
          (buildLoop L db forced p size lbd fg processed).2.1.toInt pf ∧ pf < T.forced ∧
        (buildLoop L db forced p size lbd fg processed).1.size ≤ 2 ^ 31 := by
  have hn := ctx.num
  have hfls := env.ienv.fls; have hrs := env.ienv.reason; have hN := env.ienv.nVars; have hbuf := env.buffer
  have hone : ((1 : Cell)).toInt = 1 := rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro db p size lbd fg processed hk hsz hbl
  by_cases hp : p ≥ forced
  rotate_left
  · have hp' : p.toInt < T.forced := by
      have : ¬ forced.toInt ≤ p.toInt := fun h => hp (Int32.le_iff_toInt_le.mpr h)
      omega
    rw [buildLoop.eq_1, ite_eq_right hp]
    exact ⟨p.toInt, hbl, hp', hsz⟩
  have hp' : T.forced ≤ p.toInt := by rw [← hforced]; exact Int32.le_iff_toInt_le.mp hp
  obtain ⟨lbd', flag', e⟩ := buildLoop_step L db size lbd fg processed hp
  rw [e]
  have hbl0 := hbl
  obtain ⟨u, k', ps, hst, hb, hsz', hpk⟩ := hbl
  have hu : u < trailLen T := hst.2.2.2.1
  have hkge := hb.k_ge; have hkle := hb.k_le
  have hfp : (T.forced : Int) = T.falseStack + (forcedPos T : Nat) := by omega
  have hj1 : forcedPos T + 1 ≤ k' := by omega
  obtain ⟨j, rfl⟩ : ∃ j, k' = j + 1 := ⟨k' - 1, by omega⟩
  have hjt : j < trailLen T := by omega
  have hpj : p.toInt = T.falseStack + (j : Nat) := by push_cast at hpk; omega
  have hp1 : (p - 1).toInt = p.toInt - 1 := by rw [toInt_sub (by rw [hone]; omega) (by rw [hone]; omega), hone]
  have hm : ((p - 1).toInt + 1 - T.forced).toNat < k := by rw [hp1]; omega
  have hxl := ctx.lit hjt
  -- the size is at most the number of positions
  have hlen : ps.length ≤ u + 1 := by
    have hnd : ps.Nodup := hb.sorted.imp (fun hab => Nat.ne_of_gt hab)
    have hsub : ps ⊆ (List.range' 0 (u + 1)) := fun q hq => by
      have := hb.ps_mem q hq; rw [List.mem_range'_1]; omega
    have := hnd.length_le_of_subset hsub
    rwa [List.length_range'] at this
  have hP := AS_processed (T := T) (nc := nc) (db := db) (a := A) (p := processed.toInt) (h := H)
  generalize hPd : processed.toInt = P at hP hbl0 hb
  have hS : (AS T nc db A P H).ld p.toInt = trailAt T j := by rw [hpj]; exact hb.low.trail ctx hjt
  have hx : (ld db p).toInt = trailAt T j := by rw [← AS_ld (T := T) (nc := nc) (a := A) (p := P) (h := H) hsz rfl, hS]
  have hfx : (L.fls + ld db p).toInt = (AS T nc db A P H).false + (AS T nc db A P H).ld p.toInt := by
    rw [toInt_add (by omega) (by omega), hx, hS, ← hfls]; rfl
  have hflx := AS_ld (T := T) (nc := nc) (a := A) (p := P) (h := H) hsz hfx
  -- the collect step (C:117–118)
  obtain ⟨S', r, hcall, hpost, db', hfi, hDB', hsz'', hiff⟩ := fimplied_at (M := MarksAt T Sb u) ctx.core env.ienv
    ctx.dec j (AS T nc db A P H) db rfl hsz hb.low hjt hb.cache _ hx
  obtain ⟨DB', hS'⟩ := hpost.1
  have hS'e : S' = AS T nc db' A P H := by rw [hS']; rw [hS'] at hDB'; simp only at hDB'; rw [hDB']; rfl
  subst hS'e
  have himp : (MicrosatLean.Faithful.implied (AS T nc db A P H) ((AS T nc db A P H).ld p.toInt)).getD (default, 0) =
      (AS T nc db' A P H, r) := by rw [hS, hcall]; rfl
  have hS'p : (AS T nc db' A P H).ld p.toInt = trailAt T j := by
    rw [hpost.2.1 _ (by omega) (fun i hi _ => by
      have := ctx.lit (show i < trailLen T by omega); simp only [AS]; omega), hS]
  have hfx' : (L.fls + ld db p).toInt = (AS T nc db' A P H).false + trailAt T j := by
    rw [toInt_add (by omega) (by omega), hx, ← hfls]; rfl
  have hfl' : (ld db' (L.fls + ld db p)).toInt = flag (AS T nc db' A P H) (trailAt T j) :=
    (AS_ld (T := T) (nc := nc) (a := A) (p := P) (h := H) hsz'' hfx').symm
  have hcol : ∃ (db2 : Array Cell) (size2 : Cell), fcollect L db size (ld db p) = (db2, size2) ∧
      db2.size ≤ 2 ^ 31 ∧ (AS T nc db2 A P H).ld p.toInt = trailAt T j ∧ size2.toInt ≤ u + 1 ∧
      ((¬ (AS T nc db A P H).ld ((AS T nc db A P H).false + (AS T nc db A P H).ld p.toInt) = MicrosatLean.Faithful.MARK ∧
          AS T nc db2 A P H = AS T nc db A P H ∧ size2.toInt = size.toInt) ∨
        ((AS T nc db A P H).ld ((AS T nc db A P H).false + (AS T nc db A P H).ld p.toInt) = MicrosatLean.Faithful.MARK ∧
          ¬ ((MicrosatLean.Faithful.implied (AS T nc db A P H) ((AS T nc db A P H).ld p.toInt)).getD (default, 0)).2 = 0 ∧
          AS T nc db2 A P H = ((MicrosatLean.Faithful.implied (AS T nc db A P H) ((AS T nc db A P H).ld p.toInt)).getD (default, 0)).1 ∧
          size2.toInt = size.toInt) ∨
        ((AS T nc db A P H).ld ((AS T nc db A P H).false + (AS T nc db A P H).ld p.toInt) = MicrosatLean.Faithful.MARK ∧
          ((MicrosatLean.Faithful.implied (AS T nc db A P H) ((AS T nc db A P H).ld p.toInt)).getD (default, 0)).2 = 0 ∧
          AS T nc db2 A P H = ((MicrosatLean.Faithful.implied (AS T nc db A P H) ((AS T nc db A P H).ld p.toInt)).getD (default, 0)).1.st
            (((MicrosatLean.Faithful.implied (AS T nc db A P H) ((AS T nc db A P H).ld p.toInt)).getD (default, 0)).1.buffer + size.toInt)
            (((MicrosatLean.Faithful.implied (AS T nc db A P H) ((AS T nc db A P H).ld p.toInt)).getD (default, 0)).1.ld p.toInt) ∧
          size2.toInt = size.toInt + 1)) := by
    rw [himp]
    simp only
    unfold fcollect
    by_cases hm : (AS T nc db A P H).ld ((AS T nc db A P H).false + (AS T nc db A P H).ld p.toInt) = MicrosatLean.Faithful.MARK
    · have hm' : (ld db (L.fls + ld db p) == MARK) = true := beq_cell.mpr (by rw [← hflx, hm]; rfl)
      rw [ite_eq_left hm', hfi]
      simp only [Option.getD_some]
      by_cases h6 : flag (AS T nc db' A P H) (trailAt T j) = MicrosatLean.Faithful.IMPLIED
      · have h6' : ¬ ((ld db' (L.fls + ld db p) != IMPLIED) = true) := by
          simp only [bne_iff_ne, ne_eq, Decidable.not_not]; exact Int32.toInt_inj.mp (by rw [hfl', h6]; rfl)
        rw [ite_eq_right h6']
        exact ⟨_, _, rfl, hsz'', hS'p, by omega, Or.inr (Or.inl ⟨hm, fun h => (hiff.mpr h6) h, rfl, rfl⟩)⟩
      · have h6' : (ld db' (L.fls + ld db p) != IMPLIED) = true := by
          simp only [bne_iff_ne, ne_eq]; exact fun h => h6 (by rw [← hfl', h]; rfl)
        rw [ite_eq_left h6']
        have hr0 : r = 0 := Classical.byContradiction fun h => h6 (hiff.mp h)
        have hsize : size.toInt ≤ T.nVars := by
          have := hb.ps_mem; have := hn.2.1
          rcases Nat.lt_or_ge ps.length (u + 1) with h1 | h1 <;> omega
        have hbq : (L.buffer + size).toInt = (AS T nc db' A P H).buffer + size.toInt := by
          rw [toInt_add (by omega) (by omega), ← hbuf]; rfl
        obtain ⟨e2, s2⟩ := AS_st (T := T) (nc := nc) (a := A) (p := P) (h := H) hsz'' hbq
          (V := (AS T nc db' A P H).ld p.toInt) (by rw [hx, hS'p])
        have hs1 : (size + 1).toInt = size.toInt + 1 := by
          rw [toInt_add (by rw [hone]; omega) (by rw [hone]; omega), hone]
        refine ⟨_, _, rfl, s2, ?_, ?_, Or.inr (Or.inr ⟨hm, hr0, e2.symm, hs1⟩)⟩
        · rw [← e2, ld_st_of_ne _ _ (by simp only [AS]; omega) (by omega) (by simp only [AS]; omega), hS'p]
        · rw [hs1]
          -- one more literal than the collected positions, all distinct positions in `[j, u]`
          have hnot : j ∉ ps := fun hj => by have := hb.ps_mem j hj; omega
          have hnd : (j :: ps).Nodup := List.nodup_cons.mpr ⟨hnot, hb.sorted.imp (fun hab => Nat.ne_of_gt hab)⟩
          have hsub : (j :: ps) ⊆ (List.range' j (u + 1 - j)) := fun q hq => by
            rcases List.mem_cons.mp hq with rfl | hq
            · rw [List.mem_range'_1]; omega
            · have := hb.ps_mem q hq; rw [List.mem_range'_1]; omega
          have := hnd.length_le_of_subset hsub
          rw [List.length_range', List.length_cons] at this
          omega
    · have hm' : ¬ ((ld db (L.fls + ld db p) == MARK) = true) := fun h => hm (by rw [hflx, beq_cell.mp h]; rfl)
      rw [ite_eq_right hm']
      exact ⟨_, _, rfl, hsz, hS, by omega, Or.inl ⟨hm, rfl, rfl⟩⟩
  obtain ⟨db2, size2, hfc, hsz2, hS2p, hsize2, hA⟩ := hcol
  rw [hfc]
  simp only
  -- the backjump update (C:119–120)
  have hax : (absC (ld db p)).toInt = MicrosatLean.Faithful.abs (trailAt T j) := by rw [toInt_absC (by omega), hx]
  have hav : 1 ≤ MicrosatLean.Faithful.abs (trailAt T j) ∧ MicrosatLean.Faithful.abs (trailAt T j) ≤ T.nVars := by
    rcases abs_cases (trailAt T j) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hrq : (L.reason + absC (ld db p)).toInt = (AS T nc db2 A P H).reason +
      MicrosatLean.Faithful.abs ((AS T nc db2 A P H).ld p.toInt) := by
    rw [toInt_add (by rw [hax]; omega) (by rw [hax]; omega), hax, hS2p, ← hrs]; rfl
  have hrd2 := AS_ld (T := T) (nc := nc) (a := A) (p := P) (h := H) hsz2 hrq
  have hfx2 : (L.fls + ld db p).toInt = T.false + trailAt T j := by rw [toInt_add (by omega) (by omega), hx, hfls]
  have hpf : p.toInt ≥ (AS T nc db A P H).forced := hp'
  by_cases hd : (AS T nc db2 A P H).ld ((AS T nc db2 A P H).reason +
      MicrosatLean.Faithful.abs ((AS T nc db2 A P H).ld p.toInt)) = 0 ∧ size2.toInt = 1
  · have hc : ((ld db2 (L.reason + absC (ld db p)) == 0) && (size2 == 1)) = true := by
      rw [Bool.and_eq_true]
      exact ⟨beq_cell.mpr (by rw [← hrd2, hd.1]; rfl), beq_cell.mpr (by rw [hd.2]; rfl)⟩
    rw [ite_eq_left hc]
    obtain ⟨hbl', -⟩ := vc_build ctx hbl0 hpf hA (S3 := AS T nc db2 A p.toInt H) (Or.inl ⟨hd.1, hd.2, rfl⟩)
    have hS3p : (AS T nc db2 A p.toInt H).ld p.toInt = trailAt T j := by rw [AS_ld_congr A P H]; exact hS2p
    obtain ⟨e3, s3⟩ := AS_st (T := T) (nc := nc) (a := A) (p := p.toInt) (h := H) hsz2 (v := 1) (V := 1) hfx2 rfl
    rw [hS3p, show (AS T nc db2 A p.toInt H).false = T.false from rfl, e3, ← hp1] at hbl'
    exact ih _ hm _ (p - 1) size2 lbd' flag' p rfl s3 hbl'
  · have hc : ¬ (((ld db2 (L.reason + absC (ld db p)) == 0) && (size2 == 1)) = true) := by
      rw [Bool.and_eq_true]
      exact fun ⟨h1, h2⟩ => hd ⟨by rw [hrd2, beq_cell.mp h1]; rfl, by rw [beq_cell.mp h2]; rfl⟩
    rw [ite_eq_right hc]
    obtain ⟨hbl', -⟩ := vc_build ctx hbl0 hpf hA (S3 := AS T nc db2 A P H) (Or.inr ⟨hd, rfl⟩)
    obtain ⟨e3, s3⟩ := AS_st (T := T) (nc := nc) (a := A) (p := P) (h := H) hsz2 (v := 1) (V := 1) hfx2 rfl
    rw [hS2p, show (AS T nc db2 A P H).false = T.false from rfl, e3, ← hp1, ← hPd] at hbl'
    exact ih _ hm _ (p - 1) size2 lbd' flag' processed rfl s3 hbl'

/-- C:127–128: the fast unassign loop, from a state where `UInv` holds, unassigns down to
`processed`. The result is the faithful loop's final state `S0` followed by its last
unassignment (C:128). -/
theorem unassignLoop_spec (ctx : ACtx input T dbr vs D) (env : FEnv T L) {Se : solver} (hl : SameLow T Se)
    (hu : Se.assigned - T.falseStack < trailLen T) (hpr : T.falseStack ≤ Se.processed)
    (nc H : Int) {processed : Cell} (hP : Se.processed = processed.toInt) :
    ∀ (k : Nat) (db : Array Cell) (assigned : Cell), (assigned.toInt - processed.toInt).toNat = k →
      db.size ≤ 2 ^ 31 → UInv T Se (AS T nc db assigned.toInt processed.toInt H) →
      ∃ S0, UInv T Se S0 ∧ S0.assigned ≤ S0.processed ∧
        MicrosatLean.Faithful.unassign S0 (S0.ld S0.assigned) =
          AS T nc (unassignLoop L db assigned processed) processed.toInt processed.toInt H ∧
        (unassignLoop L db assigned processed).size ≤ 2 ^ 31 := by
  have hn := ctx.num
  have hfls := env.ienv.fls; have hN := env.ienv.nVars
  have hone : ((1 : Cell)).toInt = 1 := rfl
  have hs := hl.shape
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro db assigned hk hsz hU
  obtain ⟨a, -, hP0, -, hA, hpa, haA, hcells, -⟩ := id hU
  simp only [AS_assigned, AS_processed] at hA hP0
  have hppe : (processedPos Se : Int) = processed.toInt - T.falseStack := by
    simp only [processedPos]; have := hs.falseStack; omega
  have hat : a < trailLen T := by omega
  have hxl := ctx.lit hat
  have htr : (AS T nc db assigned.toInt processed.toInt H).ld assigned.toInt = trailAt T a := by
    rw [congrArg (AS T nc db assigned.toInt processed.toInt H).ld hA, hcells _ (by omega) (fun i h1 h2 => by
      have := ctx.lit (show i < trailLen T by omega); rw [hs.false]; omega)]
    exact hl.trail ctx hat
  have hx : (ld db assigned).toInt = trailAt T a := by rw [← AS_ld hsz rfl, htr]
  have hfx : (L.fls + ld db assigned).toInt = T.false + trailAt T a := by
    rw [toInt_add (by omega) (by omega), hx, hfls]
  obtain ⟨e, s1⟩ := AS_st (T := T) (nc := nc) (a := assigned.toInt) (p := processed.toInt) (h := H) hsz hfx
    (v := 0) (V := 0) rfl
  have hun : MicrosatLean.Faithful.unassign (AS T nc db assigned.toInt processed.toInt H)
      ((AS T nc db assigned.toInt processed.toInt H).ld (AS T nc db assigned.toInt processed.toInt H).assigned) =
      AS T nc (st db (L.fls + ld db assigned) 0) assigned.toInt processed.toInt H := by
    rw [unassign_eq, AS_assigned, htr]; exact e
  rw [unassignLoop.eq_1]
  by_cases hgt : assigned > processed
  · rw [ite_eq_left hgt]
    have hgt' : (AS T nc db assigned.toInt processed.toInt H).assigned > (AS T nc db assigned.toInt processed.toInt H).processed :=
      Int32.lt_iff_toInt_lt.mp hgt
    have ha1 : (assigned - 1).toInt = assigned.toInt - 1 := by
      have := Int32.lt_iff_toInt_lt.mp hgt
      rw [toInt_sub (by rw [hone]; omega) (by rw [hone]; omega), hone]
    obtain ⟨hU', -⟩ := UInv.step ctx hl hu hpr hU hgt'
    rw [hun] at hU'
    have hlt := Int32.lt_iff_toInt_lt.mp hgt
    exact ih _ (by rw [ha1]; omega) _ (assigned - 1) rfl s1 (by rw [ha1]; exact hU')
  · rw [ite_eq_right hgt]
    have hle : assigned.toInt ≤ processed.toInt := Int.not_lt.mp fun h => hgt (Int32.lt_iff_toInt_lt.mpr h)
    have heq : assigned.toInt = processed.toInt := by omega
    rw [heq] at hun hU
    exact ⟨_, hU, by simp only [AS_assigned, AS_processed]; omega, hun, s1⟩

/-- C:103–129 for the fast port: from a conflict below the last decision `D` (the faithful
`analyzeCore_main`'s hypotheses), the fast loops of `analyze` up to its final `addClause`
leave a state that meets the faithful `Analyzed` contract. `t` holds the fast fields of the
conflict state `T`; `nc` is the new conflict count. -/
theorem analyze_core_fast (ctx : ACtx input T dbr vs D) (env : FEnv T L) {P : Nat} {r : Record}
    (hr : r ∈ dbr.all) (hfalse : ∀ l ∈ r.2, ∃ j < trailLen T, trailAt T j = l)
    (hmark : ∃ j, D ≤ j ∧ j < trailLen T ∧ trailAt T j ∈ r.2) (hDP : D ≤ P)
    (hwatched : ∀ s ∈ dbr.all, 2 ≤ s.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
      ∀ p < P, FalseAt T s.2[w]! p → ∃ q, FalseAt T (- s.2[o]!) q ∧ SameOrLowerLevel T p q)
    {db0 : Array Cell} {head0 assigned0 forced0 : Cell} (hDB : T.DB = toDB db0) (hsz : db0.size ≤ 2 ^ 31)
    (hA : T.assigned = assigned0.toInt) (hH : T.head = head0.toInt) (hF : T.forced = forced0.toInt)
    {c : Cell} (hc : c.toInt = r.1) (nc : Int) :
    ∃ Ls vs' B, Analyzed input T dbr
      (AS T nc (st (unassignLoop L
          (buildLoop L (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).1 forced0
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2 0 0 false
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2).1
          (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2
          (buildLoop L (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).1 forced0
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2 0 0 false
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2).2.2.2)
          (L.buffer + (buildLoop L (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).1 forced0
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2 0 0 false
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2).2.1) 0)
        (buildLoop L (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).1 forced0
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2 0 0 false
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2).2.2.2.toInt
        (buildLoop L (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).1 forced0
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2 0 0 false
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2).2.2.2.toInt
        (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.1.toInt)
      (buildLoop L (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).1 forced0
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2 0 0 false
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2).2.1.toInt Ls vs' B ∧
      B ≤ D ∧
      (st (unassignLoop L
          (buildLoop L (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).1 forced0
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2 0 0 false
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2).1
          (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2
          (buildLoop L (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).1 forced0
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2 0 0 false
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2).2.2.2)
          (L.buffer + (buildLoop L (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).1 forced0
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2 0 0 false
            (resolveLoop L (bumpLoop L db0 head0 c).1 (bumpLoop L db0 head0 c).2 assigned0).2.2).2.1) 0).size ≤ 2 ^ 31 := by
  have hn := ctx.num
  have hN := env.ienv.nVars; have hbuf := env.buffer
  -- C:104
  obtain ⟨hres, hsz1⟩ := bumpConf_spec ctx env hr hfalse hmark nc hc hDB hsz hH (L := L)
  rw [hA] at hres
  generalize bumpLoop L db0 head0 c = R1 at hres hsz1 ⊢
  -- C:105–113
  obtain ⟨⟨u, hst⟩, hsz2⟩ := resolveLoop_spec ctx env nc T.processed _ R1.1 R1.2 assigned0 _ rfl hsz1 hres
  generalize resolveLoop L R1.1 R1.2 assigned0 = R2 at hst hsz2 ⊢
  -- C:115–122
  have hbl : BLoop input T D (AS T nc R2.1 R2.2.2.toInt T.processed R2.2.1.toInt)
      (AS T nc R2.1 R2.2.2.toInt R2.2.2.toInt R2.2.1.toInt) (0 : Cell).toInt R2.2.2.toInt :=
    ⟨u, u + 1, [], hst, BState.init ctx hst, rfl, by have := hst.2.1; simp only [AS_assigned] at this; omega⟩
  obtain ⟨pf, hbl', hpf, hsz3⟩ := buildLoop_spec ctx env nc R2.2.2.toInt R2.2.1.toInt hF.symm _ R2.1 R2.2.2 0 0 false
    R2.2.2 rfl hsz2 hbl
  generalize buildLoop L R2.1 forced0 R2.2.2 0 0 false R2.2.2 = R3 at hbl' hsz3 ⊢
  -- C:124–128
  obtain ⟨u', ps, -, hb', hsize, hfe, hle, hAe, hue, hpre, hppe⟩ := BLoop.exit ctx ⟨hbl', hpf⟩ id
    (SameShape.refl _) (fun _ => rfl) rfl rfl
  have hU0 := UInv.init hfe hAe (by rw [hppe]; exact hb'.B_le)
  obtain ⟨S0, hU, hle0, hun, hsz4⟩ := unassignLoop_spec ctx env hle hue hpre nc R2.2.1.toInt (processed := R3.2.2.2)
    rfl _ R3.1 R2.2.2 rfl hsz3 hU0
  -- C:129
  obtain ⟨Ls, vs', B, han, hBD⟩ := analyzed_final ctx hDP hwatched ⟨hbl', hpf⟩ id (SameShape.refl _) (fun _ => rfl)
    rfl rfl rfl ⟨hU, hle0⟩
  rw [hun] at han
  have hps : ps.length ≤ trailLen T := by
    have hnd : ps.Nodup := hb'.sorted.imp (fun hab => Nat.ne_of_gt hab)
    have hsub : ps ⊆ (List.range' 0 (trailLen T)) := fun q hq => by
      have := hb'.ps_mem q hq; have := hst.2.2.2.1; rw [List.mem_range'_1]; omega
    have := hnd.length_le_of_subset hsub
    rwa [List.length_range'] at this
  have hbq : (L.buffer + R3.2.1).toInt = (AS T nc (unassignLoop L R3.1 R2.2.2 R3.2.2.2) R3.2.2.2.toInt R3.2.2.2.toInt
      R2.2.1.toInt).buffer + R3.2.1.toInt := by
    rw [toInt_add (by omega) (by omega), ← hbuf]; rfl
  obtain ⟨e, s5⟩ := AS_st (T := T) (nc := nc) (a := R3.2.2.2.toInt) (p := R3.2.2.2.toInt) (h := R2.2.1.toInt)
    hsz4 hbq (v := 0) (V := 0) rfl
  rw [e] at han
  exact ⟨Ls, vs', B, han, hBD, s5⟩

end loops

end MicrosatLean.Fast.Verification.AnalyzeAux
