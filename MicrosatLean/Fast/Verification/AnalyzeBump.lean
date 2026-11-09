import MicrosatLean.Fast.Verification.Inv

/-!
# `bump` in the fast `analyze` (C:85–91, C:104, C:111–112)

The fast `bumpLoop` inlines the faithful `bump`. `fbump` is one of its iterations;
`bump_sim` shows that it writes what the faithful `bump` writes (given the decision order,
which bounds the `next`/`prev` cells it reads). `bumpLoop_spec` turns any invariant that the
faithful `bump` keeps (`BumpInv`, `RBump`) into a fact about the fast loop.
-/

namespace MicrosatLean.Fast.Verification.AnalyzeAux

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-! ### Writing and reading a state that stands for a fast arena -/

/-- A write to a state whose memory is `toDB db` is the fast write. -/
theorem st_toDB {S : solver} {db : Array Cell} (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31)
    {p v : Cell} {P V : Int} (hp : p.toInt = P) (hv : v.toInt = V) :
    S.st P V = { S with DB := toDB (st db p v) } ∧ (st db p v).size ≤ 2 ^ 31 := by
  subst hp hv
  obtain ⟨e, hs⟩ := st_sim S hDB hsz p v
  obtain ⟨DB', h⟩ := st_eq S p.toInt v.toInt
  refine ⟨?_, hs⟩
  rw [h] at e ⊢
  change DB' = _ at e
  rw [e]

/-- A read of a state whose memory is `toDB db` is the fast read. -/
theorem ld_toDB {S : solver} {db : Array Cell} (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31)
    {q : Cell} {Q : Int} (hq : q.toInt = Q) : S.ld Q = (ld db q).toInt := by
  subst hq; exact (ld_sim S hDB hsz q).symm

/-- `x == y` on cells is equality of their values. -/
theorem beq_cell {x y : Cell} : (x == y) = true ↔ x.toInt = y.toInt := by
  rw [beq_iff_eq]; exact ⟨fun h => h ▸ rfl, fun h => Int32.toInt_inj.mp h⟩

theorem mark_toInt : (MARK : Cell).toInt = MicrosatLean.Faithful.MARK := rfl
theorem implied_toInt : (IMPLIED : Cell).toInt = MicrosatLean.Faithful.IMPLIED := rfl

/-! ### The faithful `bump` as four relinking steps -/

/-- C:87. -/
def mv1 (S : solver) (var : Int) : solver := S.st (S.prev + S.ld (S.next + var)) (S.ld (S.prev + var))
/-- C:88. -/
def mv2 (S : solver) (var : Int) : solver := S.st (S.next + S.ld (S.prev + var)) (S.ld (S.next + var))
/-- C:89. -/
def mv3 (S : solver) (var : Int) : solver := S.st (S.next + S.head) var
/-- C:90. -/
def mv4 (S : solver) (var : Int) : solver := S.st (S.prev + var) S.head

/-- C:86–90 after the MARK. -/
def bumpMove (S1 : solver) (var : Int) : solver :=
  if var = S1.head then S1 else { mv4 (mv3 (mv2 (mv1 S1 var) var) var) var with head := var }

/-- The faithful `bump` (C:85–91), step by step. -/
theorem bump_eq' (S : solver) (lit : Int) : MicrosatLean.Faithful.bump S lit =
    if S.ld (S.false + lit) = MicrosatLean.Faithful.IMPLIED then S else
      bumpMove (S.st (S.false + lit) MicrosatLean.Faithful.MARK) (MicrosatLean.Faithful.abs lit) := by
  unfold MicrosatLean.Faithful.bump bumpMove mv1 mv2 mv3 mv4
  by_cases h : S.ld (S.false + lit) = MicrosatLean.Faithful.IMPLIED
  · simp [h, Id.run]; rfl
  · simp only [h, ite_false, Id.run]
    by_cases h2 : MicrosatLean.Faithful.abs lit = (S.st (S.false + lit) MicrosatLean.Faithful.MARK).head
    · simp [h, h2]; rfl
    · simp [h]; split <;> rfl

/-- One iteration of the fast `bumpLoop` (C:85–91): `db` and `head` after bumping `lit`. -/
def fbump (L : Lay) (db : Array Cell) (head lit : Cell) : Array Cell × Cell :=
  if ld db (L.fls + lit) == IMPLIED then (db, head)
  else
    let db := st db (L.fls + lit) MARK
    let v := absC lit
    if v == head then (db, head)
    else
      let db := st db (L.prev + ld db (L.next + v)) (ld db (L.prev + v))
      let db := st db (L.next + ld db (L.prev + v)) (ld db (L.next + v))
      let db := st db (L.next + head) v
      let db := st db (L.prev + v) head
      (db, v)

/-- `bumpLoop` is `fbump` on each literal up to the terminating 0. -/
theorem bumpLoop_eq (L : Lay) (db : Array Cell) (head c : Cell) : bumpLoop L db head c =
    if ld db c == 0 then (db, head) else
      bumpLoop L (fbump L db head (ld db c)).1 (fbump L db head (ld db c)).2 (c + 1) := by
  rw [bumpLoop.eq_1]
  simp only [fbump]
  split
  · rfl
  · split
    · rfl
    · split <;> rfl

/-! ### `bump_sim` -/

section sim
variable {S : solver} {db : Array Cell} {L : Lay}

theorem mv1_sim (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31) (hnext : S.next = L.next.toInt)
    (hprev : S.prev = L.prev.toInt) {v : Cell}
    (hb : 0 ≤ L.next.toInt ∧ L.next.toInt ≤ 2 ^ 30 ∧ 0 ≤ L.prev.toInt ∧ L.prev.toInt ≤ 2 ^ 30 ∧
      0 ≤ v.toInt ∧ v.toInt ≤ 2 ^ 29)
    (ha : 0 ≤ S.ld (S.next + v.toInt) ∧ S.ld (S.next + v.toInt) ≤ 2 ^ 29) :
    mv1 S v.toInt = { S with DB := toDB (st db (L.prev + ld db (L.next + v)) (ld db (L.prev + v))) } ∧
      (st db (L.prev + ld db (L.next + v)) (ld db (L.prev + v))).size ≤ 2 ^ 31 := by
  have r1 := ld_toDB hDB hsz (q := L.next + v) (Q := S.next + v.toInt) (by rw [toInt_add (by omega) (by omega), hnext])
  have r2 := ld_toDB hDB hsz (q := L.prev + v) (Q := S.prev + v.toInt) (by rw [toInt_add (by omega) (by omega), hprev])
  unfold mv1
  rw [r2]
  rw [r1] at ha ⊢
  exact st_toDB hDB hsz (by rw [toInt_add (by omega) (by omega), hprev]) rfl

theorem mv2_sim (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31) (hnext : S.next = L.next.toInt)
    (hprev : S.prev = L.prev.toInt) {v : Cell}
    (hb : 0 ≤ L.next.toInt ∧ L.next.toInt ≤ 2 ^ 30 ∧ 0 ≤ L.prev.toInt ∧ L.prev.toInt ≤ 2 ^ 30 ∧
      0 ≤ v.toInt ∧ v.toInt ≤ 2 ^ 29)
    (ha : 0 ≤ S.ld (S.prev + v.toInt) ∧ S.ld (S.prev + v.toInt) ≤ 2 ^ 29) :
    mv2 S v.toInt = { S with DB := toDB (st db (L.next + ld db (L.prev + v)) (ld db (L.next + v))) } ∧
      (st db (L.next + ld db (L.prev + v)) (ld db (L.next + v))).size ≤ 2 ^ 31 := by
  have r1 := ld_toDB hDB hsz (q := L.next + v) (Q := S.next + v.toInt) (by rw [toInt_add (by omega) (by omega), hnext])
  have r2 := ld_toDB hDB hsz (q := L.prev + v) (Q := S.prev + v.toInt) (by rw [toInt_add (by omega) (by omega), hprev])
  unfold mv2
  rw [r1]
  rw [r2] at ha ⊢
  exact st_toDB hDB hsz (by rw [toInt_add (by omega) (by omega), hnext]) rfl

theorem mv3_sim (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31) (hnext : S.next = L.next.toInt)
    {v head : Cell} (hhead : S.head = head.toInt)
    (hb : 0 ≤ L.next.toInt ∧ L.next.toInt ≤ 2 ^ 30 ∧ 0 ≤ head.toInt ∧ head.toInt ≤ 2 ^ 29) :
    mv3 S v.toInt = { S with DB := toDB (st db (L.next + head) v) } ∧ (st db (L.next + head) v).size ≤ 2 ^ 31 := by
  unfold mv3
  exact st_toDB hDB hsz (by rw [toInt_add (by omega) (by omega), hnext, hhead]) rfl

theorem mv4_sim (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31) (hprev : S.prev = L.prev.toInt)
    {v head : Cell} (hhead : S.head = head.toInt)
    (hb : 0 ≤ L.prev.toInt ∧ L.prev.toInt ≤ 2 ^ 30 ∧ 0 ≤ v.toInt ∧ v.toInt ≤ 2 ^ 29) :
    mv4 S v.toInt = { S with DB := toDB (st db (L.prev + v) head) } ∧ (st db (L.prev + v) head).size ≤ 2 ^ 31 := by
  unfold mv4
  exact st_toDB hDB hsz (by rw [toInt_add (by omega) (by omega), hprev]) hhead.symm

/-- The fast `fbump` writes what the faithful `bump` writes. The literal is a literal of the
problem; when its variable is not the head, the cells `next[var]`, `prev[var]` and `head`
hold variables or 0 (the decision order, `order_bump_vals`). -/
theorem bump_sim (hDB : S.DB = toDB db) (hsz : db.size ≤ 2 ^ 31) (hn : 1 ≤ S.nVars)
    (hN : 10 * S.nVars + 7 ≤ 2 ^ 30)
    (hfls : S.false = L.fls.toInt) (hnext : S.next = L.next.toInt) (hprev : S.prev = L.prev.toInt)
    (hfv : S.false = 7 * S.nVars + 5) (hnv : S.next = S.nVars + 1) (hpv : S.prev = 2 * S.nVars + 2)
    {head lit : Cell} (hhead : S.head = head.toInt)
    (hlit : lit.toInt ≠ 0 ∧ -S.nVars ≤ lit.toInt ∧ lit.toInt ≤ S.nVars)
    (hvals : MicrosatLean.Faithful.abs lit.toInt ≠ S.head → 0 ≤ S.head ∧ S.head ≤ S.nVars ∧
      0 ≤ S.ld (S.next + MicrosatLean.Faithful.abs lit.toInt) ∧
      S.ld (S.next + MicrosatLean.Faithful.abs lit.toInt) ≤ S.nVars ∧
      0 ≤ S.ld (S.prev + MicrosatLean.Faithful.abs lit.toInt) ∧
      S.ld (S.prev + MicrosatLean.Faithful.abs lit.toInt) ≤ S.nVars) :
    MicrosatLean.Faithful.bump S lit.toInt =
      { S with DB := toDB (fbump L db head lit).1, head := (fbump L db head lit).2.toInt } ∧
      (fbump L db head lit).1.size ≤ 2 ^ 31 := by
  have hav : 1 ≤ MicrosatLean.Faithful.abs lit.toInt ∧ MicrosatLean.Faithful.abs lit.toInt ≤ S.nVars := by
    rcases abs_cases lit.toInt with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hv : (absC lit).toInt = MicrosatLean.Faithful.abs lit.toInt := toInt_absC (by omega)
  have hfl : (L.fls + lit).toInt = S.false + lit.toInt := by rw [toInt_add (by omega) (by omega), hfls]
  have e0 := ld_toDB hDB hsz hfl
  rw [bump_eq']
  unfold fbump
  by_cases hI : S.ld (S.false + lit.toInt) = MicrosatLean.Faithful.IMPLIED
  · rw [ite_eq_left hI, ite_eq_left (beq_cell.mpr (by rw [← e0, hI]; rfl))]
    refine ⟨?_, hsz⟩
    rw [← hDB, ← hhead]
  rw [ite_eq_right hI, ite_eq_right (fun h => hI (by rw [e0, beq_cell.mp h]; rfl))]
  obtain ⟨e1, s1⟩ := st_toDB hDB hsz hfl mark_toInt
  generalize hS1 : S.st (S.false + lit.toInt) MicrosatLean.Faithful.MARK = S1 at e1
  have hS1f : S1.false = S.false ∧ S1.next = S.next ∧ S1.prev = S.prev ∧ S1.head = S.head ∧ S1.nVars = S.nVars := by
    rw [e1]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  have hDB1 : S1.DB = toDB (st db (L.fls + lit) MARK) := by rw [e1]
  have ld1 : ∀ q, 0 ≤ q → q ≠ S.false + lit.toInt → S1.ld q = S.ld q := fun q hq hne => by
    rw [← hS1]; exact ld_st_of_ne _ _ (by omega) hq hne
  generalize hdb1 : st db (L.fls + lit) MARK = db1 at hDB1 s1 e1
  dsimp only
  unfold bumpMove
  by_cases hH : MicrosatLean.Faithful.abs lit.toInt = S1.head
  · rw [ite_eq_left hH, ite_eq_left (beq_cell.mpr (by rw [hv, hH, hS1f.2.2.2.1, hhead]))]
    refine ⟨?_, s1⟩
    rw [e1, ← hhead]
  rw [ite_eq_right hH, ite_eq_right (fun h => hH (by rw [← hv, beq_cell.mp h, hS1f.2.2.2.1, hhead]))]
  have hHS : MicrosatLean.Faithful.abs lit.toInt ≠ S.head := fun h => hH (by rw [hS1f.2.2.2.1]; exact h)
  obtain ⟨hh0, hh1, ha0, ha1, hc0, hc1⟩ := hvals hHS
  generalize hvar : MicrosatLean.Faithful.abs lit.toInt = var at hav hH hHS ha0 ha1 hc0 hc1 hv
  have ha : S1.ld (S1.next + var) = S.ld (S.next + var) := by
    rw [hS1f.2.1]; exact ld1 _ (by omega) (by omega)
  have hc : S1.ld (S1.prev + var) = S.ld (S.prev + var) := by
    rw [hS1f.2.2.1]; exact ld1 _ (by omega) (by omega)
  have hb : 0 ≤ L.next.toInt ∧ L.next.toInt ≤ 2 ^ 30 ∧ 0 ≤ L.prev.toInt ∧ L.prev.toInt ≤ 2 ^ 30 ∧
      0 ≤ (absC lit).toInt ∧ (absC lit).toInt ≤ 2 ^ 29 := by omega
  rw [← hv]
  obtain ⟨e2, s2⟩ := mv1_sim hDB1 s1 (by rw [hS1f.2.1, hnext]) (by rw [hS1f.2.2.1, hprev]) hb
    (by rw [hv, ha]; omega)
  rw [e2]
  have hDB2 : ({ S1 with DB := toDB (st db1 (L.prev + ld db1 (L.next + absC lit)) (ld db1 (L.prev + absC lit))) } : solver).DB =
      toDB (st db1 (L.prev + ld db1 (L.next + absC lit)) (ld db1 (L.prev + absC lit))) := rfl
  -- the cells `mv1` leaves: `prev[var]` is `prev[var]` before (or the value written there)
  have hS2 : ({ S1 with DB := toDB (st db1 (L.prev + ld db1 (L.next + absC lit)) (ld db1 (L.prev + absC lit))) } : solver) =
      mv1 S1 var := by rw [← hv, e2]
  have hc2 : 0 ≤ (mv1 S1 var).ld ((mv1 S1 var).prev + var) ∧ (mv1 S1 var).ld ((mv1 S1 var).prev + var) ≤ 2 ^ 29 := by
    unfold mv1
    rw [st_prev, ld_st _ _ (by rw [hS1f.2.2.1, ha]; omega) (by rw [hS1f.2.2.1]; omega)]
    split <;> rw [hc] <;> omega
  rw [← hS2, ← hv] at hc2
  generalize st db1 (L.prev + ld db1 (L.next + absC lit)) (ld db1 (L.prev + absC lit)) = db2 at hDB2 hc2 s2 ⊢
  obtain ⟨e3, s3⟩ := mv2_sim hDB2 s2 (by rw [hS1f.2.1, hnext]) (by rw [hS1f.2.2.1, hprev]) hb hc2
  rw [e3]
  generalize st db2 (L.next + ld db2 (L.prev + absC lit)) (ld db2 (L.next + absC lit)) = db3 at s3 ⊢
  obtain ⟨e4, s4⟩ := mv3_sim (v := absC lit) (S := ({ ({ S1 with DB := toDB db2 } : solver) with DB := toDB db3 } : solver))
    rfl s3 (by show S1.next = _; rw [hS1f.2.1, hnext]) (head := head)
    (by show S1.head = _; rw [hS1f.2.2.2.1, hhead]) (by omega)
  rw [e4]
  generalize st db3 (L.next + head) (absC lit) = db4 at s4 ⊢
  obtain ⟨e5, s5⟩ := mv4_sim (v := absC lit)
    (S := ({ ({ ({ S1 with DB := toDB db2 } : solver) with DB := toDB db3 } : solver) with DB := toDB db4 } : solver))
    rfl s4 (by show S1.prev = _; rw [hS1f.2.2.1, hprev]) (head := head)
    (by show S1.head = _; rw [hS1f.2.2.2.1, hhead]) (by omega)
  rw [e5]
  refine ⟨?_, s5⟩
  rw [e1]

end sim

/-- The cells `bump` reads when it relinks a variable `v` other than the head: `head`,
`next[v]` and `prev[v]` hold variables or 0 (C:87–90). -/
theorem order_bump_vals {S : solver} {vs : List Int} (ho : OrderList S vs) {v : Int}
    (hv : 1 ≤ v ∧ v ≤ S.nVars) (hH : v ≠ S.head) :
    0 ≤ S.head ∧ S.head ≤ S.nVars ∧ 0 ≤ S.ld (S.next + v) ∧ S.ld (S.next + v) ≤ S.nVars ∧
      0 ≤ S.ld (S.prev + v) ∧ S.ld (S.prev + v) ≤ S.nVars := by
  obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem (ho.mem_iff.mpr hv)
  have hvs : ∀ j (hj : j < vs.length), 1 ≤ vs[j] ∧ vs[j] ≤ S.nVars :=
    fun j hj => ho.mem_iff.mp (List.getElem_mem hj)
  have h0 : vs[0] = S.head := ho.chain.head_eq (by omega)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun e => hH (by subst e; exact hkv.symm.trans h0)
  have ha : S.ld (S.next + v) = vs[k - 1] := by
    have := ho.next_back (k - 1) (by omega)
    simp only [show k - 1 + 1 = k by omega, hkv] at this
    exact this
  have hc : S.ld (S.prev + v) = vs[k + 1]?.getD 0 := by
    rw [← hkv]; exact ho.chain.prev_getElem k hk
  have hh := hvs 0 (by omega)
  have hk1 := hvs (k - 1) (by omega)
  rw [h0] at hh
  rw [ha, hc]
  refine ⟨by omega, by omega, by omega, by omega, ?_⟩
  by_cases hk2 : k + 1 < vs.length
  · rw [List.getElem?_eq_getElem hk2, Option.getD_some]; have := hvs _ hk2; omega
  · rw [List.getElem?_eq_none (by omega), Option.getD_none]; omega

/-- What `bump_sim` needs about the state and the literal. -/
structure BumpOK (L : Lay) (S : solver) (lit : Int) : Prop where
  layout : Layout S
  nVars : 10 * S.nVars + 7 ≤ 2 ^ 30
  fls : S.false = L.fls.toInt
  next : S.next = L.next.toInt
  prev : S.prev = L.prev.toInt
  lit : InRange S.nVars lit
  order : ∃ vs, OrderList S vs

/-- One fast bump step from a state that stands for `db` and `head`. -/
theorem bump_step {L : Lay} {S0 : solver} {db : Array Cell} {head lit : Cell} (hsz : db.size ≤ 2 ^ 31)
    (hok : BumpOK L ({ S0 with DB := toDB db, head := head.toInt } : solver) lit.toInt) :
    MicrosatLean.Faithful.bump ({ S0 with DB := toDB db, head := head.toInt } : solver) lit.toInt =
      ({ S0 with DB := toDB (fbump L db head lit).1, head := (fbump L db head lit).2.toInt } : solver) ∧
      (fbump L db head lit).1.size ≤ 2 ^ 31 := by
  have hl := hok.layout
  have hnum := hl.num
  obtain ⟨vs, ho⟩ := hok.order
  have hlit := inRange_iff.mp hok.lit
  exact bump_sim rfl hsz hl.nVars_pos hok.nVars hok.fls hok.next hok.prev hnum.2.2.2.2.2.2.1 hnum.2.1 hnum.2.2.1
    rfl hlit fun hH => order_bump_vals ho (by rcases abs_cases lit.toInt with ⟨_, e⟩ | ⟨_, e⟩ <;> omega) hH

/-- The fast `bumpLoop` from cell `c` keeps any invariant `I` (of the faithful state and the
cell) that the faithful `bump` keeps, and stops at a 0 cell. The faithful states are `S0` with
the fast `db` and `head`; `I` bounds the cell below `bound ≤ 2^30`. -/
theorem bumpLoop_spec {L : Lay} {S0 : solver} (I : solver → Int → Prop) {bound : Int}
    (hbound : bound ≤ 2 ^ 30)
    (hstep : ∀ S cl, I S cl → S.ld cl ≠ 0 → I (MicrosatLean.Faithful.bump S (S.ld cl)) (cl + 1))
    (hcl : ∀ S cl, I S cl → 0 ≤ cl ∧ cl < bound)
    (hok : ∀ S cl, I S cl → S.ld cl ≠ 0 → BumpOK L S (S.ld cl)) :
    ∀ (k : Nat) (db : Array Cell) (head c : Cell), (bound - c.toInt).toNat = k →
      I ({ S0 with DB := toDB db, head := head.toInt } : solver) c.toInt → db.size ≤ 2 ^ 31 →
      ∃ cl, I ({ S0 with DB := toDB (bumpLoop L db head c).1, head := (bumpLoop L db head c).2.toInt } : solver) cl ∧
        ({ S0 with DB := toDB (bumpLoop L db head c).1, head := (bumpLoop L db head c).2.toInt } : solver).ld cl = 0 ∧
        (bumpLoop L db head c).1.size ≤ 2 ^ 31 := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro db head c hk hI hsz
  have hc := hcl _ _ hI
  have hld : ({ S0 with DB := toDB db, head := head.toInt } : solver).ld c.toInt = (ld db c).toInt :=
    ld_toDB rfl hsz rfl
  rw [bumpLoop_eq]
  by_cases hz : ld db c == 0
  · rw [ite_eq_left hz]
    refine ⟨c.toInt, hI, ?_, hsz⟩
    rw [hld, beq_cell.mp hz]; rfl
  · rw [ite_eq_right hz]
    have hne : ({ S0 with DB := toDB db, head := head.toInt } : solver).ld c.toInt ≠ 0 := by
      rw [hld]; exact fun h => hz (beq_cell.mpr h)
    have h1 := hstep _ _ hI hne
    have hok' := hok _ _ hI hne
    rw [hld] at h1 hok'
    obtain ⟨e, hsz'⟩ := bump_step hsz hok'
    rw [e] at h1
    have hone : ((1 : Cell)).toInt = 1 := rfl
    have hc1 : (c + 1).toInt = c.toInt + 1 := by rw [toInt_add (by rw [hone]; omega) (by rw [hone]; omega), hone]
    rw [← hc1] at h1
    have hc' := hcl _ _ h1
    exact ih _ (by rw [hc1] at hc'; omega) _ _ _ rfl h1 hsz'

end MicrosatLean.Fast.Verification.AnalyzeAux
