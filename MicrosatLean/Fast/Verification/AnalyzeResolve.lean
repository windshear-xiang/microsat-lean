import MicrosatLean.Fast.Verification.AnalyzeImplied

/-!
# MARK and resolution in the fast `analyze` (C:103–113)

The faithful states of the fast `analyze` are `AS T nc db a p h`: the conflict state `T` with
the fast arena `db`, the loop's `assigned`, `processed` and `head`, and the new conflict count
`nc`. They have `T`'s fields up to the ones `analyze` writes (`AFields`), so the faithful loop
invariants (`BumpInv`, `ResInv`, `CheckInv`, `RBump`) and their step lemmas apply to them.
`bumpConf_spec` is C:104, `checkLoop_spec` C:108–109, `resolveLoop_spec` C:105–113.
-/

namespace MicrosatLean.Fast.Verification.AnalyzeAux

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- The faithful state of `analyze` for the fast loop variables. -/
def AS (T : solver) (nc : Int) (db : Array Cell) (a p h : Int) : solver :=
  { T with DB := toDB db, assigned := a, processed := p, head := h, nConflicts := nc }

section AS
variable {T : solver} {nc : Int} {db : Array Cell} {a p h : Int}

@[simp] theorem AS_DB : (AS T nc db a p h).DB = toDB db := rfl
@[simp] theorem AS_assigned : (AS T nc db a p h).assigned = a := rfl
@[simp] theorem AS_processed : (AS T nc db a p h).processed = p := rfl
@[simp] theorem AS_head : (AS T nc db a p h).head = h := rfl

/-- Reading `AS` reads only the arena. -/
theorem AS_ld_congr (a' p' h' : Int) (q : Int) : (AS T nc db a p h).ld q = (AS T nc db a' p' h').ld q := rfl

theorem AS_fields : AFields T (AS T nc db a p h) := ⟨toDB db, a, p, h, T.res, nc, T.fast, T.slow, rfl⟩

theorem AS_dbhead (db' : Array Cell) (h' : Int) :
    ({ AS T nc db a p h with DB := toDB db', head := h' } : solver) = AS T nc db' a p h' := rfl

/-- A write to `AS` is the fast write. -/
theorem AS_st (hsz : db.size ≤ 2 ^ 31) {q v : Cell} {Q V : Int} (hq : q.toInt = Q) (hv : v.toInt = V) :
    (AS T nc db a p h).st Q V = AS T nc (st db q v) a p h ∧ (st db q v).size ≤ 2 ^ 31 :=
  st_toDB rfl hsz hq hv

/-- A read of `AS` is the fast read. -/
theorem AS_ld (hsz : db.size ≤ 2 ^ 31) {q : Cell} {Q : Int} (hq : q.toInt = Q) :
    (AS T nc db a p h).ld Q = (ld db q).toInt :=
  ld_toDB rfl hsz hq

end AS

/-- The offsets of `L` are those of the conflict state `T`, with the bounds that rule out
overflow. -/
structure FEnv (T : solver) (L : Lay) : Prop where
  ienv : IEnv T L
  next : T.next = L.next.toInt
  prev : T.prev = L.prev.toInt
  buffer : T.buffer = L.buffer.toInt

section loops
variable {input : Input} {T : solver} {dbr : Records} {vs : List Int} {D : Nat} {L : Lay}

/-- A state with `T`'s fields and low cells, and a decision order, can be bumped at a literal
of the problem. -/
theorem bumpOK_of (ctx : ACtx input T dbr vs D) (env : FEnv T L) {S : solver} (hf : AFields T S)
    (hl : SameLow T S) (ho : ∃ vs, OrderList S vs) {l : Int} (hlit : InRange T.nVars l) : BumpOK L S l := by
  have hs := hf.shape
  refine ⟨ctx.layout hf hl, by rw [hs.nVars]; exact env.ienv.nVars, by rw [hs.false]; exact env.ienv.fls,
    by rw [hs.next]; exact env.next, by rw [hs.prev]; exact env.prev, by rw [hs.nVars]; exact hlit, ho⟩

/-- The state after C:103 for the fast port: `T` with the new conflict count. -/
theorem RState.initFast (ctx : ACtx input T dbr vs D) (nc : Int) :
    RState T ({ T with nConflicts := nc } : solver) (trailLen T) := by
  have ht := ctx.core.trail
  have o := ctx.core.order
  exact ⟨⟨T.DB, T.assigned, T.processed, T.head, T.res, nc, T.fast, T.slow, rfl⟩,
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun q _ _ => rfl, fun q _ => rfl⟩, fun q _ _ => rfl,
    Nat.le_refl _, ⟨vs, o.1.congr fun _ _ => rfl, o.2, o.3, o.4⟩, fun i hi hr => ht.flag_root i hi hr,
    fun i hi hr => Or.inl (ht.flag_level i hi hr), fun i h1 h2 => absurd h2 (by omega),
    fun l hl ho => ht.flag_off l hl ho, ht.flag_zero⟩

/-- C:104: the fast bump of the conflict clause `r` (at the cell `c`) ends in the state where
the resolution loop starts (`ResInv.init`). -/
theorem bumpConf_spec (ctx : ACtx input T dbr vs D) (env : FEnv T L) {r : Record} (hr : r ∈ dbr.all)
    (hfalse : ∀ l ∈ r.2, ∃ j < trailLen T, trailAt T j = l)
    (hmark : ∃ j, D ≤ j ∧ j < trailLen T ∧ trailAt T j ∈ r.2) (nc : Int) {c : Cell} (hc : c.toInt = r.1)
    {db : Array Cell} (hDB : T.DB = toDB db) (hsz : db.size ≤ 2 ^ 31) {head : Cell} (hhead : T.head = head.toInt) :
    ResInv input T D (AS T nc (bumpLoop L db head c).1 T.assigned T.processed (bumpLoop L db head c).2.toInt)
      (trailLen T) ∧ (bumpLoop L db head c).1.size ≤ 2 ^ 31 := by
  have hn := ctx.num
  have hmu := env.ienv.mem
  have hge := ctx.core.database.record_ge hr
  simp only [clausesAt] at hge
  have hT : ({ ({ T with nConflicts := nc } : solver) with DB := toDB db, head := head.toInt } : solver) =
      ({ T with nConflicts := nc } : solver) := by rw [← hDB, ← hhead]
  obtain ⟨cl, hI, hz, hsz'⟩ := bumpLoop_spec (L := L) (S0 := ({ T with nConflicts := nc } : solver))
    (fun S cl => BumpInv T S r.1 r.2 cl) (bound := T.mem_used) hmu
    (fun S cl h hne => (BumpInv.step ctx hr hfalse h hne).1)
    (fun S cl h => by obtain ⟨-, -, k, hk, rfl, -⟩ := h; omega)
    (fun S cl h hne => by
      obtain ⟨hrs, -, k, hk, rfl, -⟩ := h
      have hread := ctx.read hrs.low hr hk
      have hk' : k < r.2.length := Classical.byContradiction fun hn' => hne (by rw [hread, dite_eq_right hn'])
      rw [hread, dite_eq_left hk']
      obtain ⟨j, hj, hje⟩ := hfalse _ (List.getElem_mem hk')
      rw [← hje]
      exact bumpOK_of ctx env hrs.fields hrs.low hrs.order (ctx.core.trail.lit j hj))
    _ db head c rfl (by
      rw [hT]
      exact ⟨RState.initFast ctx nc, rfl, 0, Nat.zero_le _, by rw [hc]; simp, fun i _ _ hm => by simp at hm⟩)
    hsz
  exact ⟨ResInv.init ctx hr hfalse hmark hI hz, hsz'⟩

/-- C:108–109: the fast check loop, from `ck` below the top position `a - 1`, answers as
`CheckOut` says (`true`: the first UIP is reached, `goto build`). -/
theorem checkLoop_spec (ctx : ACtx input T dbr vs D) (env : FEnv T L) {S0 : solver} {a : Nat}
    (hres : ResInv input T D S0 a) {db : Array Cell} (hDB : S0.DB = toDB db) (hsz : db.size ≤ 2 ^ 31) :
    ∀ (k : Nat) (ck : Cell), (ck.toInt - T.falseStack).toNat = k →
      CheckInv T D ({ S0 with assigned := S0.assigned - 1 } : solver) ck.toInt →
      CheckOut T D ({ S0 with assigned := S0.assigned - 1 } : solver) (checkLoop L db ck) := by
  have hn := ctx.num
  have hfls := env.ienv.fls; have hrs := env.ienv.reason; have hN := env.ienv.nVars
  have hrs1 := hres.1.setAssigned (S0.assigned - 1)
  have hs1 := hrs1.fields.shape
  have hone : ((1 : Cell)).toInt = 1 := rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro ck hk hinv
  obtain ⟨k', hck, hDk, hkj, hA, hnm, hfl, hrd⟩ := check_reads ctx hres hinv
  have hDB1 : ({ S0 with assigned := S0.assigned - 1 } : solver).DB = toDB db := hDB
  have hc1 : (ck - 1).toInt = ck.toInt - 1 := by rw [toInt_sub (by rw [hone]; omega) (by rw [hone]; omega), hone]
  have htr : ({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck.toInt - 1) = trailAt T (k' - 1) := by
    rw [hck, show T.falseStack + (k' : Int) - 1 = T.falseStack + ((k' - 1 : Nat) : Int) by omega]
    exact hrs1.low.trail ctx (by omega)
  have hy : (ld db (ck - 1)).toInt = trailAt T (k' - 1) := by rw [← ld_toDB hDB1 hsz hc1, htr]
  have hyl := ctx.lit (show k' - 1 < trailLen T by omega)
  have hfy : (L.fls + ld db (ck - 1)).toInt = ({ S0 with assigned := S0.assigned - 1 } : solver).false +
      ({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck.toInt - 1) := by
    rw [toInt_add (by omega) (by omega), hy, htr, hs1.false, hfls]
  have hfly := ld_toDB hDB1 hsz hfy
  have hay : (absC (ld db (ck - 1))).toInt = MicrosatLean.Faithful.abs (trailAt T (k' - 1)) := by
    rw [toInt_absC (by omega), hy]
  have hav : 1 ≤ MicrosatLean.Faithful.abs (trailAt T (k' - 1)) ∧
      MicrosatLean.Faithful.abs (trailAt T (k' - 1)) ≤ T.nVars := by
    rcases abs_cases (trailAt T (k' - 1)) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hry : (L.reason + absC (ld db (ck - 1))).toInt = ({ S0 with assigned := S0.assigned - 1 } : solver).reason +
      MicrosatLean.Faithful.abs (({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck.toInt - 1)) := by
    rw [toInt_add (by omega) (by omega), hay, htr, hs1.reason, hrs]
  have hrdy := ld_toDB hDB1 hsz hry
  rw [checkLoop.eq_1]
  by_cases hm : ({ S0 with assigned := S0.assigned - 1 } : solver).ld
      (({ S0 with assigned := S0.assigned - 1 } : solver).false +
        ({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck.toInt - 1)) = MicrosatLean.Faithful.MARK
  · have hm' : (ld db (L.fls + ld db (ck - 1)) == MARK) = true := beq_cell.mpr (by rw [← hfly, hm]; rfl)
    rw [ite_eq_left hm']
    exact vc_check_mark ctx hres ⟨rfl, hinv⟩ hm
  · have hm' : ¬ ((ld db (L.fls + ld db (ck - 1)) == MARK) = true) := fun h => hm (by
      rw [hfly, beq_cell.mp h]; rfl)
    rw [ite_eq_right hm']
    by_cases hz : ({ S0 with assigned := S0.assigned - 1 } : solver).ld
        (({ S0 with assigned := S0.assigned - 1 } : solver).reason +
          MicrosatLean.Faithful.abs (({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck.toInt - 1))) = 0
    · have hz' : (ld db (L.reason + absC (ld db (ck - 1))) == 0) = true := beq_cell.mpr (by rw [← hrdy, hz]; rfl)
      rw [ite_eq_left hz']
      exact vc_check_dec ctx hres ⟨rfl, hinv⟩ hm hz
    · have hz' : ¬ ((ld db (L.reason + absC (ld db (ck - 1))) == 0) = true) := fun h => hz (by
        rw [hrdy, beq_cell.mp h]; rfl)
      rw [ite_eq_right hz']
      obtain ⟨e1, -, e3⟩ := vc_check_next ctx hres ⟨rfl, hinv⟩ hm hz
      rw [← hc1] at e3
      exact ih _ (by rw [hc1]; omega) (ck - 1) rfl e3

/-- C:105–113: the fast resolution loop, from a state where `ResInv` holds, ends at the first
UIP (`BuildStart`). The faithful states are `AS` with `processed = p0`. -/
theorem resolveLoop_spec (ctx : ACtx input T dbr vs D) (env : FEnv T L) (nc p0 : Int) :
    ∀ (k : Nat) (db : Array Cell) (head assigned : Cell) (a : Nat), (assigned.toInt - T.falseStack).toNat = k →
      db.size ≤ 2 ^ 31 → ResInv input T D (AS T nc db assigned.toInt p0 head.toInt) a →
      (∃ u, BuildStart input T D (AS T nc (resolveLoop L db head assigned).1
          (resolveLoop L db head assigned).2.2.toInt p0 (resolveLoop L db head assigned).2.1.toInt) u) ∧
        (resolveLoop L db head assigned).1.size ≤ 2 ^ 31 := by
  have hn := ctx.num
  have hfls := env.ienv.fls; have hrs := env.ienv.reason; have hN := env.ienv.nVars; have hmu := env.ienv.mem
  have hone : ((1 : Cell)).toInt = 1 := rfl
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
  intro db head assigned a hk hsz hres
  obtain ⟨hA1, hlt, hDj, htr, hrd, hfl⟩ := hres.reads ctx
  have hA : assigned.toInt = T.falseStack + a := hres.2.1
  have hDa := hres.2.2.1
  have ha1 : (assigned - 1).toInt = assigned.toInt - 1 := by
    rw [toInt_sub (by rw [hone]; omega) (by rw [hone]; omega), hone]
  have hS1 : ({ AS T nc db assigned.toInt p0 head.toInt with
      assigned := (AS T nc db assigned.toInt p0 head.toInt).assigned - 1 } : solver) =
      AS T nc db (assigned - 1).toInt p0 head.toInt := by rw [ha1]; rfl
  rw [hS1] at hA1 htr hrd hfl
  simp only [AS_assigned] at hA1 htr hrd hfl
  have hxl := ctx.lit hlt
  have hx : (ld db (assigned - 1)).toInt = trailAt T (a - 1) := by rw [← AS_ld hsz rfl, htr]
  have hav : 1 ≤ MicrosatLean.Faithful.abs (trailAt T (a - 1)) ∧
      MicrosatLean.Faithful.abs (trailAt T (a - 1)) ≤ T.nVars := by
    rcases abs_cases (trailAt T (a - 1)) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hax : (absC (ld db (assigned - 1))).toInt = MicrosatLean.Faithful.abs (trailAt T (a - 1)) := by
    rw [toInt_absC (by omega), hx]
  have hrx : (ld db (L.reason + absC (ld db (assigned - 1)))).toInt = reasonOf T (trailAt T (a - 1)) := by
    rw [← hrd, htr]
    exact (AS_ld hsz (by rw [toInt_add (by omega) (by omega), hax, ← hrs]; rfl)).symm
  have hfx : (L.fls + ld db (assigned - 1)).toInt = T.false + trailAt T (a - 1) := by
    rw [toInt_add (by omega) (by omega), hx, hfls]
  have hflx : (ld db (L.fls + ld db (assigned - 1))).toInt = flag (AS T nc db assigned.toInt p0 head.toInt) (trailAt T (a - 1)) := by
    rw [← AS_ld (T := T) (nc := nc) (a := assigned.toInt) (p := p0) (h := head.toInt) hsz hfx]; rfl
  have hmeas : ((assigned - 1).toInt - T.falseStack).toNat < k := by rw [ha1]; omega
  generalize hR : resolveLoop L db head assigned = R
  rw [resolveLoop.eq_1] at hR
  by_cases hz : reasonOf T (trailAt T (a - 1)) = 0
  · have hz' : (ld db (L.reason + absC (ld db (assigned - 1))) == 0) = true := beq_cell.mpr (by rw [hrx, hz]; rfl)
    rw [ite_eq_left hz'] at hR
    subst hR
    have := hres.decision ctx hz
    rw [hS1] at this
    exact ⟨⟨_, this⟩, hsz⟩
  have hz' : ¬ ((ld db (L.reason + absC (ld db (assigned - 1))) == 0) = true) := fun h => hz (by
    rw [← hrx, beq_cell.mp h]; rfl)
  rw [ite_eq_right hz'] at hR
  by_cases hm : flag (AS T nc db assigned.toInt p0 head.toInt) (trailAt T (a - 1)) = MicrosatLean.Faithful.MARK
  · have hm' : (ld db (L.fls + ld db (assigned - 1)) == MARK) = true := beq_cell.mpr (by rw [hflx, hm]; rfl)
    rw [ite_eq_left hm'] at hR
    have hci := hres.check_init ctx hz
    rw [hS1] at hci
    simp only [AS_assigned] at hci
    have hcs := checkLoop_spec (L := L) ctx env hres (db := db) rfl hsz _ (assigned - 1) rfl (by rw [hS1]; exact hci)
    by_cases hck : checkLoop L db (assigned - 1) = true
    · rw [ite_eq_left hck] at hR
      subst hR
      rw [hck] at hcs
      have := hres.uip ctx hm hcs
      rw [hS1] at this
      exact ⟨⟨_, this⟩, hsz⟩
    · have hck' : checkLoop L db (assigned - 1) = false := by simpa using hck
      rw [ite_eq_right hck] at hR
      rw [hck'] at hcs
      -- C:110–112: bump the reason
      have hrb := RBump.init ctx hres hz
      rw [hS1] at hrb
      have hcl : (AS T nc db (assigned - 1).toInt p0 head.toInt).ld
          ((AS T nc db (assigned - 1).toInt p0 head.toInt).reason +
            MicrosatLean.Faithful.abs ((AS T nc db (assigned - 1).toInt p0 head.toInt).ld (assigned - 1).toInt)) =
          (ld db (L.reason + absC (ld db (assigned - 1)))).toInt := by rw [hrd, hrx]
      simp only [AS_assigned] at hrb
      rw [hcl] at hrb
      obtain ⟨cl, hI, hzc, hsz2⟩ := bumpLoop_spec (L := L) (S0 := AS T nc db (assigned - 1).toInt p0 head.toInt)
        (fun S cl => RBump T dbr (AS T nc db (assigned - 1).toInt p0 head.toInt) S cl) (bound := T.mem_used) hmu
        (fun S cl h hne => (RBump.step ctx h hne).1)
        (fun S cl h => by
          obtain ⟨j, rr, -, -, hrr, -, -, -, k, hk1, hk, rfl, -⟩ := h
          have := ctx.core.database.record_ge hrr; simp only [clausesAt] at this; omega)
        (fun S cl h hne => by
          obtain ⟨j, rr, -, hj, hrr, -, -, hdrop, k, hk1, hk, rfl, hrs', -⟩ := h
          have hread := ctx.read hrs'.low hrr hk
          have hk' : k < rr.2.length := Classical.byContradiction fun hn' => hne (by rw [hread, dite_eq_right hn'])
          rw [hread, dite_eq_left hk']
          obtain ⟨i0, hi0, ⟨hi0t, hie⟩⟩ := hdrop _ (mem_drop_one hk1 hk')
          rw [← hie]
          exact bumpOK_of ctx env hrs'.fields hrs'.low hrs'.order (ctx.core.trail.lit i0 hi0t))
        _ db head _ rfl hrb hsz
      generalize hB : bumpLoop L db head (ld db (L.reason + absC (ld db (assigned - 1)))) = B at hI hzc hsz2 hR
      obtain ⟨db2, head2⟩ := B
      simp only at hR hI hzc hsz2
      rw [AS_dbhead] at hI hzc
      obtain ⟨hres', -⟩ := hres.resolve ctx hm hcs (by rw [hS1]; exact hI) hzc
      -- the top literal is still on the trail of the bumped state
      obtain ⟨j, rr, hA1', -, -, -, -, -, -, -, -, -, hrs2, hA2, -⟩ := hI
      have htr2 : (AS T nc db2 (assigned - 1).toInt p0 head2.toInt).ld (AS T nc db2 (assigned - 1).toInt p0 head2.toInt).assigned =
          (ld db (assigned - 1)).toInt := by
        simp only [AS_assigned]; rw [hx, hA1]; exact hrs2.low.trail ctx hlt
      rw [htr2] at hres'
      obtain ⟨e, sz⟩ := AS_st (T := T) (nc := nc) (a := (assigned - 1).toInt) (p := p0) (h := head2.toInt) hsz2
        (q := L.fls + ld db (assigned - 1)) (v := 0) (Q := T.false + (ld db (assigned - 1)).toInt) (V := 0)
        (by rw [hfx, hx]) rfl
      rw [MicrosatLean.Faithful.Verification.unassign_eq] at hres'
      simp only [show (AS T nc db2 (assigned - 1).toInt p0 head2.toInt).false = T.false from rfl] at hres'
      rw [e] at hres'
      subst hR
      exact ih _ hmeas _ _ _ _ rfl sz hres'
  · have hm' : ¬ ((ld db (L.fls + ld db (assigned - 1)) == MARK) = true) := fun h => hm (by
      rw [← hflx, beq_cell.mp h]; rfl)
    rw [ite_eq_right hm'] at hR
    obtain ⟨hres', -⟩ := hres.skip ctx hm hz
    rw [hS1] at hres'
    simp only [AS_assigned] at hres'
    rw [htr, MicrosatLean.Faithful.Verification.unassign_eq] at hres'
    obtain ⟨e, sz⟩ := AS_st (T := T) (nc := nc) (a := (assigned - 1).toInt) (p := p0) (h := head.toInt) hsz
      (q := L.fls + ld db (assigned - 1)) (v := 0) (Q := T.false + trailAt T (a - 1)) (V := 0) hfx rfl
    simp only [show (AS T nc db (assigned - 1).toInt p0 head.toInt).false = T.false from rfl] at hres'
    rw [e] at hres'
    subst hR
    exact ih _ hmeas _ _ _ _ rfl sz hres'

end loops

end MicrosatLean.Fast.Verification.AnalyzeAux
