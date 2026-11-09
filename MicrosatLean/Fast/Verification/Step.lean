import MicrosatLean.Fast.Verification.Propagate
import MicrosatLean.Fast.Verification.ReduceDB

/-!
# One iteration of the fast `run` (C:163–179), and the loop as a whole

`fstep` is the body of the fast `run` without the recursive call (`run_eq`). Its contract
(`fstep_cases`) is the faithful `step_cases` for the fast port: from the fast invariant
`FInv`, a final step answers correctly (or runs out of memory), a non-final step keeps
`FInv` and decreases the faithful `rank`. `FRunsTo` and `frunsTo_of_rank` give
termination as in the faithful `Run.lean`. The analysis and `reduceDB` enter as the
statements `ConflictSpec` and `ReduceSpec` (proved in `Analyze.lean` and `ReduceDB.lean`).
-/

namespace MicrosatLean.Fast.Verification

set_option linter.deprecated false

open MicrosatLean.Faithful (solver Input modelOf)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- The state between two iterations of the fast `run`, or its value. -/
inductive FProgress where
  | running (s : St) (d : Cell)
  | finished (out : St × UInt8)

/-- C:166–172 after `propagate` returned `s1` (from a state with `old` lemmas): the next
state and decision cursor. After a conflict the cursor goes back to `head`, and maybe a
restart and a `reduceDB` happen. -/
def fpick (L : Lay) (s1 : St) (old decision : Cell) : St × Cell :=
  if s1.nLemmas > old then
    if s1.fast > (s1.slow / 100) * 125 then
      let s := restart L { s1 with fast := (s1.slow / 100) * 125 }
      (if s.nLemmas > s.maxLemmas then reduceDB L s 6 else s, s.head)
    else (s1, s1.head)
  else (s1, decision)

/-- C:173–179: the decision. -/
def fdecide (L : Lay) (s : St) (decision : Cell) : FProgress :=
  let d := decideLoop L s.db decision
  if d == 0 then .finished (s, SAT)
  else
    let d := if ld s.db d != 0 then d else -d
    let (db, s) := s.take
    let db := st db (L.fls - d) 1
    let db := st db s.assigned (-d)
    let db := st db (L.reason + absC d) 0
    .running { s with db, assigned := s.assigned + 1 } (absC d)

/-- The body of the fast `run` (C:163–179) without the recursive call. -/
def fstep (L : Lay) (s : St) (decision : Cell) : FProgress :=
  let (s1, r) := propagate L s
  if r != SAT then .finished (s1, r)
  else
    let (s2, d2) := fpick L s1 s.nLemmas decision
    fdecide L s2 d2

theorem run_eq (L : Lay) (s : St) (d : Cell) :
    run L s d = match fstep L s d with
      | .finished out => out
      | .running s' d' => run L s' d' := by
  rw [run.eq_1]
  unfold fstep fpick fdecide
  dsimp only
  repeat' split
  all_goals first
    | rfl
    | (rename_i heq; cases heq; rfl)
    | (rename_i heq; cases heq)

/-! ### The invariant and the decision -/

/-- The fast loop invariant at the top of `run`: `Bounds` and the faithful `Inv` of an
abstraction. -/
def FInv (input : Input) (L : Lay) (s : St) (d : Cell) : Prop :=
  Bounds L s ∧ ∃ fa sl, Inv input (abs L s (memoryBound input) fa sl) d.toInt

/-- The model the fast port prints (`printModel` in `FastMain.lean`): variable `v` is true
when its `model` cell is nonzero. -/
def fastModel (s : St) : Assignment := fun v => ld s.db (Int32.ofNat v) != 0

/-- A correct answer of the fast port: out of memory, or SAT with a printed model that
satisfies the input, or UNSAT for an unsatisfiable input. -/
def FCorrect (input : Input) (_L : Lay) (out : St × UInt8) : Prop :=
  out.2 = OOM ∨ (out.2 = SAT ∧ input.Sat (fastModel out.1)) ∨ (out.2 = UNSAT ∧ input.Unsat)

/-- The printed model is the faithful `modelOf` on the variables of a valid input. -/
theorem sat_fast {input : Input} {L : Lay} {s : St} {M fa sl : Int} (valid : input.Valid)
    (hB : Bounds L s) (hn : (abs L s M fa sl).nVars = max 1 input.nVars)
    (h : input.Sat (modelOf (abs L s M fa sl))) : input.Sat (fastModel s) := by
  obtain ⟨hN1, hN2⟩ := hB.nVars
  have eN : (abs L s M fa sl).nVars = L.nVars.toInt := rfl
  intro clause hc
  obtain ⟨lit, hlit, ht⟩ := h clause hc
  refine ⟨lit, hlit, ?_⟩
  obtain ⟨hl0, hla⟩ := valid.lit_range clause hc lit (by simpa using hlit)
  have hv : (lit.natAbs : Int) ≤ L.nVars.toInt := by
    unfold MicrosatLean.Faithful.abs at hla; split at hla <;> omega
  have hof : (Int32.ofNat lit.natAbs).toInt = lit.natAbs := by
    exact Int32.toInt_ofNat_of_lt (by omega)
  unfold LitTrue at ht ⊢
  rw [← ht]
  unfold fastModel modelOf
  have hl := ld_sim (abs L s M fa sl) rfl hB.size (Int32.ofNat lit.natAbs)
  rw [hof] at hl
  have h0 : (abs L s M fa sl).model + (lit.natAbs : Int) = lit.natAbs := by
    show (0 : Int) + _ = _; omega
  rw [h0, ← hl]
  by_cases hz : ld s.db (Int32.ofNat lit.natAbs) = 0
  · rw [hz]; rfl
  · have : (ld s.db (Int32.ofNat lit.natAbs)).toInt ≠ 0 := fun h => hz (Int32.toInt_inj.mp (by rw [h]; rfl))
    rw [bne_iff_ne.mpr hz, bne_iff_ne.mpr this]

/-- The faithful termination measure of a fast state. -/
def frank (L : Lay) (s : St) : Nat × Nat × Nat := rank (abs L s 0 0 0)

/-- The decision from a `Settled` state with a cursor: the faithful `decide_spec`. -/
theorem fdecide_cases {input : Input} {L : Lay} {s : St} {fa sl : Int} {db : Records} {vs : List Int}
    {d : Cell} (hB : Bounds L s) (h : Settled input (abs L s (memoryBound input) fa sl) db vs)
    (c : Cursor (abs L s (memoryBound input) fa sl) vs d.toInt) :
    match fdecide L s d with
    | .finished out => FCorrect input L out
    | .running s' d' => FInv input L s' d' ∧
        trailLen (abs L s' 0 0 0) = trailLen (abs L s 0 0 0) + 1 ∧
        s'.nLemmas = s.nLemmas ∧ s'.maxLemmas = s.maxLemmas := by
  obtain ⟨hN1, hN2⟩ := hB.nVars
  have hl := h.core.layout; have hnum := hl.num; have ht := h.core.trail
  have eN : (abs L s (memoryBound input) fa sl).nVars = L.nVars.toInt := rfl
  have hz : ((0 : Cell)).toInt = 0 := rfl
  unfold fdecide
  rcases decideLoop_spec h hN2 hB.size _ d rfl c with ⟨h0, all⟩ | ⟨k, hk, hv, before, free⟩
  · rw [if_pos (by simp only [beq_iff_eq]; exact Int32.toInt_inj.mp (by rw [h0, hz]))]
    exact Or.inr (Or.inl ⟨rfl, sat_fast h.core.valid hB h.core.nVars (sat_of_assigned h all)⟩)
  · have hmem := (h.core.order.mem_iff).mp (List.getElem_mem hk)
    rw [hv] at hmem
    rw [if_neg (by simp only [beq_iff_eq]; intro h'; rw [h', hz] at hmem; omega)]
    have hspec := assignDecision_spec h hk before (hv ▸ free)
    have hA : 0 ≤ s.assigned.toInt ∧ s.assigned.toInt < 2 ^ 30 := by
      have h1 := ht.forced_le; have h2 := ht.processed_le; have h3 := ht.assigned_le
      have h4 := ht.len_le; simp only [trailLen] at h4
      have : (abs L s (memoryBound input) fa sl).assigned = s.assigned.toInt := rfl
      omega
    rw [hv, assignDecision_sim hB.size hN2 ⟨hnum.2.2.2.2.2.2.1, hnum.2.2.2.2.1, hN1⟩ hmem hA] at hspec
    obtain ⟨inv', hlen, hnl, hml⟩ := hspec
    refine ⟨⟨⟨st_size (st_size (st_size hB.size _ _) _ _) _ _, hB.nVars, hB.memUsed, hB.maxLemmas⟩,
      fa, sl, inv'⟩, hlen, ?_, ?_⟩
    · exact Int32.toInt_inj.mp hnl
    · exact Int32.toInt_inj.mp hml

/-- Turns the decision's contract into the step's, given the rank decrease. -/
theorem decide_rank {input : Input} {L : Lay} {s0 s : St} {R : FProgress}
    (h : match (generalizing := false) R with
      | .finished out => FCorrect input L out
      | .running s' d' => FInv input L s' d' ∧ trailLen (abs L s' 0 0 0) = trailLen (abs L s 0 0 0) + 1 ∧
          s'.nLemmas = s.nLemmas ∧ s'.maxLemmas = s.maxLemmas)
    (hr : ∀ s' d', FInv input L s' d' → trailLen (abs L s' 0 0 0) = trailLen (abs L s 0 0 0) + 1 →
      s'.nLemmas = s.nLemmas → s'.maxLemmas = s.maxLemmas → RankLT (frank L s') (frank L s0)) :
    match (generalizing := false) R with
    | .finished out => FCorrect input L out
    | .running s' d' => FInv input L s' d' ∧ RankLT (frank L s') (frank L s0) := by
  cases R with
  | finished out => exact h
  | running s' d' => exact ⟨h.1, hr s' d' h.1 h.2.1 h.2.2.1 h.2.2.2⟩

/-- The trail of a fast state with the invariant fits in `nVars`. -/
theorem FInv.len_le {input : Input} {L : Lay} {s : St} {d : Cell} (h : FInv input L s d) :
    trailLen (abs L s 0 0 0) ≤ (abs L s 0 0 0).nVars.toNat := by
  obtain ⟨-, fa, sl, db, vs, core, -⟩ := h
  exact core.trail.len_le

/-! ### One step -/

/-- Everything about one fast step: the faithful `step_cases`, with out of memory as an
outcome. -/
theorem fstep_cases (hconf : ConflictSpec) {input : Input} {L : Lay} {s : St} {d : Cell}
    (inv : FInv input L s d) :
    match fstep L s d with
    | .finished out => FCorrect input L out
    | .running s' d' => FInv input L s' d' ∧ RankLT (frank L s') (frank L s) := by
  obtain ⟨hB, fa, sl, inv⟩ := inv
  have hp := propagate_fast hconf hB inv
  obtain ⟨db0, vs0, core0, -, -, -⟩ := inv
  have hnl0 : 0 ≤ s.nLemmas.toInt := nLemmas_nonneg core0.database
  have hml0 : 0 ≤ s.maxLemmas.toInt := core0.maxLemmas
  obtain ⟨hN1, hN2⟩ := hB.nVars
  unfold fstep
  generalize propagate L s = P at hp
  obtain ⟨s1, r⟩ := P
  dsimp only at hp ⊢
  rcases hp with rfl | ⟨rfl, unsat⟩ | ⟨rfl, hB1, fa1, sl1, hml, hcase⟩
  · rw [if_pos (by decide)]; exact Or.inl rfl
  · rw [if_pos (by decide)]; exact Or.inr (Or.inr ⟨rfl, unsat⟩)
  rw [if_neg (by decide)]
  have hml1 : s1.maxLemmas.toInt = s.maxLemmas.toInt := hml
  rcases hcase with ⟨hnl, hlen, db1, vs1, hset, hcur⟩ | ⟨hlt, db1, vs1, hset⟩
  · -- no conflict: decide from the same cursor
    have hnl1 : s1.nLemmas.toInt = s.nLemmas.toInt := hnl
    rw [fpick, if_neg (fun h => by have := Int32.lt_iff_toInt_lt.mp h; omega)]
    dsimp only
    refine decide_rank (fdecide_cases hB1 hset hcur) fun s' d' hinv hlen' hnl' hml' => ?_
    exact rank_lt_trail rfl (by show s'.maxLemmas.toInt = s.maxLemmas.toInt; rw [hml', hml1])
      (by show s'.nLemmas.toInt = s.nLemmas.toInt; rw [hnl', hnl1])
      (by rw [hlen']; exact Nat.lt_succ_of_le hlen) hinv.len_le
  · -- a conflict: back to `head`, maybe a restart and a `reduceDB`
    have hlt1 : s.nLemmas.toInt < s1.nLemmas.toInt := hlt
    have hb1 : s1.nLemmas.toInt.toNat ≤ clauseBound L.nVars.toInt := nLemmas_le_bound hset.core.database
    rw [fpick, if_pos (Int32.lt_iff_toInt_lt.mpr hlt1)]
    by_cases hf : s1.fast > s1.slow / 100 * 125
    · rw [if_pos hf]
      dsimp only
      obtain ⟨hR, hroot, hsz2, D, hRe⟩ := restart_fast (s := { s1 with fast := s1.slow / 100 * 125 })
        (M := memoryBound input) (fa := fa1) (sl := sl1) hset hN2 hB1.size
      generalize hs2 : restart L { s1 with fast := s1.slow / 100 * 125 } = s2 at hR hroot hsz2 hRe ⊢
      have hB2 : Bounds L s2 :=
        ⟨hsz2, hB1.nVars, by rw [hRe]; exact hB1.memUsed, by rw [hRe]; exact hB1.maxLemmas⟩
      have e2 : s2.nLemmas = s1.nLemmas ∧ s2.maxLemmas = s1.maxLemmas ∧ s2.head = s1.head := by
        rw [hRe]; exact ⟨rfl, rfl, rfl⟩
      by_cases hm : s2.nLemmas > s2.maxLemmas
      · rw [if_pos hm]
        have more : s2.maxLemmas.toInt < s2.nLemmas.toInt := Int32.lt_iff_toInt_lt.mp hm
        obtain ⟨hB3, db3, hset3, hmax3, hhead3⟩ := reduceDB_fast 6 hB2 hR hroot more
        have hcur3 : Cursor (abs L (reduceDB L s2 6) (memoryBound input) fa1 sl1) vs1 s2.head.toInt := by
          have := cursor_head hset3.core.order; rw [← hhead3]; exact this
        refine decide_rank (fdecide_cases hB3 hset3 hcur3) fun s' d' hinv hlen' hnl' hml' => ?_
        have hm' : s'.maxLemmas.toInt = (reduceDB L s2 6).maxLemmas.toInt := by rw [hml']
        exact rank_lt_max rfl (by show s.maxLemmas.toInt < s'.maxLemmas.toInt; rw [hm', ← hml1, ← e2.2.1]; exact hmax3)
          hml0 (by show s.maxLemmas.toInt.toNat < clauseBound L.nVars.toInt; rw [e2.1, e2.2.1] at more; omega)
      · rw [if_neg hm]
        have hcur2 : Cursor (abs L s2 (memoryBound input) fa1 sl1) vs1 s2.head.toInt := cursor_head hR.core.order
        refine decide_rank (fdecide_cases hB2 hR hcur2) fun s' d' hinv hlen' hnl' hml' => ?_
        exact rank_lt_lemmas rfl (by show s'.maxLemmas.toInt = s.maxLemmas.toInt; rw [hml', e2.2.1, hml1])
          (by show s.nLemmas.toInt < s'.nLemmas.toInt; rw [hnl', e2.1]; exact hlt1) hnl0
          (by show s'.nLemmas.toInt.toNat ≤ clauseBound L.nVars.toInt; rw [hnl', e2.1]; exact hb1)
    · rw [if_neg hf]
      dsimp only
      have hcur1 : Cursor (abs L s1 (memoryBound input) fa1 sl1) vs1 s1.head.toInt := cursor_head hset.core.order
      refine decide_rank (fdecide_cases hB1 hset hcur1) fun s' d' hinv hlen' hnl' hml' => ?_
      exact rank_lt_lemmas rfl (by show s'.maxLemmas.toInt = s.maxLemmas.toInt; rw [hml', hml1])
        (by show s.nLemmas.toInt < s'.nLemmas.toInt; rw [hnl']; exact hlt1) hnl0
        (by show s'.nLemmas.toInt.toNat ≤ clauseBound L.nVars.toInt; rw [hnl']; exact hb1)

/-! ### The loop as a whole -/

/-- `FRunsTo L s d out`: from `(s, d)`, finitely many fast steps reach `finished out`. -/
inductive FRunsTo (L : Lay) : St → Cell → St × UInt8 → Prop
  | finished {s d out} : fstep L s d = .finished out → FRunsTo L s d out
  | running {s d s' d' out} : fstep L s d = .running s' d' → FRunsTo L s' d' out → FRunsTo L s d out

/-- A finishing loop computes `run`'s value. -/
theorem FRunsTo.run_eq {L : Lay} {s : St} {d : Cell} {out : St × UInt8} (h : FRunsTo L s d out) :
    run L s d = out := by
  induction h with
  | finished hs => rw [Verification.run_eq, hs]
  | running hs _ ih => rw [Verification.run_eq, hs]; exact ih

/-- From the invariant, the fast loop finishes, with a correct answer (or out of memory):
well-founded induction on the faithful `rank`, using `fstep_cases`. -/
theorem frun_correct (hconf : ConflictSpec) {input : Input} {L : Lay} :
    ∀ s d, FInv input L s d → ∃ out, FRunsTo L s d out ∧ FCorrect input L out := by
  suffices key : ∀ x s d, frank L s = x → FInv input L s d → ∃ out, FRunsTo L s d out ∧ FCorrect input L out from
    fun s d => key _ s d rfl
  intro x
  refine rankLT_wf.induction (C := fun x => ∀ s d, frank L s = x → FInv input L s d →
    ∃ out, FRunsTo L s d out ∧ FCorrect input L out) x ?_
  intro x ih s d hx inv
  have hc := fstep_cases hconf inv
  match hs : fstep L s d with
  | .finished out => rw [hs] at hc; exact ⟨out, .finished hs, hc⟩
  | .running s' d' =>
    rw [hs] at hc
    obtain ⟨out, hrun, hpost⟩ := ih _ (hx ▸ hc.2) s' d' rfl hc.1
    exact ⟨out, .running hs hrun, hpost⟩

end MicrosatLean.Fast.Verification
