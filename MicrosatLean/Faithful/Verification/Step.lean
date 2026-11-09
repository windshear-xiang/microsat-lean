import MicrosatLean.Faithful.Verification.Propagate
import MicrosatLean.Faithful.Verification.Restart
import MicrosatLean.Faithful.Verification.ReduceDB
import MicrosatLean.Faithful.Verification.Decide
import MicrosatLean.Faithful.Verification.LemmaCount

/-!
# One iteration of `solve`'s main loop

`step` (C:163–179) is `propagate`, then after a conflict possibly `restart` and
`reduceDB` (`afterConflict`), then the decision (`scan`, `assignDecision`). The three
facts `Main.lean` needs follow from the contracts of these parts.
-/

namespace MicrosatLean.Faithful.Verification

/-- C:167–172 after a conflict: restart when the fast average exceeds the slow one,
and then reduce the database when it holds too many lemmas. -/
def afterConflict (S : solver) : solver :=
  if S.fast > (S.slow.tdiv 100) * 125 then
    let S := restart { S with res := 0, fast := (S.slow.tdiv 100) * 125 }
    if S.nLemmas > S.maxLemmas then reduceDB S 6 else S
  else S

/-- `step` is `propagate`, then `afterConflict` if lemmas were learned (resetting the
cursor to `head`, C:166), then the decision. -/
theorem step_eq (S : solver) (d : CInt) :
    step S d =
      match propagate S with
      | (S1, r) =>
        if r == UNSAT then .finished S1 UNSAT
        else if S1.nLemmas > S.nLemmas then assignDecision (afterConflict S1) (scan (afterConflict S1) S1.head)
        else assignDecision S1 (scan S1 d) := by
  unfold step
  dsimp only
  generalize propagate S = P
  obtain ⟨S1, r⟩ := P
  dsimp only
  by_cases hr : (r == UNSAT) = true
  · simp [hr]
  · simp only [hr, Bool.false_eq_true, if_false]
    by_cases hl : S1.nLemmas > S.nLemmas
    · simp only [hl, if_true]
      unfold afterConflict
      by_cases hf : S1.fast > (S1.slow.tdiv 100) * 125
      · simp only [hf, if_true]
        by_cases hm : (restart { S1 with res := 0, fast := (S1.slow.tdiv 100) * 125 }).nLemmas >
            (restart { S1 with res := 0, fast := (S1.slow.tdiv 100) * 125 }).maxLemmas
        · simp only [hm, if_true]; rfl
        · simp only [hm, if_false]; rfl
      · simp only [hf, if_false]; rfl
    · simp only [hl, if_false]; rfl

/-- The cursor can always restart at `head` (C:166). -/
theorem cursor_head {S : solver} {vs : List CInt} (h : OrderList S vs) : Cursor S vs S.head := by
  refine ⟨0, Nat.zero_le _, ?_, fun j _ hj => absurd hj (Nat.not_lt_zero j)⟩
  have hc := h.chain
  cases vs with
  | nil => simp only [PrevChain] at hc; simp [hc]
  | cons w ws => simp only [PrevChain] at hc; simp [hc.1]

/-- After a conflict: `afterConflict` keeps `Settled` and `head`; either `maxLemmas`
and `nLemmas` are unchanged, or `reduceDB` ran and raised `maxLemmas` past its old
value, which was below `nLemmas` (C:171). -/
theorem afterConflict_spec {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Settled input S db vs) :
    ∃ db', Settled input (afterConflict S) db' vs ∧ (afterConflict S).head = S.head ∧
      (((afterConflict S).maxLemmas = S.maxLemmas ∧ (afterConflict S).nLemmas = S.nLemmas) ∨
        (S.maxLemmas < (afterConflict S).maxLemmas ∧ S.maxLemmas < S.nLemmas)) := by
  unfold afterConflict
  split
  · have h' := h.withStats 0 ((S.slow.tdiv 100) * 125)
    obtain ⟨hR, hroot, DB, hRe⟩ := restart_spec h'
    have fR : (restart { S with res := 0, fast := (S.slow.tdiv 100) * 125 }).maxLemmas = S.maxLemmas ∧
        (restart { S with res := 0, fast := (S.slow.tdiv 100) * 125 }).nLemmas = S.nLemmas ∧
        (restart { S with res := 0, fast := (S.slow.tdiv 100) * 125 }).head = S.head := by
      rw [hRe]; exact ⟨rfl, rfl, rfl⟩
    dsimp only
    split
    · rename_i more
      obtain ⟨db', hD, hmax, hhead⟩ := reduceDB_spec 6 hR hroot more
      refine ⟨db', hD, by rw [hhead, fR.2.2], Or.inr ⟨?_, ?_⟩⟩
      · have := hmax; rw [fR.1] at this; exact this
      · have := more; rw [fR.1, fR.2.1] at this; exact this
    · exact ⟨db, hR, fR.2.2, Or.inl ⟨fR.1, fR.2.1⟩⟩
  · exact ⟨db, h, rfl, Or.inl ⟨rfl, rfl⟩⟩

/-- The rank decreases when only the trail grows. -/
theorem rank_lt_trail {S S' : solver} (hv : S'.nVars = S.nVars) (hm : S'.maxLemmas = S.maxLemmas)
    (hn : S'.nLemmas = S.nLemmas) (ht : trailLen S < trailLen S') (hle : trailLen S' ≤ S'.nVars.toNat) :
    RankLT (rank S') (rank S) := by
  unfold rank RankLT
  simp only [hv, hm, hn]
  rw [hv] at hle
  exact Prod.Lex.right _ (Prod.Lex.right _ (by omega))

/-- The rank decreases when lemmas are learned (at most `clauseBound` of them). -/
theorem rank_lt_lemmas {S S' : solver} (hv : S'.nVars = S.nVars) (hm : S'.maxLemmas = S.maxLemmas)
    (hn : S.nLemmas < S'.nLemmas) (h0 : 0 ≤ S.nLemmas) (hb : S'.nLemmas.toNat ≤ clauseBound S'.nVars) :
    RankLT (rank S') (rank S) := by
  unfold rank RankLT
  simp only [hv, hm]
  rw [hv] at hb
  exact Prod.Lex.right _ (Prod.Lex.left _ _ (by omega))

/-- The rank decreases when `reduceDB` raises `maxLemmas` from below the bound. -/
theorem rank_lt_max {S S' : solver} (hv : S'.nVars = S.nVars) (hm : S.maxLemmas < S'.maxLemmas)
    (h0 : 0 ≤ S.maxLemmas) (hb : S.maxLemmas.toNat < clauseBound S.nVars) :
    RankLT (rank S') (rank S) := by
  unfold rank RankLT
  simp only [hv]
  exact Prod.Lex.left _ _ (by omega)

/-- `nLemmas` is never negative: it counts the lemma records. -/
theorem nLemmas_nonneg {input : Input} {S : solver} {db : Records} (h : Database input S db) :
    0 ≤ S.nLemmas := by
  rw [h.nLemmas]; omega

/-- Everything about one `step`: a final step answers correctly; a non-final step keeps
the invariant and decreases the rank. The three theorems below are its parts. -/
theorem step_cases {input : Input} {S : solver} {d : CInt} (inv : Inv input S d) :
    match step S d with
    | .finished S' r => CorrectResult input (S', r)
    | .running S' d' => Inv input S' d' ∧ RankLT (rank S') (rank S) := by
  have hp := propagate_spec inv
  obtain ⟨db0, vs0, core0, -, -, -⟩ := inv
  have hnv0 := core0.nVars
  have hnl0 := nLemmas_nonneg core0.database
  rw [step_eq]
  generalize propagate S = P at hp
  obtain ⟨S1, r⟩ := P
  dsimp only at hp ⊢
  rcases hp with ⟨rfl, unsat⟩ | ⟨rfl, hmax, hcase⟩
  · exact Or.inr ⟨rfl, unsat⟩
  · rw [if_neg (by decide)]
    rcases hcase with ⟨hnl, hlen, db1, vs1, set1, cur1⟩ | ⟨hnl, db1, vs1, set1⟩
    · -- no conflict: the decision adds one literal to a trail that did not shrink
      rw [if_neg (by omega)]
      have := decide_spec set1 cur1
      revert this
      cases assignDecision S1 (scan S1 d) with
      | finished S' r => exact id
      | running S' d' =>
        rintro ⟨inv', hl', hn', hm'⟩
        refine ⟨inv', ?_⟩
        obtain ⟨db', vs', core', -⟩ := inv'
        exact rank_lt_trail (by rw [core'.nVars, hnv0]) (by rw [hm', hmax])
          (by rw [hn', hnl]) (by omega) core'.trail.len_le
    · -- a conflict: new lemmas, or a `reduceDB` that raised `maxLemmas`
      rw [if_pos hnl]
      obtain ⟨db2, set2, hhead, hcase2⟩ := afterConflict_spec set1
      have cur2 : Cursor (afterConflict S1) vs1 S1.head := hhead ▸ cursor_head set2.core.order
      have := decide_spec set2 cur2
      revert this
      cases assignDecision (afterConflict S1) (scan (afterConflict S1) S1.head) with
      | finished S' r => exact id
      | running S' d' =>
        rintro ⟨inv', hl', hn', hm'⟩
        refine ⟨inv', ?_⟩
        obtain ⟨db', vs', core', -⟩ := inv'
        have hv : S'.nVars = S.nVars := by rw [core'.nVars, hnv0]
        rcases hcase2 with ⟨hm2, hn2⟩ | ⟨hm2, more⟩
        · exact rank_lt_lemmas hv (by rw [hm', hm2, hmax]) (by rw [hn', hn2]; exact hnl) hnl0
            (nLemmas_le_bound core'.database)
        · have hb := nLemmas_le_bound set1.core.database
          have hv1 : S1.nVars = S.nVars := by rw [set1.core.nVars, hnv0]
          rw [hv1] at hb
          exact rank_lt_max hv (by rw [hm', ← hmax]; exact hm2) core0.maxLemmas (by omega)

/-- A non-final step keeps the invariant. Used for termination and soundness in
`Main.lean`. -/
theorem step_preserves {input : Input} {S S' : solver} {d d' : CInt}
    (inv : Inv input S d) (h : step S d = .running S' d') : Inv input S' d' := by
  have := step_cases inv
  rw [h] at this
  exact this.1

/-- A non-final step decreases the rank: it reduces the database (raising
`maxLemmas`), learns a new lemma, or assigns one more variable. Used for
termination in `Main.lean`. -/
theorem step_decreases {input : Input} {S S' : solver} {d d' : CInt}
    (inv : Inv input S d) (h : step S d = .running S' d') : RankLT (rank S') (rank S) := by
  have := step_cases inv
  rw [h] at this
  exact this.2

/-- A final step answers correctly: SAT when every variable is assigned without a
conflict (the model satisfies the input), UNSAT on a conflict at the root (the input
is unsatisfiable). Used for soundness in `Main.lean`. -/
theorem step_finished {input : Input} {S S' : solver} {d r : CInt}
    (inv : Inv input S d) (h : step S d = .finished S' r) : CorrectResult input (S', r) := by
  have := step_cases inv
  rw [h] at this
  exact this

end MicrosatLean.Faithful.Verification
