import MicrosatLean.Fast.Verification.ParseInit

/-!
# `parse`'s clause step for any `addClause` result

The faithful lemmas `ParseCore.after_add_facts`, `after_add`, `after_assign` and
`unit_reads` (`Faithful/Verification/ParseStep.lean`) are stated about the faithful
`addClause S S.buffer size 1`, but their proofs only use its postcondition
`AddClausePost`. Here they are restated (same proofs) for any result `r` meeting
`AddClausePost`, which the fast `addClause` does (`addClause_post`).

During `parse` the faithful state of a fast state is `pabs`: the abstraction with
`nClauses` as `initCDCL` sets it (`InitState` fixes it; no invariant reads it).
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-! ### `nClauses` is never read -/

/-- The faithful state of a fast state during `parse`. -/
def pabs (input : Input) (L : Lay) (s : St) : solver :=
  { abs L s (memoryBound input) 0 0 with nClauses := input.nClauses }

/-- `Inv` does not read `nClauses`. -/
theorem Inv.withNClauses {input : Input} {S : solver} {d : Int} (h : Inv input S d) (m : Int) :
    Inv input { S with nClauses := m } d := by
  obtain ⟨db, vs, ⟨valid, nv, mem, ml, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
    ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩, root,
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩, watches, reasons, units, ⟨o1, o2, o3, o4⟩⟩,
    watched, mode, cursor⟩ := h
  exact ⟨db, vs, ⟨valid, nv, mem, ml, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
    ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩, root,
    ⟨d1.frame fun _ _ _ _ => rfl, d2.frame fun _ _ _ _ => rfl, d3, d4, d5, d6, d7, d8, d9, d10⟩,
    fun lit hl => by
      obtain ⟨links, hlinks, hnd, hm⟩ := watches lit hl
      exact ⟨links, hlinks.frame fun _ _ => rfl, hnd, hm⟩,
    reasons, units, ⟨o1.congr fun _ _ => rfl, o2, o3, o4⟩⟩, watched, mode, cursor⟩

/-- A store commutes with setting `nClauses`. -/
theorem st_withNClauses (A : solver) (m p v : Int) :
    ({ A with nClauses := m } : solver).st p v = { A.st p v with nClauses := m } := by
  unfold solver.st
  by_cases hp : p < 0
  · simp only [hp, if_true, panicWith_eq]
  · simp only [hp, if_false]
    by_cases hlt : p.toNat < A.DB.size
    · simp only [hlt, dif_pos]
    · simp only [hlt, dif_neg, not_false_eq_true]

/-- `AddClausePost` does not read `nClauses`. -/
theorem AddClausePost.withNClauses {S T : solver} {Ls : List Int} {size irr c : Int} (m : Int)
    (h : AddClausePost S Ls size irr (T, c)) :
    AddClausePost { S with nClauses := m } Ls size irr ({ T with nClauses := m }, c) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, DB, h7⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, DB, ?_⟩
  simp only at h7 ⊢
  rw [h7]; rfl

/-! ### The faithful clause step, for any `addClause` result -/

/-- `ParseCore.after_add_facts` for any `r` meeting `AddClausePost`. -/
theorem ParseCore.after_add_facts' {input : Input} {S : solver} {k : Nat}
    (hk : k < input.clauses.size) {r : solver × Int}
    (post : AddClausePost S input.clauses[k].toList input.clauses[k].size 1 r) :
    (∃ DB, r.1 = extended S DB (S.mem_used + 3 + input.clauses[k].size) S.assigned) ∧
    ClauseAt r.1 (S.mem_used + 2) input.clauses[k].toList ∧ r.2 = S.mem_used + 2 ∧
    (∀ q, 0 ≤ q → q < S.mem_used + 2 → r.1.ld q = afterWatches S input.clauses[k].toList q) := by
  obtain ⟨hc, hmu, hlits, hzero, hbelow, habove, ⟨DB, hDB⟩⟩ := post
  refine ⟨⟨DB, ?_⟩, ⟨fun i hi => ?_, ?_⟩, hc, fun q hq hlt => hbelow q hq (by rw [hc]; exact hlt)⟩
  · rw [hDB]; apply solver.ext <;> first | rfl | (simp [added, extended]; omega) | simp [added, extended]
  · have := hlits i hi; rw [hc] at this; exact this
  · have := hzero; rw [hc] at this; simpa using this

/-- `ParseCore.after_add` for any `r` meeting `AddClausePost`. -/
theorem ParseCore.after_add' {input : Input} {S0 S : solver} {k : Nat} (valid : input.Valid)
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hk : k < input.clauses.size) {r : solver × Int}
    (post : AddClausePost S input.clauses[k].toList input.clauses[k].size 1 r)
    (hne : input.clauses[k].size ≠ 0)
    (hold : input.clauses[k].size = 1 → ∃ i < trailLen S, trailAt S i = - input.clauses[k][0]!) :
    ParseCore input S0 r.1 (k + 1) := by
  obtain ⟨⟨DB, hT⟩, hrec, hc, hbelow⟩ := ParseCore.after_add_facts' hk post
  apply h.extend valid h0 hk hne false ⟨DB, by simpa using hT⟩ hrec
  · intro h2
    have hl : 1 < input.clauses[k].toList.length := by simp; omega
    have e0 := toList_getElem! input.clauses[k] 0 (by omega)
    have e1 := toList_getElem! input.clauses[k] 1 (by omega)
    have hbase : clausesAt S.nVars ≤ S.mem_used := by
      have := h.records.bounds.1; rw [(h.ptrs h0).1]; exact this
    have hfirst := (h.ptrs h0).2.2.1
    have hN := (h.ptrs h0).1
    have hlit : ∀ i < 2, -S.nVars ≤ input.clauses[k][i]! ∧ input.clauses[k][i]! ≤ S.nVars ∧
        input.clauses[k][i]! ≠ 0 := by
      intro i hi
      have hm : input.clauses[k][i]! ∈ input.clauses[k].toList := by
        rw [getElem!_pos input.clauses[k] i (by omega)]; simp
      have := valid.lit_range _ (Array.getElem_mem hk) _ (by simpa using hm)
      have hv : input.nVars ≤ S.nVars := by rw [hN, h0.nVars]; unfold varsOf; split <;> omega
      rcases abs_cases input.clauses[k][i]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    have hd : input.clauses[k][0]! ≠ input.clauses[k][1]! := by
      have hnodup := valid.no_repeated_lit _ (Array.getElem_mem hk)
      have := (List.pairwise_iff_getElem.mp hnodup) 0 1 (by simp; omega) (by simp; omega) (by omega)
      rw [← e0, ← e1, getElem!_pos input.clauses[k].toList 0 (by simp; omega),
        getElem!_pos input.clauses[k].toList 1 (by simp; omega)]
      exact this
    have h0' := hlit 0 (by omega); have h1' := hlit 1 (by omega)
    have hF : S.first = 9 * S.nVars + 6 := by rw [hfirst, hN]; rfl
    simp only [clausesAt] at hbase
    rw [hbelow _ (by omega) (by omega), hbelow _ (by omega) (by omega), hbelow _ (by omega) (by omega),
      hbelow _ (by omega) (by omega)]
    unfold afterWatches
    simp only [hl, if_true, e0, e1]
    refine ⟨?_, ?_, ?_, ?_⟩
    all_goals (repeat' split)
    all_goals first | rfl | trivial | omega
  · intro hb; exact absurd hb (by decide)
  · intro _ h1; exact hold h1
  · intro q hq hlt hne _
    rw [hbelow q hq (by omega)]
    apply afterWatches_other hlt
    intro hl
    have h2 : 2 ≤ input.clauses[k].size := by simp at hl; omega
    rw [toList_getElem! _ 0 (by omega), toList_getElem! _ 1 (by omega)]
    exact hne h2

/-- `ParseCore.after_assign` for any `r` meeting `AddClausePost`. -/
theorem ParseCore.after_assign' {input : Input} {S0 S : solver} {k : Nat} (valid : input.Valid)
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hk : k < input.clauses.size) {r : solver × Int}
    (post : AddClausePost S input.clauses[k].toList input.clauses[k].size 1 r)
    (hsize : input.clauses[k].size = 1)
    (hf1 : flag S input.clauses[k][0]! = 0) (hf2 : flag S (- input.clauses[k][0]!) = 0) :
    ParseCore input S0 (MicrosatLean.Faithful.assign r.1 r.2 1) (k + 1) := by
  obtain ⟨⟨DB, hR⟩, hrec, hc, hbelow⟩ := ParseCore.after_add_facts' hk post
  obtain ⟨hnv, hb, hfirst, hfalse, hmodel, hreason, hstack, hprev, hnext, hnl, hmm⟩ := h.ptrs h0
  have hN : 1 ≤ S0.nVars := by rw [h0.nVars]; exact varsOf_pos _
  have hbase : clausesAt S0.nVars ≤ S.mem_used := h.records.bounds.1
  have hA : 5 * S0.nVars + 4 ≤ S.assigned ∧ S.assigned ≤ 5 * S0.nVars + 4 + S0.nVars := by
    have h1 := h.trail.1; have h2 := h.trail.2.1
    simp only [trailLen, hstack] at h2; simp only [stackAt] at h1 h2; omega
  -- the unit literal `l = clause[0]`, read back from its record
  have hl : r.1.ld r.2 = input.clauses[k][0]! := by
    rw [hc]
    have := hrec.1 0 (by simp; omega)
    simp only [Int.cast_ofNat_Int, Int.add_zero] at this
    rw [this, ← toList_getElem! input.clauses[k] 0 (by omega),
      getElem!_pos input.clauses[k].toList 0 (by simp; omega)]
  have hm : input.clauses[k][0]! ∈ input.clauses[k].toList := by
    rw [getElem!_pos input.clauses[k] 0 (by omega)]; simp
  have hlit := valid.lit_range _ (Array.getElem_mem hk) _ (by simpa using hm)
  have hv : input.nVars ≤ S0.nVars := by rw [h0.nVars]; unfold varsOf; split <;> omega
  have hlr : input.clauses[k][0]! ≠ 0 ∧ -S0.nVars ≤ input.clauses[k][0]! ∧ input.clauses[k][0]! ≤ S0.nVars := by
    rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have ha : 0 ≤ MicrosatLean.Faithful.abs input.clauses[k][0]! ∧
      MicrosatLean.Faithful.abs input.clauses[k][0]! ≤ S0.nVars := by
    rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hRf : r.1.false = S.false ∧ r.1.model = S.model ∧ r.1.reason = S.reason ∧
      r.1.assigned = S.assigned ∧ r.1.first = S.first := by
    rw [hR]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- the cells `assign` writes (C:44–47)
  have hcell : ∀ q, 0 ≤ q → (MicrosatLean.Faithful.assign r.1 r.2 1).ld q =
      if q = S.model + MicrosatLean.Faithful.abs input.clauses[k][0]! then
        (if input.clauses[k][0]! > 0 then 1 else 0)
      else if q = S.reason + MicrosatLean.Faithful.abs input.clauses[k][0]! then 1 + r.2
      else if q = S.assigned then - input.clauses[k][0]!
      else if q = S.false + - input.clauses[k][0]! then MicrosatLean.Faithful.IMPLIED
      else r.1.ld q := by
    intro q hq
    rw [assign_ld r.1 r.2 1 hq (by rw [hRf.1, hl, hfalse]; simp only [falseAt]; omega)
      (by rw [hRf.2.2.2.1]; omega) (by rw [hRf.2.2.1, hl, hreason]; simp only [reasonAt]; omega)
      (by rw [hRf.2.1, hl, hmodel]; simp only [modelAt]; omega)]
    simp only [hRf, hl]
    rfl
  have eM : S.model = 0 := by rw [hmodel]; rfl
  have eR : S.reason = 4 * S0.nVars + 3 := by rw [hreason]; rfl
  have eF : S.false = 7 * S0.nVars + 5 := by rw [hfalse]; rfl
  have eB : 10 * S0.nVars + 8 ≤ S.mem_used := by have := hbase; simp only [clausesAt] at this; omega
  apply h.extend valid h0 hk (by omega) true
  · obtain ⟨DB', hA'⟩ := assign_fields r.1 r.2 1
    refine ⟨DB', ?_⟩
    rw [hA', hR]
    apply solver.ext <;> first | rfl | (simp [extended]; omega) | simp [extended]
  · refine ⟨fun i hi => ?_, ?_⟩
    · rw [hcell _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hrec.1 i hi
    · rw [hcell _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      exact hrec.2
  · intro h2; omega
  · intro _
    refine ⟨hsize, hf1, hf2, ?_, ?_, ?_, ?_⟩
    · rw [hcell _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    · rw [hcell _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    · rw [hcell _ (by omega), if_neg (by omega), if_pos rfl, hc]
    · rw [hcell _ (by omega), if_pos rfl]
  · intro hb; exact absurd hb (by decide)
  · intro q hq hlt _ hne
    obtain ⟨n1, n2, n3, n4⟩ := hne rfl
    rw [hcell q hq, if_neg n4, if_neg n3, if_neg n1, if_neg n2, hbelow q hq (by omega)]
    exact afterWatches_other hlt fun hl' => by simp at hl'; omega

/-- `ParseCore.unit_reads` for any `r` meeting `AddClausePost`. -/
theorem ParseCore.unit_reads' {input : Input} {S0 S : solver} {k : Nat}
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hk : k < input.clauses.size) {r : solver × Int}
    (post : AddClausePost S input.clauses[k].toList input.clauses[k].size 1 r)
    (hsize : input.clauses[k].size = 1) :
    r.1.ld r.2 = input.clauses[k][0]! ∧
      ∀ lit, InRange S0.nVars lit → r.1.ld (r.1.false + lit) = flag S lit := by
  obtain ⟨⟨DB, hR⟩, hrec, hc, hbelow⟩ := ParseCore.after_add_facts' hk post
  obtain ⟨hnv, hb, hfirst, hfalse, -⟩ := h.ptrs h0
  have hbase : clausesAt S0.nVars ≤ S.mem_used := h.records.bounds.1
  have hN : 1 ≤ S0.nVars := by rw [h0.nVars]; exact varsOf_pos _
  refine ⟨?_, fun lit hlit => ?_⟩
  · rw [hc]
    have := hrec.1 0 (by simp; omega)
    simp only [Int.cast_ofNat_Int, Int.add_zero] at this
    rw [this, ← toList_getElem! input.clauses[k] 0 (by omega),
      getElem!_pos input.clauses[k].toList 0 (by simp; omega)]
  · have hl := inRange_iff.mp hlit
    have hrf : r.1.false = S.false := by rw [hR]; rfl
    rw [hrf, hbelow _ (by rw [hfalse]; simp only [falseAt]; omega)
      (by rw [hfalse]; simp only [falseAt, clausesAt] at hbase ⊢; omega)]
    exact afterWatches_other (by rw [hfalse]; simp only [falseAt, clausesAt] at hbase ⊢; omega)
      fun hl' => by simp at hl'; omega

end MicrosatLean.Fast.Verification
