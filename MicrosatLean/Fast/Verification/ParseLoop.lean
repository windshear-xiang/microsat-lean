import MicrosatLean.Fast.Verification.ParseStep

/-!
# `parse`'s clause loop of the fast port (C:226–242)

`parseLoop_spec`: by induction on the unread tokens, the fast loop keeps the faithful
`ParseInv` for `pabs` of its state, and ends out of memory, with a correct UNSAT, or with
every clause loaded (`ParseCore`). This follows the faithful `parse_correct`
(`Faithful/Verification/Init.lean`) case by case.
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- A token is `0` or a literal of some clause. -/
theorem mem_tokList {cs : List (Array Int)} {t : Int} (h : t ∈ tokList cs) :
    t = 0 ∨ ∃ c ∈ cs, t ∈ c.toList := by
  induction cs with
  | nil => simp [tokList] at h
  | cons c cs ih =>
    simp only [tokList, List.mem_append, List.mem_cons] at h
    rcases h with h | h | h
    · exact Or.inr ⟨c, List.mem_cons_self, h⟩
    · exact Or.inl h
    · rcases ih h with h | ⟨d, hd, ht⟩
      · exact Or.inl h
      · exact Or.inr ⟨d, List.mem_cons_of_mem _ hd, ht⟩

/-- Every token of a valid input is within `±nVars` (V1). -/
theorem token_range {input : Input} (valid : input.Valid) {t : Int} (h : t ∈ input.tokens.toList) :
    -input.nVars ≤ t ∧ t ≤ input.nVars := by
  rw [tokens_toList] at h
  rcases mem_tokList h with h | ⟨c, hc, ht⟩
  · have := valid.nVars_nonneg; omega
  · have := (valid.lit_range c (by simpa using hc) t (by simpa using ht)).2
    rcases abs_cases t with ⟨_, e⟩ | ⟨_, e⟩ <;> omega

/-- `==` on cells is equality of the numbers. -/
theorem beq_cell {a b : Cell} : (a == b) = true ↔ a.toInt = b.toInt := by
  rw [beq_iff_eq]; exact ⟨fun h => h ▸ rfl, Int32.toInt_inj.mp⟩

/-- `!=` on cells is disequality of the numbers. -/
theorem bne_cell {a b : Cell} : (a != b) = true ↔ a.toInt ≠ b.toInt := by
  rw [bne_iff_ne]; exact not_congr ⟨fun h => h ▸ rfl, Int32.toInt_inj.mp⟩

/-- A literal written to `buffer` (C:241), for `pabs`. -/
theorem pabs_st (input : Input) (L : Lay) (s : St) (hsz : s.db.size ≤ 2 ^ 31) (p v : Cell) :
    pabs input L { s with db := st s.db p v } = (pabs input L s).st p.toInt v.toInt := by
  unfold pabs
  rw [abs_st _ _ _ _ _ hsz]
  exact (st_withNClauses _ _ _ _).symm

/-- The fast `assign` of a unit clause in `parse` (C:239) is the faithful one, for `pabs`. -/
theorem pabs_assign {input : Input} {L : Lay} {s : St} {reason : Cell} (hsz : s.db.size ≤ 2 ^ 31)
    (hL : 0 ≤ L.fls.toInt ∧ L.fls.toInt < 2 ^ 30 ∧ 0 ≤ L.reason.toInt ∧ L.reason.toInt < 2 ^ 30)
    (hr : 0 ≤ reason.toInt ∧ reason.toInt < 2 ^ 30)
    (hlit : -2 ^ 29 ≤ (pabs input L s).ld reason.toInt ∧ (pabs input L s).ld reason.toInt ≤ 2 ^ 29)
    (ha : 0 ≤ s.assigned.toInt ∧ s.assigned.toInt < 2 ^ 30) :
    pabs input L { s with db := assign L s.db s.assigned reason true, assigned := s.assigned + 1 } =
      MicrosatLean.Faithful.assign (pabs input L s) reason.toInt 1 ∧
    (assign L s.db s.assigned reason true).size ≤ 2 ^ 31 := by
  obtain ⟨e, hs⟩ := assign_sim (pabs input L s) rfl hsz rfl rfl rfl hL rfl hr hlit true
  obtain ⟨DB', hA⟩ := assign_fields (pabs input L s) reason.toInt 1
  have e' : (MicrosatLean.Faithful.assign (pabs input L s) reason.toInt 1).DB =
      toDB (assign L s.db s.assigned reason true) := e
  rw [hA] at e' ⊢
  refine ⟨?_, hs⟩
  have h1 : ((1 : Cell)).toInt = 1 := rfl
  apply MicrosatLean.Faithful.solver.ext
  case DB => exact e'.symm
  case assigned =>
    show (s.assigned + 1).toInt = s.assigned.toInt + 1
    rw [toInt_add (by rw [h1]; omega) (by rw [h1]; omega), h1]
  all_goals rfl

/-- What `parseLoop` returns on a valid input: out of memory, a correct UNSAT, or SAT with
every clause loaded. -/
def ParseOut (input : Input) (S0 : solver) (L : Lay) (out : St × UInt8) : Prop :=
  out.2 = OOM ∨ (out.2 = UNSAT ∧ input.Unsat) ∨
    (out.2 = SAT ∧ out.1.db.size ≤ 2 ^ 31 ∧ out.1.memUsed.toInt ≤ 2 ^ 30 ∧
      ParseCore input S0 (pabs input L out.1) input.clauses.size)

/-- The fast `parseLoop` on a valid input, from a state where the faithful `ParseInv` holds
for `pabs` (`k` clauses loaded, `size` literals of clause `k` in `buffer`, the tokens from
`next` unread). -/
theorem parseLoop_spec {input : Input} (valid : input.Valid) (hn : input.nVars ≤ 107374181)
    {S0 : solver} (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (L : Lay) :
    ∀ (m : Nat) (s : St) (next : Nat) (nZeros : Int) (size : Cell) (k : Nat),
      input.tokens.size - next = m → s.db.size ≤ 2 ^ 31 → s.memUsed.toInt ≤ 2 ^ 30 →
      k ≤ input.clauses.size → nZeros = input.clauses.size - k → 0 ≤ size.toInt →
      ParseInv input S0 (pabs input L s) k size.toInt.toNat (input.tokens.toList.drop next) →
      ParseOut input S0 L (parseLoop L s input.tokens next nZeros size) := by
  intro m
  induction m using Nat.strongRecOn with
  | _ m ih =>
  intro s next nZeros size k hm hsz hmu hk hnz hsize hpi
  have hN : S0.nVars = varsOf input.nVars := h0.nVars
  have hN1 : 1 ≤ S0.nVars := by rw [hN]; exact varsOf_pos _
  have hNle : S0.nVars ≤ 107374181 := by rw [hN]; unfold varsOf; split <;> omega
  have hv : input.nVars ≤ S0.nVars := by rw [hN]; unfold varsOf; split <;> omega
  have hv0 := valid.nVars_nonneg
  obtain ⟨hnv, hb, hfirst, hfalse, hmodel, hreason, hstack, -, -, hnl, -⟩ := hpi.1.ptrs h0
  have eN : L.nVars.toInt = S0.nVars := hnv
  have eB : L.buffer.toInt = 3 * S0.nVars + 3 := by
    have : L.buffer.toInt = bufferAt S0.nVars := hb
    rw [this]; simp only [bufferAt]; omega
  have eF : L.fls.toInt = 7 * S0.nVars + 5 := hfalse
  have eFi : L.first.toInt = 9 * S0.nVars + 6 := hfirst
  have eR : L.reason.toInt = 4 * S0.nVars + 3 := hreason
  have eNl : s.nLemmas.toInt = 0 := hnl
  have hbase : 10 * S0.nVars + 8 ≤ s.memUsed.toInt := by
    have := hpi.1.records.bounds.1; simp only [clausesAt] at this; exact this
  rw [parseLoop.eq_1]
  by_cases hpos : nZeros > 0
  · rw [if_pos hpos]
    have hkc : k < input.clauses.size := by omega
    cases hget : input.tokens[next]? with
    | none =>
      exfalso
      have hcur := hpi.2
      unfold Current at hcur
      rw [dif_pos hkc] at hcur
      rw [getElem?_eq_head?_drop, hcur.2.2] at hget
      simp at hget
    | some t =>
      dsimp only [St.take]
      obtain ⟨hlt, hdrop⟩ := token_read hget
      have htr := token_range valid (List.mem_of_mem_drop (i := next) (by rw [hdrop]; exact List.mem_cons_self))
      have htt : (Int32.ofInt t).toInt = t := Int32.toInt_ofInt_of_le (by omega) (by omega)
      rw [hdrop] at hpi
      by_cases ht0 : t = 0
      · -- C:234–240: the end of clause `k`
        subst ht0
        rw [if_pos (by decide)]
        obtain ⟨hkc', hsz_eq, hrest⟩ := hpi.size_eq valid
        have hbuf := hpi.buf hkc' hsz_eq
        have hcs : (input.clauses[k].size : Int) ≤ S0.nVars := by rw [hN]; exact clause_size_le_vars valid hkc
        have hsz' : size.toInt = (input.clauses[k].size : Int) := by omega
        have h3 : ((3 : Cell)).toInt = 3 := rfl
        have hus : (s.memUsed + size).toInt = s.memUsed.toInt + size.toInt := toInt_add (by omega) (by omega)
        have hus3 : (s.memUsed + size + 3).toInt = s.memUsed.toInt + size.toInt + 3 := by
          rw [toInt_add (by rw [hus, h3]; omega) (by rw [hus, h3]; omega), hus, h3]
        -- the literals of clause `k`
        have hlits : ∀ l ∈ input.clauses[k].toList, l ≠ 0 ∧ -S0.nVars ≤ l ∧ l ≤ S0.nVars := by
          intro l hl
          have := valid.lit_range _ (Array.getElem_mem hkc) l (by simpa using hl)
          rcases abs_cases l with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
        by_cases hoom : s.memUsed.toInt + size.toInt + 3 ≤ 2 ^ 30
        · -- C:235: `addClause` (`AddClausePost` for `pabs`)
          have hsrc : ∀ i (h : i < input.clauses[k].toList.length),
              (abs L s (memoryBound input) 0 0).ld (L.buffer.toInt + i) = input.clauses[k].toList[i] := by
            intro i hi
            have := hbuf i (by simpa using hi)
            rw [getElem!_pos input.clauses[k] i (by simpa using hi)] at this
            simp only [Array.getElem_toList]
            exact this
          have hheads : 1 < input.clauses[k].toList.length → ∀ i < 2,
              0 ≤ L.first.toInt + input.clauses[k].toList[i]! ∧
              L.first.toInt + input.clauses[k].toList[i]! < s.memUsed.toInt ∧
              (L.first.toInt + input.clauses[k].toList[i]! < L.buffer.toInt ∨
                L.buffer.toInt + size.toInt ≤ L.first.toInt + input.clauses[k].toList[i]!) := by
            intro hl i hi
            have hm : input.clauses[k].toList[i]! ∈ input.clauses[k].toList := by
              rw [getElem!_pos _ i (by omega)]; exact List.getElem_mem _
            have := hlits _ hm
            omega
          have hdistinct : 1 < input.clauses[k].toList.length →
              input.clauses[k].toList[0]! ≠ input.clauses[k].toList[1]! := by
            intro hl he
            have hnodup := valid.no_repeated_lit _ (Array.getElem_mem hkc)
            have := (List.pairwise_iff_getElem.mp hnodup) 0 1 (by omega) (by omega) (by omega)
            rw [getElem!_pos _ 0 (by omega), getElem!_pos _ 1 (by omega)] at he
            exact this he
          obtain ⟨hcl, hmu', hsz1, post⟩ := addClause_post (L := L) (s := s) (M := memoryBound input)
            (fa := 0) (sl := 0) (src := L.buffer) (size := size) (Ls := input.clauses[k].toList) true hsz
            (by simp; omega) hsrc (by omega) (by omega) (Or.inl (by omega)) hheads hdistinct (by omega) hoom
            ⟨by omega, by omega⟩ (fun l hl => by have := hlits l hl; omega) (by omega)
          generalize hac : addClause L s.db s.memUsed L.buffer size = ac at hcl hmu' hsz1 post ⊢
          obtain ⟨db1, mu1, cl1⟩ := ac
          dsimp only at hcl hmu' hsz1 post ⊢
          have hcl0 : ¬ cl1 < 0 := fun h => by
            have := Int32.lt_iff_toInt_lt.mp h; rw [hcl] at this
            have : ((0 : Cell)).toInt = 0 := rfl
            omega
          rw [if_neg hcl0]
          rw [hsz'] at post
          have post' : AddClausePost (pabs input L s) input.clauses[k].toList input.clauses[k].size 1
              (pabs input L { s with db := db1, memUsed := mu1, memFixed := mu1 }, cl1.toInt) :=
            AddClausePost.withNClauses input.nClauses post
          have hP := hpi.1
          have h0c : ((0 : Cell)).toInt = 0 := rfl
          have h1c : ((1 : Cell)).toInt = 1 := rfl
          have hkey : ∀ x, (ld db1 x).toInt =
              (pabs input L { s with db := db1, memUsed := mu1, memFixed := mu1 }).ld x.toInt :=
            fun x => ld_sim _ rfl hsz1 x
          have hm0 : input.clauses[k].size = 1 → input.clauses[k][0]! ∈ input.clauses[k].toList := by
            intro hc1; rw [getElem!_pos input.clauses[k] 0 (by omega)]; simp
          -- C:236–238: the literal of a unit clause and its flags, read after `addClause`
          have hunit : input.clauses[k].size = 1 →
              (ld db1 cl1).toInt = input.clauses[k][0]! ∧
              (ld db1 (L.fls + ld db1 cl1)).toInt = flag (pabs input L s) input.clauses[k][0]! ∧
              (ld db1 (L.fls - ld db1 cl1)).toInt = flag (pabs input L s) (- input.clauses[k][0]!) := by
            intro hc1
            obtain ⟨hl, hfl⟩ := ParseCore.unit_reads' h0 hP hkc post' hc1
            have hr := hlits _ (hm0 hc1)
            have e0 : (ld db1 cl1).toInt = input.clauses[k][0]! := by rw [hkey]; exact hl
            refine ⟨e0, ?_, ?_⟩
            · rw [hkey, toInt_add (by rw [e0]; omega) (by rw [e0]; omega), e0]
              exact hfl _ (inRange_iff.mpr ⟨hr.1, hr.2.1, hr.2.2⟩)
            · rw [hkey, toInt_sub (by rw [e0]; omega) (by rw [e0]; omega), e0, Int.sub_eq_add_neg]
              exact hfl _ (inRange_iff.mpr ⟨by omega, by omega, by omega⟩)
          by_cases hc : (size == 0 || size == 1 && ld db1 (L.fls + ld db1 cl1) != 0) = true
          · -- C:236: an empty clause, or a unit clause whose literal is false
            rw [if_pos hc]
            refine Or.inr (Or.inl ⟨rfl, ?_⟩)
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_cell, bne_cell, h0c, h1c] at hc
            rcases hc with he | ⟨h1', hne⟩
            · exact unsat_of_empty hkc (by omega)
            · have hc1 : input.clauses[k].size = 1 := by omega
              rw [(hunit hc1).2.1] at hne
              exact hP.unsat_conflict valid h0 hkc hc1 hne
          · rw [if_neg hc]
            simp only [Bool.or_eq_true, Bool.and_eq_true, beq_cell, bne_cell, h0c, h1c, not_or,
              not_and, Decidable.not_not] at hc
            have hne0 : input.clauses[k].size ≠ 0 := by omega
            have hmu1 : mu1.toInt ≤ 2 ^ 30 := by omega
            have hnext : ∀ s' : St, ParseCore input S0 (pabs input L s') (k + 1) →
                s'.db.size ≤ 2 ^ 31 → s'.memUsed.toInt ≤ 2 ^ 30 →
                ParseOut input S0 L (parseLoop L s' input.tokens (next + 1) (nZeros - 1) 0) :=
              fun s' hc' hs' hm' => ih _ (by omega) s' (next + 1) (nZeros - 1) 0 (k + 1) rfl hs' hm'
                (by omega) (by omega) (by decide) ⟨hc', by rw [hrest]; exact current_next input _ k⟩
            by_cases hc2 : (size == 1 && ld db1 (L.fls - ld db1 cl1) == 0) = true
            · -- C:238–239: a new unit clause, assigned at the root
              rw [if_pos hc2]
              simp only [Bool.and_eq_true, beq_cell, h0c, h1c] at hc2
              have hc1 : input.clauses[k].size = 1 := by omega
              obtain ⟨e0, ef1, ef2⟩ := hunit hc1
              have hr := hlits _ (hm0 hc1)
              have hA : 0 ≤ s.assigned.toInt ∧ s.assigned.toInt < 2 ^ 30 := by
                have h1 := hP.trail.1; have h2 := hP.trail.2.1
                simp only [trailLen, hstack] at h2; simp only [stackAt] at h1 h2
                have : (pabs input L s).assigned = s.assigned.toInt := rfl
                omega
              obtain ⟨ea, hsa⟩ := pabs_assign (input := input) (L := L)
                (s := { s with db := db1, memUsed := mu1, memFixed := mu1 }) (reason := cl1) hsz1
                ⟨by omega, by omega, by omega, by omega⟩ ⟨by omega, by omega⟩
                (by rw [← hkey, e0]; omega) hA
              refine hnext _ ?_ hsa hmu1
              have hassign := ParseCore.after_assign' valid h0 hP hkc post' hc1 (by rw [← ef1]; exact hc.2 (by omega))
                (by rw [← ef2]; exact hc2.2)
              dsimp only at hassign
              rw [← ea] at hassign
              exact hassign
            · -- C:235: the clause is kept as it is
              rw [if_neg hc2]
              refine hnext _ ?_ hsz1 hmu1
              have hold : input.clauses[k].size = 1 → ∃ i < trailLen (pabs input L s),
                  trailAt (pabs input L s) i = - input.clauses[k][0]! := by
                intro hc1
                obtain ⟨e0, ef1, ef2⟩ := hunit hc1
                have hr := hlits _ (hm0 hc1)
                simp only [Bool.and_eq_true, beq_cell, h0c, h1c, not_and] at hc2
                have hne : flag (pabs input L s) (- input.clauses[k][0]!) ≠ 0 := by
                  rw [← ef2]; exact hc2 (by omega)
                rw [hP.flags _ (inRange_iff.mpr ⟨by omega, by omega, by omega⟩)] at hne
                split at hne
                · assumption
                · exact absurd rfl hne
              exact ParseCore.after_add' valid h0 hP hkc post' hne0 hold
        · -- C:53–54: out of memory
          have hnone : (addClause L s.db s.memUsed L.buffer size).2.2 = NONE := by
            unfold addClause
            rw [if_pos (Int32.lt_iff_toInt_lt.mpr (by rw [hus3, memMax_toInt]; omega))]
          rw [hnone, if_pos (by decide)]
          exact Or.inl rfl
      · -- C:241: a literal of clause `k`
        rw [if_neg (by rw [beq_cell, htt]; exact ht0)]
        have hcur := hpi.2
        unfold Current at hcur
        rw [dif_pos hkc] at hcur
        have hcs : (input.clauses[k].size : Int) ≤ S0.nVars := by rw [hN]; exact clause_size_le_vars valid hkc
        have hsl : size.toInt.toNat ≤ input.clauses[k].size := hcur.1
        have h1 : ((1 : Cell)).toInt = 1 := rfl
        have hs1 : (size + 1).toInt = size.toInt + 1 := by
          rw [toInt_add (by rw [h1]; omega) (by rw [h1]; omega), h1]
        have haddr : (L.buffer + size).toInt = L.buffer.toInt + size.toInt :=
          toInt_add (by omega) (by omega)
        have hpl := parseInv_lit valid h0 hpi ht0
        have e : (pabs input L s).buffer + (size.toInt.toNat : Int) = (L.buffer + size).toInt := by
          rw [haddr]; show L.buffer.toInt + _ = _; omega
        rw [e, ← htt, ← pabs_st input L s hsz, show size.toInt.toNat + 1 = (size + 1).toInt.toNat by omega] at hpl
        exact ih _ (by omega) _ (next + 1) nZeros (size + 1) k rfl (st_size hsz _ _) hmu hk hnz (by omega) hpl
  · rw [if_neg hpos]
    have hkc : k = input.clauses.size := by omega
    subst hkc
    exact Or.inr (Or.inr ⟨rfl, hsz, hmu, hpi.1⟩)

end MicrosatLean.Fast.Verification
