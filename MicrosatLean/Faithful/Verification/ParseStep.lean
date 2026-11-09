import MicrosatLean.Faithful.Verification.ParseInv
import MicrosatLean.Faithful.Verification.Counting
import MicrosatLean.Faithful.Verification.AddClause

/-!
# `parse` adding one clause (C:234–240)

`ParseCore.extend` covers every outcome of reading a clause's `0` other than UNSAT:
the record is appended, its watches linked if it has two or more literals, and a new
unit clause's literal assigned at the root.
-/

namespace MicrosatLean.Faithful.Verification

/-- The state after adding a record ending at `mu` and possibly assigning: only `DB`,
`mem_used`, `mem_fixed` (C:65) and `assigned` change. -/
def extended (S : solver) (DB : Array CInt) (mu a : CInt) : solver :=
  { S with
    DB := DB
    mem_used := mu
    mem_fixed := mu
    assigned := a }

/-- What `parse` does with clause `k` once its `0` is read, other than reporting
UNSAT. `b` says whether a new unit clause was assigned. The hypotheses describe the
cells written: the record (`hrec`), the watch links (`hw2`), the assignment (`hunit`);
every other cell below the record is unchanged (`hsame`). -/
theorem ParseCore.extend {input : Input} {S0 S T : solver} {k : Nat} (valid : input.Valid)
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hk : k < input.clauses.size) (hne : input.clauses[k].size ≠ 0) (b : Bool)
    (hT : ∃ DB, T = extended S DB (S.mem_used + 3 + input.clauses[k].size)
      (S.assigned + if b then 1 else 0))
    (hrec : ClauseAt T (S.mem_used + 2) input.clauses[k].toList)
    (hw2 : 2 ≤ input.clauses[k].size →
      T.ld (S.first + input.clauses[k][0]!) = S.mem_used ∧
      T.ld S.mem_used = S.ld (S.first + input.clauses[k][0]!) ∧
      T.ld (S.first + input.clauses[k][1]!) = S.mem_used + 1 ∧
      T.ld (S.mem_used + 1) = S.ld (S.first + input.clauses[k][1]!))
    (hunit : b = true → input.clauses[k].size = 1 ∧
      flag S input.clauses[k][0]! = 0 ∧ flag S (- input.clauses[k][0]!) = 0 ∧
      T.ld S.assigned = - input.clauses[k][0]! ∧
      T.ld (S.false + - input.clauses[k][0]!) = IMPLIED ∧
      T.ld (S.reason + abs input.clauses[k][0]!) = 1 + (S.mem_used + 2) ∧
      T.ld (S.model + abs input.clauses[k][0]!) = if input.clauses[k][0]! > 0 then 1 else 0)
    (hold : b = false → input.clauses[k].size = 1 →
      ∃ i < trailLen S, trailAt S i = - input.clauses[k][0]!)
    (hsame : ∀ q, 0 ≤ q → q < S.mem_used →
      (2 ≤ input.clauses[k].size →
        q ≠ S.first + input.clauses[k][0]! ∧ q ≠ S.first + input.clauses[k][1]!) →
      (b = true → q ≠ S.assigned ∧ q ≠ S.false + - input.clauses[k][0]! ∧
        q ≠ S.reason + abs input.clauses[k][0]! ∧ q ≠ S.model + abs input.clauses[k][0]!) →
      T.ld q = S.ld q) :
    ParseCore input S0 T (k + 1) := by
  obtain ⟨DBT, hT⟩ := hT
  obtain ⟨hnv, hbuf, hfirst, hfalse, hmodel, hreason, hstack, hprev, hnext, hnl, hmm⟩ := h.ptrs h0
  have hN : 1 ≤ S0.nVars := by rw [h0.nVars]; exact varsOf_pos _
  have hNv : S0.nVars = varsOf input.nVars := h0.nVars
  have hbase : clausesAt S0.nVars ≤ S.mem_used := h.records.bounds.1
  have hu : S.mem_used = parseEnd (clausesAt S0.nVars) (input.clauses.toList.take k) := by
    obtain ⟨DB, mf, hS⟩ := h.fields; rw [hS]; rfl
  have hTf : T.nVars = S.nVars ∧ T.first = S.first ∧ T.false = S.false ∧ T.model = S.model ∧
      T.reason = S.reason ∧ T.falseStack = S.falseStack ∧
      T.mem_used = S.mem_used + 3 + input.clauses[k].size ∧
      T.mem_fixed = S.mem_used + 3 + input.clauses[k].size ∧
      T.assigned = S.assigned + (if b then 1 else 0) := by
    subst hT; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- the clause: literals of the problem (V1), no repeats (V2), fits (V3)
  have hlits : ∀ l ∈ input.clauses[k].toList, l ≠ 0 ∧ -S0.nVars ≤ l ∧ l ≤ S0.nVars := by
    intro l hl
    have := valid.lit_range _ (Array.getElem_mem hk) l (by simpa using hl)
    have hv : input.nVars ≤ S0.nVars := by rw [hNv]; unfold varsOf; split <;> omega
    rcases abs_cases l with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hcsize : (input.clauses[k].size : CInt) ≤ S0.nVars := by rw [hNv]; exact clause_size_le_vars valid hk
  have hnodup : input.clauses[k].toList.Nodup := valid.no_repeated_lit _ (Array.getElem_mem hk)
  -- where the new record goes
  have htake : input.clauses.toList.take (k + 1) = input.clauses.toList.take k ++ [input.clauses[k]] := by
    rw [List.take_succ, List.getElem?_eq_getElem (by simpa using hk)]; simp
  have hend : parseEnd (clausesAt S0.nVars) (input.clauses.toList.take (k + 1)) =
      S.mem_used + 3 + input.clauses[k].size := by
    rw [htake, parseEnd_append, ← hu]
  have hrecs : parseRecords (clausesAt S0.nVars) (input.clauses.toList.take (k + 1)) =
      parseRecords (clausesAt S0.nVars) (input.clauses.toList.take k) ++
        [(S.mem_used + 2, input.clauses[k].toList)] := by
    rw [htake, parseRecords_append, ← hu]
  -- the cells written below the record lie in `first` (watch heads) or in the trail's
  -- arrays (an assignment); nothing else below the record changes
  have hc0 : 1 ≤ input.clauses[k].size → input.clauses[k][0]! ∈ input.clauses[k].toList := by
    intro h1; rw [getElem!_pos input.clauses[k] 0 (by omega)]; simp
  have hc1 : 2 ≤ input.clauses[k].size → input.clauses[k][1]! ∈ input.clauses[k].toList := by
    intro h1; rw [getElem!_pos input.clauses[k] 1 (by omega)]; simp
  have hb1 : b = true → input.clauses[k].size = 1 := fun hb => (hunit hb).1
  have hsingle : input.clauses[k].size = 1 → input.clauses[k].toList = [input.clauses[k][0]!] := by
    intro h1
    apply List.ext_getElem (by simp [h1])
    intro i hi1 hi2
    have : i = 0 := by simp at hi2; omega
    subst this; simp [getElem!_pos input.clauses[k] 0 (by omega)]
  have low : ∀ q, 0 ≤ q → q < S.mem_used → q < 8 * S0.nVars + 6 →
      (q < 4 * S0.nVars + 3 ∨ (6 * S0.nVars + 5 ≤ q → b = false) ∨ True) →
      (b = true → q ≠ S.assigned ∧ q ≠ S.false + - input.clauses[k][0]! ∧
        q ≠ S.reason + abs input.clauses[k][0]! ∧ q ≠ S.model + abs input.clauses[k][0]!) →
      T.ld q = S.ld q := by
    intro q hq hu' hlow _ hassign
    apply hsame q hq hu' _ hassign
    intro h2
    have := hlits _ (hc0 (by omega)); have := hlits _ (hc1 h2)
    rw [hfirst]; simp only [firstAt]; omega
  have high : ∀ q, clausesAt S0.nVars ≤ q → q < S.mem_used → T.ld q = S.ld q := by
    intro q hq hu'
    apply hsame q (by simp only [clausesAt] at hq; omega) hu'
    · intro h2
      have := hlits _ (hc0 (by omega)); have := hlits _ (hc1 h2)
      rw [hfirst]; simp only [firstAt, clausesAt] at hq ⊢; omega
    · intro hb
      have hl := hlits _ (hc0 (by have := hb1 hb; omega))
      have ha : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
        rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
      have hasg := h.trail.1
      have hlen := h.trail.2.1
      simp only [trailLen, hstack, stackAt] at hlen
      rw [hfalse, hreason, hmodel]
      simp only [falseAt, reasonAt, modelAt, clausesAt, stackAt] at hq hasg ⊢
      omega
  -- the trail: unchanged, plus `-lit` on top when a unit clause is assigned
  have hasg := h.trail.1
  have hlenS := h.trail.2.1
  have hlenS' : (S.assigned - S.falseStack).toNat ≤ S0.nVars.toNat := hlenS
  have hA : 5 * S0.nVars + 4 ≤ S.assigned ∧ S.assigned ≤ 5 * S0.nVars + 4 + S0.nVars := by
    have h1 := hasg; have h2 := hlenS'; rw [hstack] at h2; simp only [stackAt] at h1 h2; omega
  have hlenT : trailLen T = trailLen S + (if b then 1 else 0) := by
    simp only [trailLen, hTf.2.2.2.2.2.2.2.2, hTf.2.2.2.2.2.1, hstack]
    cases b <;> simp <;> omega
  have htrS : ∀ i < trailLen S, trailAt T i = trailAt S i := by
    intro i hi
    simp only [trailAt, hTf.2.2.2.2.2.1]
    simp only [trailLen, hstack] at hi
    rw [hstack]
    apply low _ (by simp only [stackAt]; omega) (by simp only [stackAt, clausesAt] at hbase ⊢; omega)
      (by simp only [stackAt]; omega) (Or.inr (Or.inr trivial))
    intro hb
    have hl := hlits _ (hc0 (by have := hb1 hb; omega))
    have ha : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
      rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    rw [hfalse, hreason, hmodel]
    simp only [falseAt, reasonAt, modelAt, stackAt] at hasg hi ⊢
    have := hA
    omega
  have htrNew : b = true → trailAt T (trailLen S) = - input.clauses[k][0]! := by
    intro hb
    simp only [trailAt, hTf.2.2.2.2.2.1]
    rw [show S.falseStack + (trailLen S : CInt) = S.assigned by
      simp only [trailLen]; rw [hstack]; simp only [stackAt] at hasg ⊢; omega]
    exact (hunit hb).2.2.2.1
  -- a newly assigned literal was unassigned
  have hfree : b = true → ∀ i < trailLen S,
      trailAt S i ≠ input.clauses[k][0]! ∧ trailAt S i ≠ - input.clauses[k][0]! := by
    intro hb i hi
    obtain ⟨_, f1, f2, -⟩ := hunit hb
    have hl := hlits _ (hc0 (by have := hb1 hb; omega))
    have g1 := h.flags _ (inRange_iff.mpr hl)
    have g2 := h.flags (- input.clauses[k][0]!) (inRange_iff.mpr ⟨by omega, by omega, by omega⟩)
    rw [f1] at g1; rw [f2] at g2
    constructor
    · intro he; rw [if_pos ⟨i, hi, he⟩] at g1; exact absurd g1 (by decide)
    · intro he; rw [if_pos ⟨i, hi, he⟩] at g2; exact absurd g2 (by decide)
  have hfreeAbs : b = true → ∀ i < trailLen S,
      abs (trailAt S i) ≠ abs input.clauses[k][0]! := by
    intro hb i hi he
    obtain ⟨n1, n2⟩ := hfree hb i hi
    rcases abs_cases (trailAt S i) with ⟨_, e1⟩ | ⟨_, e1⟩ <;>
      rcases abs_cases input.clauses[k][0]! with ⟨_, e2⟩ | ⟨_, e2⟩ <;> omega
  -- the other cells the trail facts read are unchanged
  have hcellS : ∀ i < trailLen S, ∀ q, (q = S.model + abs (trailAt S i) ∨
      q = S.reason + abs (trailAt S i)) → T.ld q = S.ld q := by
    intro i hi q hq
    have hl := inRange_iff.mp (h.trail.2.2.1 i hi)
    have ha : 0 ≤ abs (trailAt S i) ∧ abs (trailAt S i) ≤ S0.nVars := by
      rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    apply low q (by rw [hmodel, hreason] at hq; simp only [modelAt, reasonAt] at hq; omega)
      (by rw [hmodel, hreason] at hq; simp only [modelAt, reasonAt, clausesAt] at hq hbase; omega)
      (by rw [hmodel, hreason] at hq; simp only [modelAt, reasonAt] at hq; omega) (Or.inr (Or.inr trivial))
    intro hb
    have hl0 := hlits _ (hc0 (by have := hb1 hb; omega))
    have ha0 : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
      rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    have hne := hfreeAbs hb i hi
    simp only [trailLen, hstack] at hlenS'
    rw [hfalse, hreason, hmodel] at *
    simp only [falseAt, reasonAt, modelAt, stackAt] at hasg hlenS' hq ⊢
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨DB, mf, hS⟩ := h.fields
    refine ⟨DBT, S.mem_used + 3 + input.clauses[k].size, ?_⟩
    rw [hend, hT]
    apply solver.ext <;> first | rfl | (simp only [extended, withParsed]; rw [hS]; rfl)
  · intro _; rw [hTf.2.2.2.2.2.2.2.1, hTf.2.2.2.2.2.2.1]
  · intro q hq
    rw [← h.static q hq]
    have hq' := hq
    simp only [StaticCell, nextAt, prevAt, clausesAt] at hq'
    rcases hq' with hq' | hq' | hq' | hq'
    · apply low q (by omega) (by simp only [clausesAt] at hbase; omega) (by omega) (Or.inr (Or.inr trivial))
      intro hb
      have hl := hlits _ (hc0 (by have := hb1 hb; omega))
      have ha : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
        rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
      have hasg := h.trail.1
      have hlen := h.trail.2.1
      simp only [trailLen, hstack, stackAt] at hlen
      rw [hfalse, hreason, hmodel]
      simp only [falseAt, reasonAt, modelAt, stackAt] at hasg ⊢
      omega
    · apply low q (by omega) (by simp only [clausesAt] at hbase; omega) (by omega) (Or.inr (Or.inr trivial))
      intro hb
      have hl := hlits _ (hc0 (by have := hb1 hb; omega))
      have ha : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
        rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
      have hasg := h.trail.1
      have hlen := h.trail.2.1
      simp only [trailLen, hstack, stackAt] at hlen
      rw [hfalse, hreason, hmodel]
      simp only [falseAt, reasonAt, modelAt, stackAt] at hasg ⊢
      omega
    · apply hsame q (by omega) (by simp only [clausesAt] at hbase; omega)
      · intro h2
        have := hlits _ (hc0 (by omega)); have := hlits _ (hc1 h2)
        rw [hfirst]; simp only [firstAt]; omega
      · intro hb
        have hl := hlits _ (hc0 (by have := hb1 hb; omega))
        have ha : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
          rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
        have hasg := h.trail.1
        have hlen := h.trail.2.1
        simp only [trailLen, hstack, stackAt] at hlen
        rw [hfalse, hreason, hmodel]
        simp only [falseAt, reasonAt, modelAt, stackAt] at hasg ⊢
        omega
    · simp only [falseAt] at hq'
      apply low q (by omega) (by simp only [clausesAt] at hbase; omega) (by omega) (Or.inr (Or.inr trivial))
      intro hb
      have hl := hlits _ (hc0 (by have := hb1 hb; omega))
      have ha : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
        rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
      have hasg := h.trail.1
      have hlen := h.trail.2.1
      simp only [trailLen, hstack, stackAt] at hlen
      rw [hfalse, hreason, hmodel]
      simp only [falseAt, reasonAt, modelAt, stackAt] at hasg ⊢
      omega
  · rw [hrecs, hTf.2.2.2.2.2.2.1]
    have := (h.records.frame fun r hr q hq => (high q (by
      have := h.record_ge hr; simp only [RecordCell] at hq; omega) (by
      have := h.record_ge hr; simp only [RecordCell] at hq; omega)).symm ▸ rfl).append hrec
    simpa using this
  -- watch lists: a record of two or more literals links its two watches (C:62–63)
  · intro lit hlit
    rw [hTf.1] at hlit
    have hr := inRange_iff.mp hlit
    rw [hnv] at hr
    obtain ⟨links, hl, hnd, hmem⟩ := h.watches lit hlit
    simp only [records_all_inputs] at hmem
    have hlinks : ∀ q ∈ links, clausesAt S0.nVars ≤ q ∧ q < S.mem_used := by
      intro q hq
      obtain ⟨r, hr', h2, hw⟩ := (hmem q).1 hq
      have := h.record_ge hr'
      rcases hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    have hsameL : ∀ q ∈ links, T.ld q = S.ld q := fun q hq => high q (hlinks q hq).1 (hlinks q hq).2
    have huL : S.mem_used ∉ links := fun hm => by have := hlinks _ hm; omega
    have hu1L : S.mem_used + 1 ∉ links := fun hm => by have := hlinks _ hm; omega
    rw [hrecs, records_all_inputs, hTf.2.1]
    -- a list whose head cell did not change keeps its links
    have keep : (2 ≤ input.clauses[k].size →
        lit ≠ input.clauses[k][0]! ∧ lit ≠ input.clauses[k][1]!) →
        ∃ links', ListFrom T (S.first + lit) links' ∧ links'.Nodup ∧ ∀ link, link ∈ links' ↔
          Watches (parseRecords (clausesAt S0.nVars) (input.clauses.toList.take k) ++
            [(S.mem_used + 2, input.clauses[k].toList)]) lit link := by
      intro hne
      refine ⟨links, hl.frame fun q hq => ?_, hnd, fun link => ?_⟩
      · rcases hq with rfl | hq
        · apply hsame _ (by rw [hfirst]; simp only [firstAt]; omega)
            (by rw [hfirst]; simp only [firstAt, clausesAt] at hbase ⊢; omega)
          · intro h2
            obtain ⟨n0, n1⟩ := hne h2
            exact ⟨fun he => n0 (by omega), fun he => n1 (by omega)⟩
          · intro hb
            have hl0 := hlits _ (hc0 (by have := hb1 hb; omega))
            have ha0 : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
              rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
            have := hA
            rw [hfirst, hfalse, hreason, hmodel]
            simp only [firstAt, falseAt, reasonAt, modelAt]
            omega
        · exact hsameL q hq
      · rw [watches_append, hmem]
        constructor
        · exact Or.inl
        · rintro (hw | ⟨h2, hw⟩)
          · exact hw
          · exfalso
            obtain ⟨n0, n1⟩ := hne (by simpa using h2)
            rcases hw with ⟨_, hw⟩ | ⟨_, hw⟩
            · rw [List.getElem?_eq_getElem (by simp at h2 ⊢; omega)] at hw
              simp only [Option.some.injEq, Array.getElem_toList] at hw
              exact n0 (by rw [getElem!_pos input.clauses[k] 0 (by simp at h2; omega)]; exact hw.symm)
            · rw [List.getElem?_eq_getElem (by simp at h2 ⊢; omega)] at hw
              simp only [Option.some.injEq, Array.getElem_toList] at hw
              exact n1 (by rw [getElem!_pos input.clauses[k] 1 (by simp at h2; omega)]; exact hw.symm)
    by_cases h2 : 2 ≤ input.clauses[k].size
    · have g0 : input.clauses[k].toList[0]? = some input.clauses[k][0]! := by
        rw [List.getElem?_eq_getElem (by simp; omega), getElem!_pos input.clauses[k] 0 (by omega)]; simp
      have g1 : input.clauses[k].toList[1]? = some input.clauses[k][1]! := by
        rw [List.getElem?_eq_getElem (by simp; omega), getElem!_pos input.clauses[k] 1 (by omega)]; simp
      have h01 : input.clauses[k][0]! ≠ input.clauses[k][1]! := by
        rw [getElem!_pos input.clauses[k] 0 (by omega), getElem!_pos input.clauses[k] 1 (by omega)]
        have := (List.pairwise_iff_getElem.mp hnodup) 0 1 (by simp; omega) (by simp; omega) (by omega)
        simpa only [Array.getElem_toList] using this
      obtain ⟨w1, w2, w3, w4⟩ := hw2 h2
      by_cases e0 : lit = input.clauses[k][0]!
      · subst e0
        refine ⟨S.mem_used :: links, hl.push w1 w2 hsameL, List.nodup_cons.mpr ⟨huL, hnd⟩,
          fun link => ?_⟩
        rw [watches_append, List.mem_cons, hmem]
        have hlen2 : 2 ≤ input.clauses[k].toList.length := by simp; omega
        constructor
        · rintro (rfl | hw)
          · exact Or.inr ⟨hlen2, Or.inl ⟨by omega, g0⟩⟩
          · exact Or.inl hw
        · rintro (hw | ⟨-, ⟨he, -⟩ | ⟨-, he⟩⟩)
          · exact Or.inr hw
          · exact Or.inl (by omega)
          · simp only [Bool.false_eq_true, ite_false] at he
            rw [g1] at he; exact (h01 (Option.some.inj he).symm).elim
      · by_cases e1 : lit = input.clauses[k][1]!
        · subst e1
          refine ⟨(S.mem_used + 1) :: links, hl.push w3 w4 hsameL, List.nodup_cons.mpr ⟨hu1L, hnd⟩,
            fun link => ?_⟩
          rw [watches_append, List.mem_cons, hmem]
          have hlen2 : 2 ≤ input.clauses[k].toList.length := by simp; omega
          constructor
          · rintro (rfl | hw)
            · exact Or.inr ⟨hlen2, Or.inr ⟨by omega, g1⟩⟩
            · exact Or.inl hw
          · rintro (hw | ⟨-, ⟨-, he⟩ | ⟨he, -⟩⟩)
            · exact Or.inr hw
            · simp only [Bool.false_eq_true, ite_false] at he
              rw [g0] at he; exact (h01 (Option.some.inj he)).elim
            · exact Or.inl (by omega)
        · exact keep fun _ => ⟨e0, e1⟩
    · exact keep fun h2' => absurd h2' h2
  · refine ⟨by rw [hTf.2.2.2.2.2.2.2.2]; simp only [stackAt]; cases b <;> simp <;> omega, ?_, ?_, ?_⟩
    · rw [hlenT]
      cases b
      · simpa using hlenS
      · simp only [if_true]
        have := card_lt_of_distinct (N := S0.nVars.toNat) (m := trailLen S)
          (fun i => (trailAt S i).natAbs)
          (fun i hi => by
            have := inRange_iff.mp (h.trail.2.2.1 i hi); omega)
          (fun i hi j hj he => h.trail.2.2.2 i hi j hj (by rw [abs_eq_natAbs, abs_eq_natAbs, he]))
          (v := input.clauses[k][0]!.natAbs)
          (by have := hlits _ (hc0 (by have := hb1 rfl; omega)); omega)
          (fun i hi he => hfreeAbs rfl i hi (by rw [abs_eq_natAbs, abs_eq_natAbs, he]))
        omega
    · intro i hi
      rw [hlenT] at hi
      by_cases hi' : i < trailLen S
      · rw [htrS i hi']; exact h.trail.2.2.1 i hi'
      · cases b
        · simp at hi; omega
        · have : i = trailLen S := by simp at hi; omega
          subst this; rw [htrNew rfl]
          have := hlits _ (hc0 (by have := hb1 rfl; omega))
          exact inRange_iff.mpr ⟨by omega, by omega, by omega⟩
    · intro i hi j hj he
      rw [hlenT] at hi hj
      by_cases hi' : i < trailLen S <;> by_cases hj' : j < trailLen S
      · rw [htrS i hi', htrS j hj'] at he; exact h.trail.2.2.2 i hi' j hj' he
      · cases b
        · simp at hj; omega
        · have : j = trailLen S := by simp at hj; omega
          subst this
          rw [htrS i hi', htrNew rfl] at he
          exact absurd (by rw [he]; rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;>
            rcases abs_cases (-input.clauses[k][0]!) with ⟨_, e'⟩ | ⟨_, e'⟩ <;> omega)
            (hfreeAbs rfl i hi')
      · cases b
        · simp at hi; omega
        · have : i = trailLen S := by simp at hi; omega
          subst this
          rw [htrS j hj', htrNew rfl] at he
          exact absurd (by rw [← he]; rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;>
            rcases abs_cases (-input.clauses[k][0]!) with ⟨_, e'⟩ | ⟨_, e'⟩ <;> omega)
            (hfreeAbs rfl j hj')
      · cases b <;> simp at hi hj <;> omega
  -- `false`: the new literal `-lit` is tagged `IMPLIED`; other tags are unchanged
  · intro lit hlit
    have hr := inRange_iff.mp hlit
    rw [hlenT]
    by_cases hnew : b = true ∧ lit = - input.clauses[k][0]!
    · obtain ⟨hb, rfl⟩ := hnew
      rw [if_pos ⟨trailLen S, by simp [hb], htrNew hb⟩]
      unfold flag; rw [hTf.2.2.1]; exact (hunit hb).2.2.2.2.1
    · have hcell : flag T lit = flag S lit := by
        unfold flag; rw [hTf.2.2.1]
        apply low _ (by rw [hfalse]; simp only [falseAt]; omega)
          (by rw [hfalse]; simp only [falseAt, clausesAt] at hbase ⊢; omega)
          (by rw [hfalse]; simp only [falseAt]; omega) (Or.inr (Or.inr trivial))
        intro hb
        have hl0 := hlits _ (hc0 (by have := hb1 hb; omega))
        have ha0 : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
          rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
        have hne : lit ≠ - input.clauses[k][0]! := fun he => hnew ⟨hb, he⟩
        have := hA
        rw [hfalse, hreason, hmodel]
        simp only [falseAt, reasonAt, modelAt]
        omega
      rw [hcell, h.flags lit hlit]
      congr 1
      apply propext
      constructor
      · rintro ⟨i, hi, he⟩; exact ⟨i, by omega, by rw [htrS i hi]; exact he⟩
      · rintro ⟨i, hi, he⟩
        by_cases hi' : i < trailLen S
        · exact ⟨i, hi', by rw [← htrS i hi']; exact he⟩
        · cases b
          · simp at hi; omega
          · have : i = trailLen S := by simp at hi; omega
            subst this; rw [htrNew rfl] at he; exact absurd ⟨rfl, he.symm⟩ hnew
  -- `model`: the new variable gets its value (C:47)
  · intro i hi
    rw [hlenT] at hi
    rw [hTf.2.2.2.1]
    by_cases hi' : i < trailLen S
    · rw [htrS i hi', hcellS i hi' _ (Or.inl rfl)]; exact h.model i hi'
    · cases b
      · simp at hi; omega
      · have : i = trailLen S := by simp at hi; omega
        subst this
        rw [htrNew rfl, abs_neg', (hunit rfl).2.2.2.2.2.2]
        split <;> split <;> omega
  -- `reason`: the new literal's reason is its unit record (C:46)
  · intro i hi
    rw [hlenT] at hi
    by_cases hi' : i < trailLen S
    · obtain ⟨r, hr, e1, e2⟩ := h.reasons i hi'
      refine ⟨r, by rw [hrecs]; exact List.mem_append_left _ hr, ?_, by rw [htrS i hi']; exact e2⟩
      unfold reasonOf; rw [htrS i hi', hTf.2.2.2.2.1, hcellS i hi' _ (Or.inr rfl)]; exact e1
    · cases b
      · simp at hi; omega
      · have : i = trailLen S := by simp at hi; omega
        subst this
        refine ⟨(S.mem_used + 2, input.clauses[k].toList), by rw [hrecs]; simp, ?_, ?_⟩
        · unfold reasonOf; rw [htrNew rfl, hTf.2.2.2.2.1, abs_neg']
          exact (hunit rfl).2.2.2.2.2.1
        · rw [htrNew rfl, Int.neg_neg, hsingle (hb1 rfl)]
  -- each assigned literal comes from a unit clause of the input
  · intro i hi
    rw [hlenT] at hi
    by_cases hi' : i < trailLen S
    · obtain ⟨j, hj, hjs, he⟩ := h.units_input i hi'
      exact ⟨j, by omega, hjs, by rw [htrS i hi']; exact he⟩
    · cases b
      · simp at hi; omega
      · have : i = trailLen S := by simp at hi; omega
        subst this
        exact ⟨k, by omega, hk, by rw [htrNew rfl, Int.neg_neg, hsingle (hb1 rfl)]⟩
  -- every unit record, the new one included, is true at the root
  · intro r hr h1
    rw [hrecs] at hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i, hi, he⟩ := h.units_true r hr h1
      exact ⟨i, by rw [hlenT]; omega, by rw [htrS i hi]; exact he⟩
    · simp only [List.mem_singleton] at hr
      subst hr
      have hs1 : input.clauses[k].size = 1 := by simpa using h1
      have hl0 : (input.clauses[k].toList)[0]! = input.clauses[k][0]! := by
        rw [hsingle hs1]; rfl
      cases b
      · obtain ⟨i, hi, he⟩ := hold rfl hs1
        exact ⟨i, by rw [hlenT]; simp; exact hi, by rw [htrS i hi, he, hl0]⟩
      · exact ⟨trailLen S, by rw [hlenT]; simp, by rw [htrNew rfl, hl0]⟩
  -- no clause read is empty
  · intro c hc
    rw [htake] at hc
    rcases List.mem_append.mp hc with hc | hc
    · exact h.nonempty c hc
    · simp only [List.mem_singleton] at hc; subst hc; exact hne

/-- When `parse` reads clause `k`'s `0`, every literal of the clause is in `buffer`:
`size` is the clause's size. -/
theorem ParseInv.size_eq {input : Input} {S0 S : solver} {k size : Nat} {rest : List CInt}
    (valid : input.Valid) (h : ParseInv input S0 S k size (0 :: rest)) :
    ∃ hk : k < input.clauses.size, size = input.clauses[k].size ∧
      rest = tokList (input.clauses.toList.drop (k + 1)) := by
  obtain ⟨_, hcur⟩ := h
  unfold Current at hcur
  split at hcur
  case isFalse => simp at hcur
  rename_i hk
  obtain ⟨hsz, _, hrest⟩ := hcur
  have hsz' : size = input.clauses[k].size := by
    rcases Nat.lt_or_ge size input.clauses[k].size with hlt | hge
    · exfalso
      rw [List.drop_eq_getElem_cons (by rw [Array.length_toList]; exact hlt)] at hrest
      simp only [List.cons_append, List.cons.injEq] at hrest
      have := valid.lit_range _ (Array.getElem_mem hk) input.clauses[k][size] (Array.getElem_mem hlt)
      exact this.1 (by simpa using hrest.1.symm)
    · omega
  refine ⟨hk, hsz', ?_⟩
  have : input.clauses[k].toList.drop size = [] := by simp; omega
  rw [this] at hrest; simpa using hrest

/-- `addClause`'s preconditions hold when `parse` adds clause `k` from `buffer`
(C:235), given enough memory (E3). -/
theorem ParseCore.addClause_post {input : Input} {S0 S : solver} {k : Nat}
    (valid : input.Valid) (memory : memoryBound input ≤ S0.mem_max)
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hk : k < input.clauses.size)
    (hbuf : ∀ i < input.clauses[k].size, S.ld (S.buffer + i) = input.clauses[k][i]!) :
    AddClausePost S input.clauses[k].toList input.clauses[k].size 1
      (addClause S S.buffer input.clauses[k].size 1) := by
  obtain ⟨hnv, hb, hfirst, hfalse, hmodel, hreason, hstack, hprev, hnext, hnl, hmm⟩ := h.ptrs h0
  have hN : 1 ≤ S0.nVars := by rw [h0.nVars]; exact varsOf_pos _
  have hNv : S0.nVars = varsOf input.nVars := h0.nVars
  have hbase : clausesAt S0.nVars ≤ S.mem_used := h.records.bounds.1
  have hu : S.mem_used = parseEnd (clausesAt S0.nVars) (input.clauses.toList.take k) := by
    obtain ⟨DB, mf, hS⟩ := h.fields; rw [hS]; rfl
  have hcsize : (input.clauses[k].size : CInt) ≤ S0.nVars := by rw [hNv]; exact clause_size_le_vars valid hk
  have hlits : ∀ l ∈ input.clauses[k].toList, l ≠ 0 ∧ -S0.nVars ≤ l ∧ l ≤ S0.nVars := by
    intro l hl
    have := valid.lit_range _ (Array.getElem_mem hk) l (by simpa using hl)
    have hv : input.nVars ≤ S0.nVars := by rw [hNv]; unfold varsOf; split <;> omega
    rcases abs_cases l with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
  have hnodup : input.clauses[k].toList.Nodup := valid.no_repeated_lit _ (Array.getElem_mem hk)
  apply addClause_spec
  · simp
  · rw [hb]; simp only [bufferAt]; omega
  · left; rw [hb]; simp only [bufferAt, clausesAt] at hbase ⊢; omega
  · intro i hi
    rw [hbuf i (by simpa using hi), getElem!_pos input.clauses[k] i (by simpa using hi)]
    simp
  · -- the record ends within the input records, so within `memoryBound` (E3)
    have htake : input.clauses.toList.take (k + 1) = input.clauses.toList.take k ++ [input.clauses[k]] := by
      rw [List.take_succ, List.getElem?_eq_getElem (by simpa using hk)]; simp
    have e1 := parseEnd_append (clausesAt S0.nVars) (input.clauses.toList.take k) input.clauses[k]
    rw [← htake, ← hu] at e1
    have e2 := parseEnd_take_le (clausesAt S0.nVars) input.clauses.toList (k + 1)
    have e3 := parseEnd_le_memoryBound input
    rw [← hNv] at e3
    rw [hmm]; omega
  · intro hl i hi
    have hm : input.clauses[k].toList[i]! ∈ input.clauses[k].toList := by
      rw [getElem!_pos input.clauses[k].toList i (by omega)]; simp
    have := hlits _ hm
    rw [hfirst, hb]; simp only [firstAt, bufferAt, clausesAt] at hbase ⊢; omega
  · intro hl he
    have := (List.pairwise_iff_getElem.mp hnodup) 0 1 (by omega) (by omega) (by omega)
    rw [getElem!_pos input.clauses[k].toList 0 (by omega),
      getElem!_pos input.clauses[k].toList 1 (by omega)] at he
    exact this he

/-- A clause's literal list read with `!` agrees with the array. -/
theorem toList_getElem! (c : Array CInt) (i : Nat) (hi : i < c.size) : c.toList[i]! = c[i]! := by
  rw [getElem!_pos c.toList i (by simpa using hi), getElem!_pos c i hi]; simp

/-- Facts about `addClause`'s result in `parse`, shared by every outcome below. -/
theorem ParseCore.after_add_facts {input : Input} {S0 S : solver} {k : Nat}
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hk : k < input.clauses.size)
    (post : AddClausePost S input.clauses[k].toList input.clauses[k].size 1
      (addClause S S.buffer input.clauses[k].size 1)) :
    let r := addClause S S.buffer input.clauses[k].size 1
    (∃ DB, r.1 = extended S DB (S.mem_used + 3 + input.clauses[k].size) S.assigned) ∧
    ClauseAt r.1 (S.mem_used + 2) input.clauses[k].toList ∧ r.2 = S.mem_used + 2 ∧
    (∀ q, 0 ≤ q → q < S.mem_used + 2 → r.1.ld q = afterWatches S input.clauses[k].toList q) := by
  intro r
  obtain ⟨hc, hmu, hlits, hzero, hbelow, habove, ⟨DB, hDB⟩⟩ := post
  refine ⟨⟨DB, ?_⟩, ⟨fun i hi => ?_, ?_⟩, hc, fun q hq hlt => hbelow q hq (by rw [hc]; exact hlt)⟩
  · show r.1 = _
    rw [hDB]; apply solver.ext <;> first | rfl | (simp [added, extended]; omega) | simp [added, extended]
  · have := hlits i hi; rw [hc] at this; exact this
  · have := hzero; rw [hc] at this; simpa using this

/-- `afterWatches` leaves every cell below the record other than the two watch heads. -/
theorem afterWatches_other {S0 : solver} {L : List CInt} {q : CInt} (hq : q < S0.mem_used)
    (hne : 1 < L.length → q ≠ S0.first + L[0]! ∧ q ≠ S0.first + L[1]!) :
    afterWatches S0 L q = S0.ld q := by
  unfold afterWatches
  split
  · rename_i hl
    obtain ⟨n0, n1⟩ := hne hl
    simp only
    rw [if_neg (by omega), if_neg n0, if_neg (by omega), if_neg n1]
  · rfl

/-- `parse` keeps `addClause`'s result (C:235): clauses of two or more literals, and unit
clauses whose literal is already true. -/
theorem ParseCore.after_add {input : Input} {S0 S : solver} {k : Nat} (valid : input.Valid)
    (memory : memoryBound input ≤ S0.mem_max)
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hk : k < input.clauses.size)
    (hbuf : ∀ i < input.clauses[k].size, S.ld (S.buffer + i) = input.clauses[k][i]!)
    (hne : input.clauses[k].size ≠ 0)
    (hold : input.clauses[k].size = 1 → ∃ i < trailLen S, trailAt S i = - input.clauses[k][0]!) :
    ParseCore input S0 (addClause S S.buffer input.clauses[k].size 1).1 (k + 1) := by
  have post := h.addClause_post valid memory h0 hk hbuf
  obtain ⟨⟨DB, hT⟩, hrec, hc, hbelow⟩ := h.after_add_facts h0 hk post
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

/-- `parse` assigns a new unit clause whose literal is unassigned (C:238–239). -/
theorem ParseCore.after_assign {input : Input} {S0 S : solver} {k : Nat} (valid : input.Valid)
    (memory : memoryBound input ≤ S0.mem_max)
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hk : k < input.clauses.size)
    (hbuf : ∀ i < input.clauses[k].size, S.ld (S.buffer + i) = input.clauses[k][i]!)
    (hsize : input.clauses[k].size = 1)
    (hf1 : flag S input.clauses[k][0]! = 0) (hf2 : flag S (- input.clauses[k][0]!) = 0) :
    ParseCore input S0 (assign (addClause S S.buffer input.clauses[k].size 1).1
      (addClause S S.buffer input.clauses[k].size 1).2 1) (k + 1) := by
  have post := h.addClause_post valid memory h0 hk hbuf
  obtain ⟨⟨DB, hR⟩, hrec, hc, hbelow⟩ := h.after_add_facts h0 hk post
  generalize hr : addClause S S.buffer input.clauses[k].size 1 = r at hR hrec hc hbelow ⊢
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
  have ha : 0 ≤ abs input.clauses[k][0]! ∧ abs input.clauses[k][0]! ≤ S0.nVars := by
    rcases abs_cases input.clauses[k][0]! with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hRf : r.1.false = S.false ∧ r.1.model = S.model ∧ r.1.reason = S.reason ∧
      r.1.assigned = S.assigned ∧ r.1.first = S.first := by
    rw [hR]; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  -- the cells `assign` writes (C:44–47)
  have hcell : ∀ q, 0 ≤ q → (assign r.1 r.2 1).ld q =
      if q = S.model + abs input.clauses[k][0]! then (if input.clauses[k][0]! > 0 then 1 else 0)
      else if q = S.reason + abs input.clauses[k][0]! then 1 + r.2
      else if q = S.assigned then - input.clauses[k][0]!
      else if q = S.false + - input.clauses[k][0]! then IMPLIED
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

/-- An input with an empty clause is unsatisfiable (C:236, `!size`). -/
theorem unsat_of_empty {input : Input} {k : Nat} (hk : k < input.clauses.size)
    (h0 : input.clauses[k].size = 0) : input.Unsat := by
  intro a sat
  obtain ⟨lit, hlit, _⟩ := sat _ (Array.getElem_mem hk)
  have : input.clauses[k].toList = [] := List.eq_nil_of_length_eq_zero (by simp [h0])
  rw [this] at hlit; simp at hlit

/-- An input with unit clauses `[l]` and `[-l]` is unsatisfiable (C:236, a unit clause
whose literal is already false). -/
theorem unsat_of_opposite_units {input : Input} {j k : Nat} (hj : j < input.clauses.size)
    (hk : k < input.clauses.size) {l : CInt} (hl : l ≠ 0)
    (cj : input.clauses[j].toList = [-l]) (ck : input.clauses[k].toList = [l]) : input.Unsat := by
  intro a sat
  obtain ⟨x, hx, tx⟩ := sat _ (Array.getElem_mem hj)
  obtain ⟨y, hy, ty⟩ := sat _ (Array.getElem_mem hk)
  rw [cj] at hx; rw [ck] at hy
  simp only [List.mem_singleton] at hx hy
  rw [hx] at tx; rw [hy] at ty
  unfold Verification.LitTrue at tx ty
  rw [Int.natAbs_neg, ty] at tx
  by_cases hp : 0 < l
  · simp [hp] at tx; omega
  · simp [hp] at tx; omega

/-- In `parse`, a unit clause whose literal is already false means the input is
unsatisfiable: the literal was made false by an earlier opposite unit clause. -/
theorem ParseCore.unsat_conflict {input : Input} {S0 S : solver} {k : Nat} (valid : input.Valid)
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0)
    (h : ParseCore input S0 S k) (hk : k < input.clauses.size) (hsize : input.clauses[k].size = 1)
    (hf : flag S input.clauses[k][0]! ≠ 0) : input.Unsat := by
  have hm : input.clauses[k][0]! ∈ input.clauses[k].toList := by
    rw [getElem!_pos input.clauses[k] 0 (by omega)]; simp
  have hlit := valid.lit_range _ (Array.getElem_mem hk) _ (by simpa using hm)
  have hv : input.nVars ≤ S0.nVars := by rw [h0.nVars]; unfold varsOf; split <;> omega
  have hr : InRange S0.nVars input.clauses[k][0]! := ⟨hlit.1, by omega⟩
  have hfl := h.flags _ hr
  rw [hfl] at hf
  split at hf
  · rename_i hex
    obtain ⟨i, hi, he⟩ := hex
    obtain ⟨j, hj, hjs, cj⟩ := h.units_input i hi
    rw [he] at cj
    have ck : input.clauses[k].toList = [input.clauses[k][0]!] := by
      apply List.ext_getElem (by simp [hsize])
      intro i hi1 hi2
      have : i = 0 := by simp at hi2; omega
      subst this; simp [getElem!_pos input.clauses[k] 0 (by omega)]
    exact unsat_of_opposite_units hjs hk hlit.1 cj ck
  · exact absurd rfl hf

/-- After clause `k`, `buffer` is empty and the unread tokens start at clause `k + 1`. -/
theorem current_next (input : Input) (S : solver) (k : Nat) :
    Current input S (k + 1) 0 (tokList (input.clauses.toList.drop (k + 1))) := by
  unfold Current
  split
  · rename_i hk
    refine ⟨by omega, fun i hi => by omega, ?_⟩
    rw [List.drop_eq_getElem_cons (by simpa using hk)]
    simp [tokList]
  · rename_i hk
    have : input.clauses.toList.drop (k + 1) = [] := by simp; omega
    simp [this, tokList]

/-- What `parse`'s checks after `addClause` read (C:236–238): for a unit clause, the
literal `clause[0]` and the old `false` tags, which `addClause` does not touch. -/
theorem ParseCore.unit_reads {input : Input} {S0 S : solver} {k : Nat} (valid : input.Valid)
    (memory : memoryBound input ≤ S0.mem_max)
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hk : k < input.clauses.size)
    (hbuf : ∀ i < input.clauses[k].size, S.ld (S.buffer + i) = input.clauses[k][i]!)
    (hsize : input.clauses[k].size = 1) :
    let r := addClause S S.buffer input.clauses[k].size 1
    r.1.ld r.2 = input.clauses[k][0]! ∧
      ∀ lit, InRange S0.nVars lit → r.1.ld (r.1.false + lit) = flag S lit := by
  intro r
  have post := h.addClause_post valid memory h0 hk hbuf
  obtain ⟨⟨DB, hR⟩, hrec, hc, hbelow⟩ := h.after_add_facts h0 hk post
  obtain ⟨hnv, hb, hfirst, hfalse, -⟩ := h.ptrs h0
  have hbase : clausesAt S0.nVars ≤ S.mem_used := h.records.bounds.1
  have hN : 1 ≤ S0.nVars := by rw [h0.nVars]; exact varsOf_pos _
  refine ⟨?_, fun lit hlit => ?_⟩
  · show r.1.ld r.2 = _
    rw [hc]
    have := hrec.1 0 (by simp; omega)
    simp only [Int.cast_ofNat_Int, Int.add_zero] at this
    rw [this, ← toList_getElem! input.clauses[k] 0 (by omega),
      getElem!_pos input.clauses[k].toList 0 (by simp; omega)]
  · have hl := inRange_iff.mp hlit
    have hrf : r.1.false = S.false := by show r.1.false = _; rw [hR]; rfl
    show r.1.ld (r.1.false + lit) = _
    rw [hrf, hbelow _ (by rw [hfalse]; simp only [falseAt]; omega)
      (by rw [hfalse]; simp only [falseAt, clausesAt] at hbase ⊢; omega)]
    exact afterWatches_other (by rw [hfalse]; simp only [falseAt, clausesAt] at hbase ⊢; omega)
      fun hl' => by simp at hl'; omega

/-- `buffer` holds clause `k` once its `0` is read. -/
theorem ParseInv.buf {input : Input} {S0 S : solver} {k size : Nat} {rest : List CInt}
    (h : ParseInv input S0 S k size rest) (hk : k < input.clauses.size)
    (hsize : size = input.clauses[k].size) :
    ∀ i < input.clauses[k].size, S.ld (S.buffer + i) = input.clauses[k][i]! := by
  obtain ⟨_, hcur⟩ := h
  unfold Current at hcur
  rw [dif_pos hk] at hcur
  intro i hi; exact hcur.2.1 i (by omega)

end MicrosatLean.Faithful.Verification
