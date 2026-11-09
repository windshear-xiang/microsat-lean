import MicrosatLean.Faithful.Verification.Order
import MicrosatLean.Faithful.Verification.AddClause
import Std.Tactic.Do

/-!
# `initCDCL` (C:181–210)

With enough memory, `initCDCL` places every array at its `Layout` offset and
leaves `prev`, `next` and `first` initialized as C:206–209 does; every other cell
reads 0.
-/

namespace MicrosatLean.Faithful.Verification

open Std.Do
set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- The number of variables `initCDCL` uses: at least 1 (C:182). -/
def varsOf (n : CInt) : CInt := if n < 1 then 1 else n

/-- The value of cell `p` once the initialization loop has handled the variables `vs`:
`prev[v] = v - 1`, `next[v - 1] = v` and `first[±v] = END` (C:207–209); else 0. -/
def initCell (n : CInt) (vs : List CInt) (p : CInt) : CInt :=
  if vs.any (fun v => p == prevAt n + v) then p - prevAt n - 1
  else if vs.any (fun v => p == nextAt n + v - 1) then p - nextAt n + 1
  else if vs.any (fun v => p == firstAt n + v || p == firstAt n - v) then END
  else 0

/-- Everything `initCDCL` guarantees, for `N = varsOf n` variables. Used by `parse`'s proof. -/
structure InitState (n m mem_max : CInt) (S : solver) : Prop where
  nVars : S.nVars = varsOf n
  nClauses : S.nClauses = m
  mem_max : S.mem_max = mem_max
  mem_used : S.mem_used = clausesAt (varsOf n)
  nLemmas : S.nLemmas = 0
  maxLemmas : S.maxLemmas = 2000
  model : S.model = modelAt (varsOf n)
  next : S.next = nextAt (varsOf n)
  prev : S.prev = prevAt (varsOf n)
  buffer : S.buffer = bufferAt (varsOf n)
  reason : S.reason = reasonAt (varsOf n)
  falseStack : S.falseStack = stackAt (varsOf n)
  «false» : S.false = falseAt (varsOf n)
  first : S.first = firstAt (varsOf n)
  forced : S.forced = stackAt (varsOf n)
  processed : S.processed = stackAt (varsOf n)
  assigned : S.assigned = stackAt (varsOf n)
  head : S.head = varsOf n
  cells : ∀ p, 0 ≤ p → S.ld p = initCell (varsOf n) (vars (varsOf n)) p

/-- `List.any` only depends on membership. -/
theorem any_congr_mem {l1 l2 : List CInt} (f : CInt → Bool) (h : ∀ v, v ∈ l1 ↔ v ∈ l2) :
    l1.any f = l2.any f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  exact ⟨fun ⟨v, hv, hf⟩ => ⟨v, (h v).1 hv, hf⟩, fun ⟨v, hv, hf⟩ => ⟨v, (h v).2 hv, hf⟩⟩

/-- `initCell` only depends on which variables are handled. -/
theorem initCell_congr {N : CInt} {l1 l2 : List CInt} (h : ∀ v, v ∈ l1 ↔ v ∈ l2) (p : CInt) :
    initCell N l1 p = initCell N l2 p := by
  simp only [initCell, any_congr_mem _ h]

/-- No handled variable has its cell at `p`. -/
theorem any_false_of {pre : List CInt} {f : CInt → Bool} (h : ∀ v ∈ pre, f v = false) :
    pre.any f = false := by
  simpa [List.any_eq_false] using h

/-- Handling one more variable `x` sets `prev[x]`, `next[x - 1]` and `first[±x]`
(C:207–209); every other cell keeps its value. -/
theorem initCell_snoc {N : CInt} {pre : List CInt} {x p : CInt}
    (hpre : ∀ v ∈ pre, 1 ≤ v ∧ v ≤ N) (hx : 1 ≤ x ∧ x ≤ N) :
    initCell N (pre ++ [x]) p =
      if p = prevAt N + x then x - 1 else if p = nextAt N + x - 1 then x
      else if p = firstAt N + x ∨ p = firstAt N - x then END else initCell N pre p := by
  simp only [initCell, List.any_append, List.any_cons, List.any_nil, Bool.or_false]
  by_cases h1 : p = prevAt N + x
  · rw [if_pos (by simp [h1]), if_pos h1]; omega
  rw [if_neg h1]
  -- the first condition holds only through an earlier variable, which cannot be the case
  -- for the cells of `x`; otherwise both sides agree with `initCell N pre p`
  by_cases h2 : p = nextAt N + x - 1
  · have c1 : (pre.any (fun v => p == prevAt N + v) || (p == prevAt N + x)) = false := by
      simp only [Bool.or_eq_false_iff, List.any_eq_false, beq_iff_eq]
      exact ⟨fun v hv hpv => by have := hpre v hv; simp [prevAt, nextAt] at hpv h2; omega, beq_eq_false_iff_ne.mpr h1⟩
    rw [if_neg (by simp [c1]), if_pos (by simp [h2]), if_pos h2]; omega
  rw [if_neg h2]
  by_cases h3 : p = firstAt N + x ∨ p = firstAt N - x
  · have c1 : (pre.any (fun v => p == prevAt N + v) || (p == prevAt N + x)) = false := by
      simp only [Bool.or_eq_false_iff, List.any_eq_false, beq_iff_eq]
      exact ⟨fun v hv hpv => by have := hpre v hv; simp [prevAt, firstAt] at hpv h3; omega, beq_eq_false_iff_ne.mpr h1⟩
    have c2 : (pre.any (fun v => p == nextAt N + v - 1) || (p == nextAt N + x - 1)) = false := by
      simp only [Bool.or_eq_false_iff, List.any_eq_false, beq_iff_eq]
      exact ⟨fun v hv hpv => by have := hpre v hv; simp [nextAt, firstAt] at hpv h3; omega, beq_eq_false_iff_ne.mpr h2⟩
    have c3 : (pre.any (fun v => p == firstAt N + v || p == firstAt N - v) ||
        (p == firstAt N + x || p == firstAt N - x)) = true := by
      rcases h3 with h3 | h3 <;> simp [h3]
    rw [if_neg (by simp [c1]), if_neg (by simp [c2]), if_pos c3, if_pos h3]
  rw [if_neg h3]
  have h3' := not_or.mp h3
  simp [h1, h2, h3'.1, h3'.2]

/-- Cells of `false` and `model` are never set by the loop: they read 0. -/
theorem initCell_zero {N : CInt} {vs : List CInt} {p : CInt}
    (hvs : ∀ v ∈ vs, 1 ≤ v ∧ v ≤ N) (hp : p ≤ N ∨ (6 * N + 5 ≤ p ∧ p ≤ 8 * N + 5)) :
    initCell N vs p = 0 := by
  have n1 : vs.any (fun v => p == prevAt N + v) = false :=
    any_false_of fun v hv => by have := hvs v hv; simp [prevAt]; omega
  have n2 : vs.any (fun v => p == nextAt N + v - 1) = false :=
    any_false_of fun v hv => by have := hvs v hv; simp [nextAt]; omega
  have n3 : vs.any (fun v => p == firstAt N + v || p == firstAt N - v) = false :=
    any_false_of fun v hv => by have := hvs v hv; simp [firstAt]; omega
  simp [initCell, n1, n2, n3]

/-- `prev[v] = v - 1` after initialization (C:207). -/
theorem initCell_prev {N v : CInt} (hv : 1 ≤ v ∧ v ≤ N) :
    initCell N (vars N) (prevAt N + v) = v - 1 := by
  have c1 : (vars N).any (fun w => prevAt N + v == prevAt N + w) = true :=
    List.any_eq_true.mpr ⟨v, mem_vars.mpr hv, by simp⟩
  simp only [initCell, c1, if_true]; omega

/-- `next[v - 1] = v` after initialization (C:207). -/
theorem initCell_next {N v : CInt} (hv : 1 ≤ v ∧ v ≤ N) :
    initCell N (vars N) (nextAt N + v - 1) = v := by
  have c1 : (vars N).any (fun w => nextAt N + v - 1 == prevAt N + w) = false :=
    any_false_of fun w hw => by rw [mem_vars] at hw; simp [nextAt, prevAt]; omega
  have c2 : (vars N).any (fun w => nextAt N + v - 1 == nextAt N + w - 1) = true :=
    List.any_eq_true.mpr ⟨v, mem_vars.mpr hv, by simp⟩
  simp only [initCell, c1, c2, Bool.false_eq_true, if_false, if_true]; omega

/-- The extra cell of C:204 reads 0. -/
theorem initCell_sentinel {N : CInt} (hN : 1 ≤ N) : initCell N (vars N) (clausesAt N - 1) = 0 := by
  have c1 : (vars N).any (fun w => clausesAt N - 1 == prevAt N + w) = false :=
    any_false_of fun w hw => by rw [mem_vars] at hw; simp [clausesAt, prevAt]; omega
  have c2 : (vars N).any (fun w => clausesAt N - 1 == nextAt N + w - 1) = false :=
    any_false_of fun w hw => by rw [mem_vars] at hw; simp [clausesAt, nextAt]; omega
  have c3 : (vars N).any (fun w => clausesAt N - 1 == firstAt N + w ||
      clausesAt N - 1 == firstAt N - w) = false :=
    any_false_of fun w hw => by rw [mem_vars] at hw; simp [clausesAt, firstAt]; omega
  simp [initCell, c1, c2, c3]

/-- The fields `initCDCL` sets (C:183–204), with `head` still 0 and memory `DB`. -/
def initFields (n m mem_max : CInt) (DB : Array CInt) : solver :=
  { DB := DB, nVars := varsOf n, nClauses := m, mem_used := clausesAt (varsOf n), mem_fixed := 0,
    mem_max := mem_max, maxLemmas := 2000, nLemmas := 0, buffer := bufferAt (varsOf n),
    nConflicts := 0, model := modelAt (varsOf n), reason := reasonAt (varsOf n),
    falseStack := stackAt (varsOf n), «false» := falseAt (varsOf n), first := firstAt (varsOf n),
    forced := stackAt (varsOf n), processed := stackAt (varsOf n), assigned := stackAt (varsOf n),
    next := nextAt (varsOf n), prev := prevAt (varsOf n), head := 0, res := 0,
    fast := 1 <<< 24, slow := 1 <<< 24 }

/-- Invariant of the initialization loop (C:206–209) after handling the variables `vs`. -/
def InitLoop (n m mem_max : CInt) (vs : List CInt) (S : solver) : Prop :=
  (∃ DB, S = initFields n m mem_max DB) ∧ ∀ p, 0 ≤ p → S.ld p = initCell (varsOf n) vs p

theorem initCDCL_spec {n m mem_max : CInt} (h : clausesAt (varsOf n) ≤ mem_max) :
    InitState n m mem_max (initCDCL n m mem_max) := by
  generalize hR : initCDCL n m mem_max = R
  apply Id.of_wp_run_eq hR
  mvcgen [initCDCL] invariants
  · ⇓⟨cur, S⟩ => ⌜InitLoop n m mem_max cur.prefix S⌝
  case vc2.pre =>
    have hN : 1 ≤ varsOf n := by unfold varsOf; split <;> omega
    generalize hNv : varsOf n = N at h hN
    have hNv' : varsOf n = N := hNv
    unfold varsOf at hNv
    simp only [clausesAt] at h
    refine ⟨⟨?w, ?hext⟩, ?hcells⟩
    case hext =>
      apply solver.ext
      all_goals (try rfl)
      all_goals (simp +zetaDelta (disch := omega) [getMemory_fst, if_neg, hNv, hNv', initFields,
        modelAt, nextAt, prevAt, bufferAt, reasonAt, stackAt, falseAt, firstAt, clausesAt]; try omega)
    case hcells =>
      intro p hp
      rename_i S2 S1 Spre
      have hS2 : S2.mem_used = clausesAt N - 1 ∧ S2.DB = #[] := by
        simp +zetaDelta (disch := omega) [getMemory_fst, if_neg, hNv, clausesAt]; omega
      show ({ S1 with mem_used := S1.mem_used + 1 } : solver).ld p = _
      rw [ld_with_mem_used]
      show (S2.st S2.mem_used 0).ld p = _
      rw [ld_st _ _ (by simp only [clausesAt] at hS2; omega) hp, ld_eq_getD _ hp, hS2.2]
      simp [initCell]
  case vc1.step =>
    rename_i pre x suff hlist B T6 T5 T4 T3 T2 T1 T hinv
    obtain ⟨⟨DB, hB⟩, hcells⟩ := hinv
    have hN : 1 ≤ varsOf n := by unfold varsOf; split <;> omega
    have hmem : ∀ v, v ∈ (1...=varsOf n).toList ↔ 1 ≤ v ∧ v ≤ varsOf n := by
      intro v; simp [Std.Rcc.mem_toList_iff_mem, Std.Rcc.mem_iff]
    have hlist' : (1...=varsOf n).toList = pre ++ x :: suff := hlist
    have hx : 1 ≤ x ∧ x ≤ varsOf n := (hmem x).1 (by rw [hlist']; simp)
    have hpre : ∀ v ∈ pre, 1 ≤ v ∧ v ≤ varsOf n := fun v hv => (hmem v).1 (by rw [hlist']; simp [hv])
    have hBf : B.prev = prevAt (varsOf n) ∧ B.next = nextAt (varsOf n) ∧
        B.false = falseAt (varsOf n) ∧ B.model = modelAt (varsOf n) ∧ B.first = firstAt (varsOf n) := by
      simp [hB, initFields]
    refine ⟨⟨T.DB, ?_⟩, ?_⟩
    · apply solver.ext <;> first | rfl | simp [T, T1, T2, T3, T4, T5, T6, hB, initFields]
    · intro p hp
      show T.ld p = _
      simp only [T, T1, T2, T3, T4, T5, T6, st_prev, st_next, st_false, st_model, st_first,
        hBf.1, hBf.2.1, hBf.2.2.1, hBf.2.2.2.1, hBf.2.2.2.2]
      generalize varsOf n = N at hN hx hpre hcells
      rw [initCell_snoc hpre hx]
      have e1 : prevAt N = 2 * (N + 1) := rfl
      have e2 : nextAt N = N + 1 := rfl
      have e3 : falseAt N = 7 * N + 5 := rfl
      have e4 : modelAt N = 0 := rfl
      have e5 : firstAt N = 9 * N + 6 := rfl
      simp (disch := omega) only [ld_st]
      rw [hcells p hp]
      repeat' split
      all_goals first
        | rfl
        | omega
        | (exact (initCell_zero hpre (by omega)).symm)
  case vc3.post.success =>
    rename_i r S' hinv
    obtain ⟨⟨DB, hr⟩, hcells⟩ := hinv
    constructor
    all_goals try (simp +zetaDelta [S', hr, initFields, varsOf]; done)
    intro p hp
    show r.ld p = _
    rw [hcells p hp]
    apply initCell_congr
    intro v
    simp only [mem_vars, Std.Rcc.mem_toList_iff_mem, Std.Rcc.mem_iff, varsOf]
    exact Iff.rfl

end MicrosatLean.Faithful.Verification
