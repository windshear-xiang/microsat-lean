import MicrosatLean.Faithful.Verification.InitCDCL
import MicrosatLean.Faithful.Verification.Frame
import MicrosatLean.Faithful.Verification.Trail
import MicrosatLean.Faithful.Verification.Assign
import MicrosatLean.Faithful.Verification.Tokens
import MicrosatLean.Faithful.Verification.Invariant

/-!
# The loop invariant of `parse` (C:226–241)

After `parse` has added `k` clauses and copied `size` literals of clause `k` into
`buffer`, the state is `initCDCL`'s with the first `k` records appended, their watches
linked, and their unit clauses assigned at the root.
-/

namespace MicrosatLean.Faithful.Verification

/-- Records of the clauses `cs`, laid out from `p` on (C:59–66). -/
def parseRecords (p : Ptr) : List (Array CInt) → List Record
  | [] => []
  | c :: cs => (p + 2, c.toList) :: parseRecords (p + 3 + c.size) cs

/-- Where the records of the clauses `cs` end, from `p` on. -/
def parseEnd (p : Ptr) : List (Array CInt) → Ptr
  | [] => p
  | c :: cs => parseEnd (p + 3 + c.size) cs

/-- The records end after every clause's `size + 3` cells. -/
theorem parseEnd_eq (p : Ptr) (cs : List (Array CInt)) :
    parseEnd p cs = p + (cs.map fun c => (c.size : CInt) + 3).sum := by
  induction cs generalizing p with
  | nil => simp [parseEnd]
  | cons c cs ih => simp [parseEnd, ih]; omega

/-- Adding one more clause appends its record at the current end (C:59–61). -/
theorem parseRecords_append (p : Ptr) (cs : List (Array CInt)) (c : Array CInt) :
    parseRecords p (cs ++ [c]) = parseRecords p cs ++ [(parseEnd p cs + 2, c.toList)] := by
  induction cs generalizing p with
  | nil => simp [parseRecords, parseEnd]
  | cons d cs ih => simp [parseRecords, parseEnd, ih]

/-- Adding one more clause moves the end by `size + 3`. -/
theorem parseEnd_append (p : Ptr) (cs : List (Array CInt)) (c : Array CInt) :
    parseEnd p (cs ++ [c]) = parseEnd p cs + 3 + c.size := by
  rw [parseEnd_eq, parseEnd_eq]; simp; omega

/-- The cells of a list of clause records add up to a nonnegative size. -/
theorem sizes_sum_nonneg (l : List (Array CInt)) : 0 ≤ (l.map fun c => (c.size : CInt) + 3).sum := by
  induction l with
  | nil => simp
  | cons c l ih => simp only [List.map_cons, List.sum_cons]; omega

/-- The records of a prefix end no later than all the input records. -/
theorem parseEnd_take_le (p : Ptr) (cs : List (Array CInt)) (k : Nat) :
    parseEnd p (cs.take k) ≤ parseEnd p cs := by
  rw [parseEnd_eq, parseEnd_eq]
  have : ∀ (l : List (Array CInt)) (k : Nat),
      ((l.take k).map fun c => (c.size : CInt) + 3).sum ≤ (l.map fun c => (c.size : CInt) + 3).sum := by
    intro l k
    induction l generalizing k with
    | nil => simp
    | cons c l ih =>
      cases k with
      | zero => have := sizes_sum_nonneg l; simp only [List.take_zero, List.map_nil, List.sum_nil,
          List.map_cons, List.sum_cons]; omega
      | succ k => simp only [List.take_succ_cons, List.map_cons, List.sum_cons]; have := ih k; omega
  have := this cs k; omega

/-- The input records fit in the memory `memoryBound` allows (E3). -/
theorem parseEnd_le_memoryBound (input : Input) :
    parseEnd (clausesAt (varsOf input.nVars)) input.clauses.toList ≤ memoryBound input := by
  rw [parseEnd_eq]
  have hv : varsOf input.nVars = max 1 input.nVars := by unfold varsOf; split <;> omega
  have hb : (0 : CInt) ≤ (clauseBound (max 1 input.nVars) : CInt) := Int.natCast_nonneg _
  have := Int.mul_nonneg hb (show (0 : CInt) ≤ max 1 input.nVars + 3 by omega)
  dsimp only [memoryBound]
  rw [hv]; omega

/-- Cell `q` is in the `prev` or `next` arrays, is the extra 0 of C:204, or is `false[0]`.
These cells are only written by `initCDCL`. -/
def StaticCell (N q : CInt) : Prop :=
  (nextAt N ≤ q ∧ q ≤ nextAt N + N) ∨ (prevAt N ≤ q ∧ q ≤ prevAt N + N) ∨ q = clausesAt N - 1 ∨
    q = falseAt N

/-- `S0` with new memory, `mem_used`, `mem_fixed` and `assigned`: the only fields `parse`
changes after `initCDCL` (C:56, C:65, C:45). -/
def withParsed (S0 : solver) (DB : Array CInt) (mu mf a : CInt) : solver :=
  { S0 with
    DB := DB
    mem_used := mu
    mem_fixed := mf
    assigned := a }

/-- What holds after `parse` added `k` clauses, apart from `buffer`'s contents. `S0` is
the state `initCDCL` produced. -/
structure ParseCore (input : Input) (S0 S : solver) (k : Nat) : Prop where
  /-- Only `DB`, `mem_used`, `mem_fixed` and `assigned` differ from `initCDCL`'s state. -/
  fields : ∃ DB mf, S = withParsed S0 DB (parseEnd (clausesAt S0.nVars) (input.clauses.toList.take k))
    mf S.assigned
  /-- `mem_fixed` marks the end of the input records once one was added (C:65). -/
  fixed : 0 < k → S.mem_fixed = S.mem_used
  static : ∀ q, StaticCell S0.nVars q → S.ld q = S0.ld q
  records : Tiling S (clausesAt S0.nVars) S.mem_used
    (parseRecords (clausesAt S0.nVars) (input.clauses.toList.take k))
  watches : WatchLists S ⟨parseRecords (clausesAt S0.nVars) (input.clauses.toList.take k), [], fun _ => false⟩
  trail : stackAt S0.nVars ≤ S.assigned ∧ trailLen S ≤ S0.nVars.toNat ∧
    (∀ i < trailLen S, InRange S0.nVars (trailAt S i)) ∧
    (∀ i < trailLen S, ∀ j < trailLen S, abs (trailAt S i) = abs (trailAt S j) → i = j)
  /-- Assigned literals are tagged `IMPLIED` (C:44); all others are untagged. -/
  flags : ∀ lit, InRange S0.nVars lit →
    flag S lit = if ∃ i < trailLen S, trailAt S i = lit then IMPLIED else 0
  model : ∀ i < trailLen S, S.ld (S.model + abs (trailAt S i)) = if trailAt S i < 0 then 1 else 0
  /-- Each assigned literal's reason is its unit record (C:46, C:239). -/
  reasons : ∀ i < trailLen S, ∃ r ∈ parseRecords (clausesAt S0.nVars) (input.clauses.toList.take k),
    reasonOf S (trailAt S i) = 1 + r.1 ∧ r.2 = [- trailAt S i]
  /-- Each assigned literal comes from a unit clause of the input. -/
  units_input : ∀ i < trailLen S, ∃ j < k, ∃ h : j < input.clauses.size,
    input.clauses[j].toList = [- trailAt S i]
  /-- Every unit record is true at the root. -/
  units_true : ∀ r ∈ parseRecords (clausesAt S0.nVars) (input.clauses.toList.take k),
    r.2.length = 1 → ∃ i < trailLen S, trailAt S i = - r.2[0]!
  /-- No clause read so far is empty (an empty clause makes `parse` stop, C:236). -/
  nonempty : ∀ c ∈ input.clauses.toList.take k, c.size ≠ 0

/-- `buffer` holds the `size` literals of clause `k` read so far, and `rest` is the unread
tokens: the rest of clause `k`, its `0`, then the later clauses. -/
def Current (input : Input) (S : solver) (k size : Nat) (rest : List CInt) : Prop :=
  if h : k < input.clauses.size then
    size ≤ input.clauses[k].size ∧
    (∀ i < size, S.ld (S.buffer + i) = input.clauses[k][i]!) ∧
    rest = (input.clauses[k].toList.drop size) ++ 0 :: tokList (input.clauses.toList.drop (k + 1))
  else size = 0 ∧ rest = []

/-- The invariant of `parse`'s loop after `k` clauses and `size` literals of clause `k`,
with `rest` the tokens not read yet. -/
def ParseInv (input : Input) (S0 S : solver) (k size : Nat) (rest : List CInt) : Prop :=
  ParseCore input S0 S k ∧ Current input S k size rest

/-- The variable count: at least 1, and `varsOf` of the input's (V1: nonnegative). -/
theorem varsOf_pos (n : CInt) : 1 ≤ varsOf n := by unfold varsOf; split <;> omega

/-- `initCDCL`'s state satisfies the loop invariant before any token is read. -/
theorem parseInv_init {input : Input} {S0 : solver} (h0 : InitState input.nVars input.nClauses S0.mem_max S0) :
    ParseInv input S0 S0 0 0 (tokList input.clauses.toList) := by
  have hN := varsOf_pos input.nVars
  have hNv : S0.nVars = varsOf input.nVars := h0.nVars
  have hcell := h0.cells
  have hlen : trailLen S0 = 0 := by simp [trailLen, h0.assigned, h0.falseStack]
  refine ⟨⟨⟨S0.DB, S0.mem_fixed, ?_⟩, by simp, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · apply solver.ext <;> simp [withParsed, parseEnd, h0.mem_used, hNv]
  · simp only [List.take_zero, parseRecords, h0.mem_used, hNv]; exact .nil _
  · intro lit hlit
    refine ⟨[], ?_, by simp, fun link => by simp [Watches, parseRecords, Records.all]⟩
    simp only [ListFrom, h0.first, hNv]
    have hl := hlit; rw [inRange_iff, hNv] at hl
    rw [hcell _ (by simp only [firstAt]; omega)]
    have hv : lit ∈ vars (varsOf input.nVars) ∨ -lit ∈ vars (varsOf input.nVars) := by
      simp only [mem_vars]; omega
    unfold initCell
    have n1 : (vars (varsOf input.nVars)).any
        (fun v => firstAt (varsOf input.nVars) + lit == prevAt (varsOf input.nVars) + v) = false :=
      any_false_of fun v hv => by rw [mem_vars] at hv; simp [firstAt, prevAt]; omega
    have n2 : (vars (varsOf input.nVars)).any
        (fun v => firstAt (varsOf input.nVars) + lit == nextAt (varsOf input.nVars) + v - 1) = false :=
      any_false_of fun v hv => by rw [mem_vars] at hv; simp [firstAt, nextAt]; omega
    have n3 : (vars (varsOf input.nVars)).any (fun v => firstAt (varsOf input.nVars) + lit ==
        firstAt (varsOf input.nVars) + v || firstAt (varsOf input.nVars) + lit ==
        firstAt (varsOf input.nVars) - v) = true := by
      rw [List.any_eq_true]
      rcases hv with hv | hv
      · exact ⟨lit, hv, by simp⟩
      · exact ⟨-lit, hv, by simp⟩
    simp [n1, n2, n3]
  · exact ⟨by rw [h0.assigned, hNv]; exact Int.le_refl _, by simp [hlen], by simp [hlen], by simp [hlen]⟩
  · intro lit hlit
    simp only [hlen, Nat.not_lt_zero, false_and, exists_false, if_false, flag, h0.false, hNv]
    have hl := hlit; rw [inRange_iff, hNv] at hl
    rw [hcell _ (by simp only [falseAt]; omega)]
    exact initCell_zero (fun v hv => mem_vars.mp hv) (by simp only [falseAt] at *; omega)
  · simp [hlen]
  · simp [hlen]
  · simp [hlen]
  · simp [parseRecords]
  · simp
  · unfold Current
    split
    · rename_i hk
      refine ⟨by omega, by simp, ?_⟩
      obtain ⟨c, rest, hcs⟩ : ∃ c rest, input.clauses.toList = c :: rest := by
        cases h : input.clauses.toList with
        | nil =>
          have := congrArg List.length h
          rw [Array.length_toList, List.length_nil] at this; omega
        | cons c rest => exact ⟨c, rest, rfl⟩
      have h0c : input.clauses[0] = c := by
        have := congrArg (·[0]?) hcs; simp only [Array.getElem?_toList, List.getElem?_cons_zero] at this
        rw [Array.getElem?_eq_getElem hk] at this; exact Option.some.inj this
      rw [hcs, h0c]; simp [tokList]
    · rename_i hk
      have : input.clauses.toList = [] := by simp at hk ⊢; exact hk
      simp [this, tokList]

/-- During `parse` the pointer fields keep `initCDCL`'s offsets. -/
theorem ParseCore.ptrs {input : Input} {S0 S : solver} {k : Nat}
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k) :
    S.nVars = S0.nVars ∧ S.buffer = bufferAt S0.nVars ∧ S.first = firstAt S0.nVars ∧
    S.false = falseAt S0.nVars ∧ S.model = modelAt S0.nVars ∧ S.reason = reasonAt S0.nVars ∧
    S.falseStack = stackAt S0.nVars ∧ S.prev = prevAt S0.nVars ∧ S.next = nextAt S0.nVars ∧
    S.nLemmas = 0 ∧ S.mem_max = S0.mem_max := by
  obtain ⟨DB, mf, hS⟩ := h.fields
  have hN : S0.nVars = varsOf input.nVars := h0.nVars
  rw [hS]
  simp [withParsed, h0.buffer, h0.first, h0.false, h0.model, h0.reason, h0.falseStack,
    h0.prev, h0.next, h0.nLemmas, hN]

/-- A record of `parse` lies in the clause area, at or above `clausesAt`. -/
theorem ParseCore.record_ge {input : Input} {S0 S : solver} {k : Nat} (h : ParseCore input S0 S k)
    {r : Record} (hr : r ∈ parseRecords (clausesAt S0.nVars) (input.clauses.toList.take k)) :
    clausesAt S0.nVars + 2 ≤ r.1 ∧ r.1 + r.2.length < S.mem_used :=
  h.records.bounds.2 r hr

/-- `ParseCore` only reads cells outside `buffer`: a state with the same fields and the
same cells outside `buffer` satisfies it too. Used for the literal step of `parse`. -/
theorem ParseCore.frame_buffer {input : Input} {S0 S T : solver} {k : Nat}
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0) (h : ParseCore input S0 S k)
    (hT : ∃ DB, T = { S with DB := DB })
    (same : ∀ q, 0 ≤ q → (q < bufferAt S0.nVars ∨ bufferAt S0.nVars + S0.nVars ≤ q) → T.ld q = S.ld q) :
    ParseCore input S0 T k := by
  obtain ⟨DBT, hT⟩ := hT
  have hp := h.ptrs h0
  have hN := varsOf_pos input.nVars
  have hNv : S0.nVars = varsOf input.nVars := h0.nVars
  have hf : ∀ {α : Type} (f : solver → α), (∀ X DB, f { X with DB := DB } = f X) → f T = f S := by
    intro α f hf; rw [hT, hf]
  have hlen : trailLen T = trailLen S := by simp [trailLen, hT]
  have htr : ∀ i < trailLen S, trailAt T i = trailAt S i := by
    intro i hi
    have hl := h.trail.2.1
    unfold trailAt
    rw [show T.falseStack = S.falseStack by rw [hT]]
    exact same _ (by simp only [hp.2.2.2.2.2.2.1, stackAt]; omega) (Or.inr (by
      simp only [hp.2.2.2.2.2.2.1, stackAt, bufferAt]; omega))
  obtain ⟨hnv, hbuf, hfirst, hfalse, hmodel, hreason, hstack, -, -, -, -⟩ := hp
  have hTf : T.nVars = S.nVars ∧ T.mem_used = S.mem_used ∧ T.mem_fixed = S.mem_fixed ∧
      T.first = S.first ∧ T.false = S.false ∧ T.model = S.model ∧ T.reason = S.reason ∧
      T.assigned = S.assigned := by
    subst hT; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  -- every cell `ParseCore` reads lies outside `buffer`
  have far : ∀ q, bufferAt S0.nVars + S0.nVars ≤ q → T.ld q = S.ld q := fun q hq =>
    same q (by simp only [bufferAt] at hq; omega) (Or.inr hq)
  have near : ∀ q, 0 ≤ q → q < bufferAt S0.nVars → T.ld q = S.ld q := fun q h1 h2 =>
    same q h1 (Or.inl h2)
  have hbase : bufferAt S0.nVars + S0.nVars ≤ clausesAt S0.nVars := by
    simp only [bufferAt, clausesAt]; omega
  have hlit : ∀ i < trailLen S, -S0.nVars ≤ trailAt S i ∧ trailAt S i ≤ S0.nVars := by
    intro i hi; have := inRange_iff.mp (h.trail.2.2.1 i hi); omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨DB, mf, hS⟩ := h.fields
    refine ⟨DBT, mf, ?_⟩
    rw [hT]
    apply solver.ext <;> first | rfl | (rw [hS]; rfl)
  · intro hk; rw [hTf.2.2.1, hTf.2.1]; exact h.fixed hk
  · intro q hq
    rw [← h.static q hq]
    simp only [StaticCell, nextAt, prevAt, clausesAt] at hq
    rcases hq with hq | hq | hq | hq
    · exact near q (by omega) (by simp only [bufferAt]; omega)
    · exact near q (by omega) (by simp only [bufferAt]; omega)
    · exact far q (by simp only [bufferAt]; omega)
    · exact far q (by simp only [falseAt] at hq; simp only [bufferAt]; omega)
  · rw [hTf.2.1]
    exact h.records.frame fun r hr q hq => far q (by
      have := h.record_ge hr; simp only [RecordCell] at hq; omega)
  · intro lit hlit'
    rw [hTf.1] at hlit'
    obtain ⟨links, hl, hnd, hmem⟩ := h.watches lit hlit'
    refine ⟨links, ?_, hnd, hmem⟩
    rw [hTf.2.2.2.1]
    have hr := inRange_iff.mp hlit'
    rw [hnv] at hr
    exact hl.frame fun q hq => by
      rcases hq with rfl | hq
      · exact far _ (by rw [hfirst]; simp only [firstAt, bufferAt]; omega)
      · obtain ⟨r, hr', h2, hw⟩ := (hmem q).1 hq
        have := h.record_ge (by simpa [Records.all] using hr')
        exact far _ (by rcases hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega)
  · refine ⟨by rw [hTf.2.2.2.2.2.2.2]; exact h.trail.1, by rw [hlen]; exact h.trail.2.1, ?_, ?_⟩
    · intro i hi; rw [hlen] at hi; rw [htr i hi]; exact h.trail.2.2.1 i hi
    · intro i hi j hj; rw [hlen] at hi hj; rw [htr i hi, htr j hj]; exact h.trail.2.2.2 i hi j hj
  · intro lit hlit'
    have hr := inRange_iff.mp hlit'
    have e : flag T lit = flag S lit := by
      unfold flag; rw [hTf.2.2.2.2.1]
      exact far _ (by rw [hfalse]; simp only [falseAt, bufferAt]; omega)
    rw [e, h.flags lit hlit', hlen]
    congr 1
    exact propext ⟨fun ⟨i, hi, he⟩ => ⟨i, hi, by rw [htr i hi]; exact he⟩,
      fun ⟨i, hi, he⟩ => ⟨i, hi, by rw [← htr i hi]; exact he⟩⟩
  · intro i hi
    rw [hlen] at hi
    have := hlit i hi
    have ha : 0 ≤ abs (trailAt S i) ∧ abs (trailAt S i) ≤ S0.nVars := by
      rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    rw [htr i hi, hTf.2.2.2.2.2.1, near _ (by rw [hmodel]; simp only [modelAt]; omega)
      (by rw [hmodel]; simp only [modelAt, bufferAt]; omega)]
    exact h.model i hi
  · intro i hi
    rw [hlen] at hi
    obtain ⟨r, hr, e1, e2⟩ := h.reasons i hi
    refine ⟨r, hr, ?_, by rw [htr i hi]; exact e2⟩
    have := hlit i hi
    have ha : 0 ≤ abs (trailAt S i) ∧ abs (trailAt S i) ≤ S0.nVars := by
      rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    unfold reasonOf
    rw [htr i hi, hTf.2.2.2.2.2.2.1,
      far _ (by rw [hreason]; simp only [reasonAt, bufferAt]; omega)]
    exact e1
  · intro i hi; rw [hlen] at hi; rw [htr i hi]; exact h.units_input i hi
  · intro r hr h1
    obtain ⟨i, hi, he⟩ := h.units_true r hr h1
    exact ⟨i, by rw [hlen]; exact hi, by rw [htr i hi]; exact he⟩
  · exact h.nonempty

/-- A clause of a valid input fits in `buffer`: at most `varsOf nVars` literals (V3). -/
theorem clause_size_le_vars {input : Input} (valid : input.Valid) {k : Nat}
    (hk : k < input.clauses.size) : (input.clauses[k].size : CInt) ≤ varsOf input.nVars := by
  have := valid.clause_size_le _ (Array.getElem_mem hk)
  unfold varsOf; split <;> omega

/-- Reading a literal token (C:241): it is stored at `buffer[size]`. -/
theorem parseInv_lit {input : Input} {S0 S : solver} {k size : Nat} {lit : CInt} {rest : List CInt}
    (valid : input.Valid) (h0 : InitState input.nVars input.nClauses S0.mem_max S0)
    (h : ParseInv input S0 S k size (lit :: rest)) (hlit : lit ≠ 0) :
    ParseInv input S0 (S.st (S.buffer + size) lit) k (size + 1) rest := by
  obtain ⟨hc, hcur⟩ := h
  have hp := hc.ptrs h0
  have hN : S0.nVars = varsOf input.nVars := h0.nVars
  unfold Current at hcur
  split at hcur
  case isFalse => simp at hcur
  rename_i hk
  obtain ⟨hsz, hbuf, hrest⟩ := hcur
  have hcl := clause_size_le_vars valid hk
  -- the literal read is `clause[size]`, so `size < clause.size`
  have hlt : size < input.clauses[k].size := by
    rcases Nat.lt_or_ge size input.clauses[k].size with h | h
    · exact h
    · have : input.clauses[k].toList.drop size = [] := by simp; omega
      rw [this] at hrest; simp at hrest; exact absurd (by omega) hlit
  have hdrop : input.clauses[k].toList.drop size =
      input.clauses[k][size] :: input.clauses[k].toList.drop (size + 1) := by
    rw [List.drop_eq_getElem_cons (by rw [Array.length_toList]; exact hlt), Array.getElem_toList]
  rw [hdrop] at hrest
  simp only [List.cons_append, List.cons.injEq] at hrest
  obtain ⟨hl, hr⟩ := hrest
  have hw : 0 ≤ S.buffer + size := by rw [hp.2.1]; simp only [bufferAt]; omega
  refine ⟨hc.frame_buffer h0 (st_eq S _ lit) fun q hq hout => ?_, ?_⟩
  · apply ld_st_of_ne _ _ hw hq
    rw [hp.2.1]; simp only [bufferAt] at hout ⊢; omega
  · unfold Current
    rw [dif_pos hk]
    refine ⟨hlt, fun i hi => ?_, hr⟩
    rw [st_buffer]
    by_cases hi' : i = size
    · subst hi'; rw [ld_st_self _ _ hw, hl, getElem!_pos input.clauses[k] i hlt]
    · rw [ld_st_of_ne _ _ hw (by rw [hp.2.1]; simp only [bufferAt]; omega) (by omega)]
      exact hbuf i (by omega)

end MicrosatLean.Faithful.Verification
