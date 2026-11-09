import MicrosatLean.Faithful.Verification.ParseFinal

/-!
# Loading the input: `initCDCL` and `parse`

`parse` (C:216–243) either reports UNSAT (an empty clause or two opposite unit
clauses) or leaves a state where `solve`'s loop invariant holds.
-/

namespace MicrosatLean.Faithful.Verification

open Std.Do
set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- Reading token `next` (C:231): it exists, and the unread tokens start with it. -/
theorem token_read {toks : Array CInt} {next : Nat} {lit : CInt} (hget : toks[next]? = some lit) :
    next < toks.size ∧ toks.toList.drop next = lit :: toks.toList.drop (next + 1) := by
  have hlt : next < toks.size := by
    rcases Nat.lt_or_ge next toks.size with h | h
    · exact h
    · rw [Array.getElem?_eq_none h] at hget; simp at hget
  refine ⟨hlt, ?_⟩
  rw [List.drop_eq_getElem_cons (by simpa using hlt)]
  rw [Array.getElem?_eq_getElem hlt] at hget
  simp only [Option.some.injEq] at hget
  simp [hget]

/-- `parse` on a valid input with enough memory: an UNSAT answer is correct, and
otherwise the state `solve` starts its loop from (C:161) satisfies `Inv`. Used by
every theorem in `Main.lean`. -/
theorem parse_correct {input : Input} {mem_max : CInt} {S : solver} {r : CInt}
    (valid : input.Valid) (memory : memoryBound input ≤ mem_max)
    (h : parse input.nVars input.nClauses input.tokens mem_max = (S, r)) :
    (r = UNSAT ∧ input.Unsat) ∨ (r = SAT ∧ Inv input { S with res := 0 } S.head) := by
  have hS0 := initCDCL_spec (n := input.nVars) (m := input.nClauses) (mem_max := mem_max) (by
    have := parseEnd_le_memoryBound input
    have := parseEnd_take_le (clausesAt (varsOf input.nVars)) input.clauses.toList 0
    simp only [List.take_zero, parseEnd] at this; omega)
  generalize hS0def : initCDCL input.nVars input.nClauses mem_max = S0 at hS0
  have hmm : S0.mem_max = mem_max := hS0.mem_max
  have h0 : InitState input.nVars input.nClauses S0.mem_max S0 := by rw [hmm]; exact hS0
  have memory' : memoryBound input ≤ S0.mem_max := by rw [hmm]; exact memory
  have htok := tokens_toList input
  have hnc : input.nClauses = input.clauses.size := valid.nClauses_eq
  suffices key : (fun out : solver × CInt => (out.2 = UNSAT ∧ input.Unsat) ∨
      (out.2 = SAT ∧ Inv input { out.1 with res := 0 } out.1.head))
      (parse input.nVars input.nClauses input.tokens mem_max) by
    rw [h] at key; exact key
  generalize hR : parse input.nVars input.nClauses input.tokens mem_max = R
  apply Id.of_wp_run_eq hR
  mvcgen [parse] invariants
  · fun ⟨_, _, _, _, next⟩ => ULift.up (input.tokens.size - next)
  · ⇓ c => match c with
      | .inl ⟨ret, S, nZeros, size, next⟩ => ⌜ret = none ∧ ∃ k ≤ input.clauses.size,
          nZeros = (input.clauses.size : CInt) - k ∧ 0 ≤ size ∧
          ParseInv input S0 S k size.toNat (input.tokens.toList.drop next)⌝
      | .inr ⟨ret, S, nZeros, size, next⟩ => ⌜(∃ S', ret = some (S', UNSAT) ∧ input.Unsat) ∨
          (ret = none ∧ ParseCore input S0 S input.clauses.size)⌝
  case vc4.step.isTrue.h_1.isFalse =>
    rename_i S00 nZ0 b mb s2 S s1 nZ s0 sz nx hpos lit hget nxt hlit hinv
    obtain ⟨hvar, hret, k, hk, hnz, hsz, hpi⟩ := hinv
    simp [WhileVariant.eval, SVal.evalsTo, SVal.curry, SVal.uncurry] at hvar ⊢
    simp only [nxt, nx, sz, nZ, S, s0, s1, s2] at hget ⊢
    have hsz : 0 ≤ b.snd.snd.snd.fst := hsz
    have hvar : mb = input.tokens.size - b.snd.snd.snd.snd := hvar
    have hnz : b.snd.snd.fst = ↑input.clauses.size - ↑k := hnz
    obtain ⟨hlt, hdrop⟩ := token_read hget
    have hlit' : lit ≠ 0 := by simpa using hlit
    have hpi' : ParseInv input S0 b.2.1 k b.2.2.2.1.toNat
        (lit :: input.tokens.toList.drop (b.2.2.2.2 + 1)) := by
      rw [← hdrop]; exact hpi
    have := parseInv_lit valid h0 hpi' hlit'
    rw [show ((b.2.2.2.1.toNat : Nat) : CInt) = b.2.2.2.1 by omega] at this
    refine ⟨by omega, k, hk, hnz, by omega, ?_⟩
    rw [show (b.2.2.2.1 + 1).toNat = b.2.2.2.1.toNat + 1 by omega]
    exact this
  case vc1.step.isTrue.h_1.isTrue.isTrue =>
    rename_i S00 nZ0 b mb s2 S s1 nZ s0 sz nx hpos lit hget nxt hlit0 hcond hinv
    obtain ⟨-, -, k, hk, hnz, hsz, hpi⟩ := hinv
    simp only [nxt, nx, sz, nZ, S, s0, s1, s2] at hget hcond ⊢
    have hsz : 0 ≤ b.snd.snd.snd.fst := hsz
    obtain ⟨-, hdrop⟩ := token_read hget
    have hl0 : lit = 0 := by simpa using hlit0
    subst hl0
    rw [hdrop] at hpi
    obtain ⟨hkc, hsize, hrest⟩ := hpi.size_eq valid
    have hbuf := hpi.buf hkc hsize
    have hsize : b.snd.snd.snd.fst.toNat = input.clauses[k].size := hsize
    have hsz' : b.snd.snd.snd.fst = (input.clauses[k].size : CInt) := by omega
    rw [hsz'] at hcond
    left
    refine ⟨_, rfl, ?_⟩
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq] at hcond
    rcases hcond with h0' | ⟨h1', hne⟩
    · exact unsat_of_empty hkc (by omega)
    · have hc1 : input.clauses[k].size = 1 := by omega
      obtain ⟨hl, hfl⟩ := hpi.1.unit_reads valid memory' h0 hkc hbuf hc1
      have hm : input.clauses[k][0]! ∈ input.clauses[k].toList := by
        rw [getElem!_pos input.clauses[k] 0 (by omega)]; simp
      have hlit := valid.lit_range _ (Array.getElem_mem hkc) _ (by simpa using hm)
      have hv : input.nVars ≤ S0.nVars := by rw [h0.nVars]; unfold varsOf; split <;> omega
      rw [hl, hfl _ ⟨hlit.1, by omega⟩] at hne
      exact hpi.1.unsat_conflict valid h0 hkc hc1 hne
  case vc2.step.isTrue.h_1.isTrue.isFalse.isTrue =>
    rename_i S00 nZ0 b mb s2 S s1 nZ s0 sz nx hpos lit hget nxt hlit0 hnot jp hc2 hinv
    obtain ⟨hvar, -, k, hk, hnz, hsz, hpi⟩ := hinv
    simp [WhileVariant.eval, SVal.evalsTo, SVal.curry, SVal.uncurry] at hvar ⊢
    simp only [nxt, nx, sz, nZ, S, s0, s1, s2] at hget hnot hc2 ⊢
    have hsz : 0 ≤ b.snd.snd.snd.fst := hsz
    have hvar : mb = input.tokens.size - b.snd.snd.snd.snd := hvar
    have hnz : b.snd.snd.fst = ↑input.clauses.size - ↑k := hnz
    have hpi : ParseInv input S0 b.snd.fst k b.snd.snd.snd.fst.toNat
        (List.drop b.snd.snd.snd.snd input.tokens.toList) := hpi
    obtain ⟨hlt, hdrop⟩ := token_read hget
    have hl0 : lit = 0 := by simpa using hlit0
    subst hl0
    rw [hdrop] at hpi
    obtain ⟨hkc, hsize, hrest⟩ := hpi.size_eq valid
    have hbuf := hpi.buf hkc hsize
    have hsz' : b.snd.snd.snd.fst = (input.clauses[k].size : CInt) := by omega
    rw [hsz'] at hnot hc2 ⊢
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, not_or,
      not_and, Decidable.not_not] at hnot hc2
    have hm1 : input.clauses[k].size = 1 → input.clauses[k][0]! ∈ input.clauses[k].toList := by
      intro h1; rw [getElem!_pos input.clauses[k] 0 (by omega)]; simp
    have hv : input.nVars ≤ S0.nVars := by rw [h0.nVars]; unfold varsOf; split <;> omega
    have hr1 : input.clauses[k].size = 1 → InRange S0.nVars input.clauses[k][0]! ∧
        InRange S0.nVars (- input.clauses[k][0]!) := by
      intro h1
      have hlit := valid.lit_range _ (Array.getElem_mem hkc) _ (by simpa using hm1 h1)
      exact ⟨⟨hlit.1, by omega⟩, ⟨by omega, by rw [abs_neg']; omega⟩⟩
    have hc1 : input.clauses[k].size = 1 := by omega
    obtain ⟨hl, hfl⟩ := hpi.1.unit_reads valid memory' h0 hkc hbuf hc1
    obtain ⟨r1, r2⟩ := hr1 hc1
    rw [hl, hfl _ r1] at hnot
    rw [hl, hfl _ r2] at hc2
    have := hpi.1.after_assign valid memory' h0 hkc hbuf hc1 (by omega) hc2.2
    refine ⟨by omega, k + 1, by omega, by omega, ⟨this, ?_⟩⟩
    rw [hrest]; exact current_next input _ k
  case vc3.step.isTrue.h_1.isTrue.isFalse.isFalse =>
    rename_i S00 nZ0 b mb s2 S s1 nZ s0 sz nx hpos lit hget nxt hlit0 hnot jp hc2 hinv
    obtain ⟨hvar, -, k, hk, hnz, hsz, hpi⟩ := hinv
    simp [WhileVariant.eval, SVal.evalsTo, SVal.curry, SVal.uncurry] at hvar ⊢
    simp only [nxt, nx, sz, nZ, S, s0, s1, s2] at hget hnot hc2 ⊢
    have hsz : 0 ≤ b.snd.snd.snd.fst := hsz
    have hvar : mb = input.tokens.size - b.snd.snd.snd.snd := hvar
    have hnz : b.snd.snd.fst = ↑input.clauses.size - ↑k := hnz
    have hpi : ParseInv input S0 b.snd.fst k b.snd.snd.snd.fst.toNat
        (List.drop b.snd.snd.snd.snd input.tokens.toList) := hpi
    obtain ⟨hlt, hdrop⟩ := token_read hget
    have hl0 : lit = 0 := by simpa using hlit0
    subst hl0
    rw [hdrop] at hpi
    obtain ⟨hkc, hsize, hrest⟩ := hpi.size_eq valid
    have hbuf := hpi.buf hkc hsize
    have hsz' : b.snd.snd.snd.fst = (input.clauses[k].size : CInt) := by omega
    rw [hsz'] at hnot hc2 ⊢
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, bne_iff_ne, ne_eq, not_or,
      not_and, Decidable.not_not] at hnot hc2
    have hm1 : input.clauses[k].size = 1 → input.clauses[k][0]! ∈ input.clauses[k].toList := by
      intro h1; rw [getElem!_pos input.clauses[k] 0 (by omega)]; simp
    have hv : input.nVars ≤ S0.nVars := by rw [h0.nVars]; unfold varsOf; split <;> omega
    have hr1 : input.clauses[k].size = 1 → InRange S0.nVars input.clauses[k][0]! ∧
        InRange S0.nVars (- input.clauses[k][0]!) := by
      intro h1
      have hlit := valid.lit_range _ (Array.getElem_mem hkc) _ (by simpa using hm1 h1)
      exact ⟨⟨hlit.1, by omega⟩, ⟨by omega, by rw [abs_neg']; omega⟩⟩
    have hold : input.clauses[k].size = 1 →
        ∃ i < trailLen b.snd.fst, trailAt b.snd.fst i = - input.clauses[k][0]! := by
      intro hc1
      obtain ⟨hl, hfl⟩ := hpi.1.unit_reads valid memory' h0 hkc hbuf hc1
      obtain ⟨r1, r2⟩ := hr1 hc1
      have hne := hc2 (by omega)
      rw [hl, hfl _ r2] at hne
      have := hpi.1.flags _ r2
      rw [this] at hne
      split at hne
      · assumption
      · exact absurd rfl hne
    have := hpi.1.after_add valid memory' h0 hkc hbuf (fun h0s => by rw [h0s] at hnot; simp at hnot) hold
    refine ⟨by omega, k + 1, by omega, by omega, ⟨this, ?_⟩⟩
    rw [hrest]; exact current_next input _ k
  case vc5.step.isTrue.h_2 =>
    rename_i S00 nZ0 b mb s2 S s1 nZ s0 sz nx hpos o ho hget hinv
    exfalso
    obtain ⟨-, -, k, hk, hnz, hsz, hpi⟩ := hinv
    simp only [nx, nZ, s0, s1, s2] at hget hpos
    have hnz : b.snd.snd.fst = ↑input.clauses.size - ↑k := hnz
    have hpi : ParseInv input S0 b.snd.fst k b.snd.snd.snd.fst.toNat
        (List.drop b.snd.snd.snd.snd input.tokens.toList) := hpi
    have hkc : k < input.clauses.size := by omega
    have hcur := hpi.2
    unfold Current at hcur
    rw [dif_pos hkc] at hcur
    rw [getElem?_eq_head?_drop, hcur.2.2] at hget
    cases ho' : o with
    | none =>
      rw [ho'] at hget
      cases hl : input.clauses[k].toList.drop b.snd.snd.snd.fst.toNat <;> simp [hl] at hget
    | some x => exact ho x ho'
  case vc6.step.isFalse =>
    rename_i S00 nZ0 b mb s2 S s1 nZ s0 sz nx hnpos hinv
    obtain ⟨-, -, k, hk, hnz, hsz, hpi⟩ := hinv
    simp only [nZ, s1, s2] at hnpos
    have hnz : b.snd.snd.fst = ↑input.clauses.size - ↑k := hnz
    have hkc : k = input.clauses.size := by omega
    subst hkc
    exact Or.inr ⟨trivial, hpi.1⟩
  case vc7.pre =>
    refine ⟨trivial, 0, Nat.zero_le _, ?_, Int.le_refl 0, ?_⟩
    · show (initCDCL input.nVars input.nClauses mem_max).nClauses = _
      rw [hS0def, hS0.nClauses, hnc]; simp
    · show ParseInv input S0 (initCDCL input.nVars input.nClauses mem_max) 0 0
        (List.drop 0 input.tokens.toList)
      rw [hS0def, List.drop_zero, htok]
      exact parseInv_init h0
  case vc8.post.success.h_1 =>
    rename_i S00 nZ0 r' a hsome hinv
    rcases hinv with ⟨S', he, hu⟩ | ⟨he, -⟩
    · rw [hsome] at he
      simp only [Option.some.injEq] at he
      subst he
      exact Or.inl ⟨rfl, hu⟩
    · rw [hsome] at he; simp at he
  case vc9.post.success.h_2 =>
    rename_i S00 nZ0 r' hnone hinv
    rcases hinv with ⟨S', he, -⟩ | ⟨-, hcore⟩
    · rw [hnone] at he; simp at he
    · exact Or.inr ⟨by first | trivial | rfl, ParseCore.inv valid memory' h0 hcore⟩

end MicrosatLean.Faithful.Verification
