import MicrosatLean.Fast.Verification.ParseLoop

/-!
# `parse` and `initCDCL` of the fast port (C:181–243)

`parse_fast` is the faithful `parse_correct` for the fast `parse`, with running out of
memory as an outcome (`none`, or `OOM`).

The proof follows `parse_correct` (`Faithful/Verification/Init.lean`): the faithful state of
a fast state during `parse` is `pabs` (the abstraction with `nClauses` as `initCDCL` sets
it). `initCDCL_fast` gives `InitState` for the initial one (`ParseInit.lean`),
`parseLoop_spec` keeps `ParseInv` through the clause loop (`ParseLoop.lean`, with the
faithful step lemmas restated for the fast `addClause` in `ParseStep.lean`), and the
faithful `ParseCore.inv` gives `Inv` at the end. `Inv` does not read `nClauses`.
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- `parse` on a valid input: out of memory, or a correct UNSAT (an empty clause or two
opposite units), or the invariant at the top of `solve`'s loop with the cursor at `head`. -/
theorem parse_fast {input : Input} (valid : input.Valid) :
    match parse input.nVars input.nClauses input.tokens with
    | none => True
    | some (L, s, r) => r = OOM ∨ (r = UNSAT ∧ input.Unsat) ∨
        (r = SAT ∧ Bounds L s ∧ ∃ fa sl, Inv input (abs L s (memoryBound input) fa sl) s.head.toInt) := by
  unfold parse
  by_cases hn : input.nVars > 107374181
  · rw [if_pos hn]; trivial
  rw [if_neg hn]
  obtain ⟨L, s0, hinit, hok, hsz, hmu, hst⟩ := initCDCL_fast valid.nVars_nonneg (by omega)
  rw [hinit]
  dsimp only
  have h0 : InitState input.nVars input.nClauses (pabs input L s0).mem_max (pabs input L s0) :=
    hst input.nClauses (memoryBound input) 0 0
  have hpi : ParseInv input (pabs input L s0) (pabs input L s0) 0 ((0 : Cell).toInt.toNat)
      (input.tokens.toList.drop 0) := by
    rw [List.drop_zero, tokens_toList]; exact parseInv_init h0
  have hout := parseLoop_spec valid (by omega) h0 L _ s0 0 input.nClauses 0 0 rfl hsz hmu
    (Nat.zero_le _) (by rw [valid.nClauses_eq]; simp) (by decide) hpi
  generalize parseLoop L s0 input.tokens 0 input.nClauses 0 = out at hout ⊢
  obtain ⟨s, r⟩ := out
  rcases hout with h | h | ⟨hr, hsz', hmu', hcore⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · dsimp only at hr hsz' hmu' hcore ⊢
    have hml : s.maxLemmas.toInt = 2000 := by
      obtain ⟨DB, mf, hS⟩ := hcore.fields
      have := congrArg solver.maxLemmas hS
      simp only [withParsed] at this
      rw [h0.maxLemmas] at this
      exact this
    refine Or.inr (Or.inr ⟨hr, ⟨hsz', hok, hmu', by omega⟩, 0, 0, ?_⟩)
    exact Inv.withNClauses (ParseCore.inv valid (Int.le_refl _) h0 hcore) 0

end MicrosatLean.Fast.Verification
