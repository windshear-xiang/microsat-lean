import MicrosatLean.CDCL.Search
import MicrosatLean.Verification.Representation.State

namespace MicrosatLean.Verification.Propagation

open CDCL
open Representation

/-- A successful concrete scan returns a nonfalse literal within its budget.
Every position it passes contains a false, nonzero literal. -/
theorem replacementScan_some {fuel : Nat} {arena marks : Array Nat} {start pos : Nat}
    (found : replacementScan fuel arena marks start = some pos) :
    start ≤ pos ∧ pos < start + fuel ∧ arena[pos]! ≠ 0 ∧ marks[arena[pos]!]! = 0 ∧
      ∀ i, start ≤ i → i < pos → arena[i]! ≠ 0 ∧ marks[arena[i]!]! ≠ 0 := by
  induction fuel generalizing start with
  | zero => simp [replacementScan] at found
  | succ fuel ih =>
    simp only [replacementScan] at found
    split at found
    · simp at found
    · rename_i nonzero
      split at found
      · have equal : start = pos := Option.some.inj found
        subst pos
        refine ⟨Nat.le_refl _, by omega, ?_, ?_, ?_⟩
        · simpa using nonzero
        · simpa using ‹(marks[arena[start]!]! == 0) = true›
        · intro i lower upper
          omega
      · rename_i marked
        obtain ⟨lower, upper, nz, unmarked, skipped⟩ := ih found
        refine ⟨by omega, by omega, nz, unmarked, ?_⟩
        intro i hlo hhi
        by_cases equal : i = start
        · subst i
          exact ⟨by simpa using nonzero, by simpa using marked⟩
        · exact skipped i (by omega) hhi

/-- If a scan finds no replacement, each nonzero position before a terminator
and within the scan budget is false. The premise excludes crossing zero. -/
theorem replacementScan_none {fuel : Nat} {arena marks : Array Nat} {start : Nat}
    (missing : replacementScan fuel arena marks start = none)
    {pos : Nat} (lower : start ≤ pos) (upper : pos < start + fuel)
    (nonzero : ∀ i, start ≤ i → i ≤ pos → arena[i]! ≠ 0) :
    marks[arena[pos]!]! ≠ 0 := by
  induction fuel generalizing start with
  | zero => omega
  | succ fuel ih =>
    have head := nonzero start (Nat.le_refl _) lower
    simp only [replacementScan, beq_iff_eq, head, ↓reduceIte] at missing
    split at missing
    · simp at missing
    · rename_i marked
      by_cases equal : pos = start
      · simpa [equal] using marked
      · exact ih missing (by omega) (by omega)
          (fun i hlo hhi => nonzero i (by omega) hhi)

/-- For an actual terminated arena clause, failure to find a replacement means
all literals beyond the two watched positions are marked false. -/
theorem replacement_none_of_packed {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits)
    (missing : replacement s.arena s.marks clauseId = none)
    {i : Nat} (afterWatches : 2 ≤ i) (within : i < lits.size) :
    s.mark lits[i]! ≠ 0 := by
  have endBound := packed.endBound
  have position : clauseId + i < s.arena.size := by omega
  have literal := packed.literals i within
  have scan : s.marks[s.arena[clauseId + i]!]! ≠ 0 := by
    apply replacementScan_none (start := clauseId + 2) (pos := clauseId + i) missing
      (by omega) (by omega)
    intro cursor lo hi
    have offset : cursor - clauseId < lits.size := by omega
    have hc : clauseId + (cursor - clauseId) = cursor := by omega
    have data := packed.literals (cursor - clauseId) offset
    rw [hc] at data
    have mem : lits[cursor - clauseId]! ∈ lits := by
      simpa only [getElem!_pos lits (cursor - clauseId) offset] using Array.getElem_mem offset
    change s.db cursor ≠ 0
    rw [data]
    exact (packed.wellFormed _ mem).nonzero
  change s.marks[lits[i]!]! ≠ 0
  simpa only [← literal, State.db] using scan

/-- A successful scan of a clause with two watches stays inside that clause;
in particular, its budget cannot let it pass the clause's zero terminator. -/
theorem replacement_some_of_packed {s : State} {clauseId : Nat} {lits : Array Lit}
    (packed : PackedClause s clauseId lits) (twoWatches : 2 ≤ lits.size)
    {pos : Nat} (found : replacement s.arena s.marks clauseId = some pos) :
    ∃ i, 2 ≤ i ∧ i < lits.size ∧ pos = clauseId + i ∧ s.mark lits[i]! = 0 := by
  obtain ⟨lower, _, nonzero, unmarked, skipped⟩ := replacementScan_some found
  have beforeEnd : pos < clauseId + lits.size := by
    by_cases before : pos < clauseId + lits.size
    · exact before
    · have afterEnd : clauseId + lits.size ≤ pos := by omega
      have zero : s.arena[clauseId + lits.size]! = 0 := packed.terminator
      apply False.elim
      by_cases equal : pos = clauseId + lits.size
      · exact nonzero (equal ▸ zero)
      · have nz := (skipped (clauseId + lits.size) (by omega) (by omega)).1
        exact nz zero
  refine ⟨pos - clauseId, by omega, by omega, by omega, ?_⟩
  have offset : pos - clauseId < lits.size := by omega
  have data := packed.literals (pos - clauseId) offset
  have position : clauseId + (pos - clauseId) = pos := by omega
  rw [position] at data
  change s.marks[lits[pos - clauseId]!]! = 0
  simpa only [← data, State.db] using unmarked

end MicrosatLean.Verification.Propagation
