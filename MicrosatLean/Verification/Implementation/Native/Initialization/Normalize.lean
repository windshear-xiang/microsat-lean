import MicrosatLean.Verification.Implementation.Native.Specification
import MicrosatLean.Verification.Implementation.Native.Representation.State

namespace MicrosatLean.Verification.Implementation.Native.Initialization

open CDCL Representation

/-- A clause contains a literal together with its encoded complement. -/
def ComplementPair (literals : List Lit) : Prop :=
  ∃ lit ∈ literals, lit.negate ∈ literals

/-- The shared table covers both polarities of all declared variables. -/
def StampCoverage (numVars : Nat) (stamps : Array Nat) : Prop :=
  2 * (numVars + 1) ≤ stamps.size

/-- The caller's new clause stamp has not appeared in the old table. -/
def FreshStamp (stamp : Nat) (stamps : Array Nat) : Prop :=
  0 < stamp ∧ ∀ i, i < stamps.size → stamps[i]! ≠ stamp

/-- Exact observable effects of the actual clause-normalization loop. -/
structure NormalizationSpec (numVars stamp : Nat) (old : Array Nat)
    (clause : Array Lit) (result : NormalizedClause) : Prop where
  membership : ∀ lit, lit ∈ result.lits ↔ lit ∈ clause
  noDuplicates : result.lits.toList.Nodup
  tautology : result.tautology = true ↔ ComplementPair clause.toList
  stampsSize : result.stamps.size = old.size
  stampsValues : ∀ i, i < old.size →
    result.stamps[i]! = if i ∈ clause then stamp else old[i]!
  wellFormed : ClauseWellFormed numVars result.lits

private def advance (stamp : Nat) (result : NormalizedClause) (lit : Lit) : NormalizedClause :=
  {
    lits := if result.stamps[lit]! == stamp then result.lits else result.lits.push lit
    stamps := if result.stamps[lit]! == stamp then result.stamps else result.stamps.set! lit stamp
    tautology := if result.stamps[lit.negate]! == stamp then true else result.tautology }

/-- This is the literal body of `normalizeClause`, named only to state the
invariant of its existing `forIn` loop. The execution equation below unfolds
the real implementation; it does not introduce another production normalizer. -/
private def normalizeBody (numVars stamp : Nat) (lit : Lit) (initial : NormalizedClause) :
    Except String (ForInStep NormalizedClause) := do
  let mut result := initial
  if lit.var == 0 || lit.var > numVars then
    throw s!"literal {lit.toInt} is outside declared variable range 1..{numVars}"
  if result.stamps[lit.negate]! == stamp then
    result := { result with tautology := true }
  if result.stamps[lit]! != stamp then
    result := { result with stamps := result.stamps.set! lit stamp, lits := result.lits.push lit }
  return .yield result

private theorem normalizeClause_eq_forIn (numVars stamp : Nat) (stamps : Array Nat)
    (clause : Array Lit) :
    normalizeClause numVars stamp stamps clause =
      forIn clause.toList (⟨#[], stamps, false⟩ : NormalizedClause) (normalizeBody numVars stamp) := by
  simp only [normalizeClause, Array.forIn_toList]
  simp
  congr 1
  funext lit result
  simp [normalizeBody]

private theorem normalizeBody_valid {numVars stamp : Nat} {lit : Lit}
    (hLit : LiteralBound numVars lit) (result : NormalizedClause) :
    normalizeBody numVars stamp lit result = .ok (.yield (advance stamp result lit)) := by
  have nonzero : lit.var ≠ 0 := by have := hLit.1; omega
  have upper : ¬ lit.var > numVars := by have := hLit.2; omega
  rcases result with ⟨lits, stamps, tautology⟩
  cases tautology <;>
    by_cases direct : stamps[lit]! = stamp <;>
    by_cases opposite : stamps[lit.negate]! = stamp <;>
    simp [normalizeBody, advance, nonzero, upper, direct, opposite] <;> rfl

private structure LoopInvariant (stamp : Nat) (old : Array Nat)
    (seen : List Lit) (result : NormalizedClause) : Prop where
  membership : ∀ lit, lit ∈ result.lits ↔ lit ∈ seen
  noDuplicates : result.lits.toList.Nodup
  tautology : result.tautology = true ↔ ComplementPair seen
  stampsSize : result.stamps.size = old.size
  stampsValues : ∀ i, i < old.size →
    result.stamps[i]! = if i ∈ seen then stamp else old[i]!

private theorem stamped_iff_mem {stamp : Nat} {old : Array Nat} {seen : List Lit}
    {result : NormalizedClause} (hFresh : FreshStamp stamp old)
    (hInv : LoopInvariant stamp old seen result) {lit : Lit} (hIndex : lit < old.size) :
    result.stamps[lit]! = stamp ↔ lit ∈ seen := by
  rw [hInv.stampsValues lit hIndex]
  by_cases hMem : lit ∈ seen
  · simp [hMem]
  · simp [hMem, hFresh.2 lit hIndex]

private theorem complementPair_append_singleton (seen : List Lit) (lit : Lit) :
    ComplementPair (seen ++ [lit]) ↔ ComplementPair seen ∨ lit.negate ∈ seen := by
  constructor
  · rintro ⟨other, hOther, hNeg⟩
    simp only [List.mem_append, List.mem_singleton] at hOther hNeg
    rcases hOther with hOther | equal
    · rcases hNeg with hNeg | equal
      · exact Or.inl ⟨other, hOther, hNeg⟩
      · right
        have inverse : other = lit.negate := by
          simpa only [negate_negate] using congrArg Lit.negate equal
        simpa only [inverse] using hOther
    · subst other
      rcases hNeg with hNeg | equal
      · exact Or.inr hNeg
      · exact False.elim (negate_ne lit equal)
  · rintro (⟨other, hOther, hNeg⟩ | hNeg)
    · exact ⟨other, List.mem_append_left _ hOther, List.mem_append_left _ hNeg⟩
    · exact ⟨lit, by simp, List.mem_append_left _ hNeg⟩

private theorem advance_tautology {stamp : Nat} {old : Array Nat} {seen : List Lit}
    {result : NormalizedClause} {lit : Lit} (hFresh : FreshStamp stamp old)
    (hInv : LoopInvariant stamp old seen result) (hNeg : lit.negate < old.size) :
    (advance stamp result lit).tautology = true ↔ ComplementPair (seen ++ [lit]) := by
  by_cases stamped : result.stamps[lit.negate]! = stamp
  · have hMember := (stamped_iff_mem hFresh hInv hNeg).mp stamped
    have hPair : ComplementPair (seen ++ [lit]) :=
      (complementPair_append_singleton seen lit).mpr (Or.inr hMember)
    simp [advance, stamped, hPair]
  · have hAbsent : lit.negate ∉ seen :=
      fun member => stamped ((stamped_iff_mem hFresh hInv hNeg).mpr member)
    simpa [advance, stamped, complementPair_append_singleton, hAbsent] using hInv.tautology

private theorem advance_invariant {stamp : Nat} {old : Array Nat} {seen : List Lit}
    {result : NormalizedClause} {lit : Lit} (hFresh : FreshStamp stamp old)
    (hInv : LoopInvariant stamp old seen result)
    (hIndex : lit < old.size) (hNeg : lit.negate < old.size) :
    LoopInvariant stamp old (seen ++ [lit]) (advance stamp result lit) := by
  have hTaut := advance_tautology hFresh hInv hNeg
  by_cases duplicate : lit ∈ seen
  · have stamped : result.stamps[lit]! = stamp := (stamped_iff_mem hFresh hInv hIndex).mpr duplicate
    have unchanged : ∀ other, other ∈ seen ++ [lit] ↔ other ∈ seen := by
      intro other
      simp only [List.mem_append, List.mem_singleton]
      constructor
      · rintro (h | equal)
        · exact h
        · simpa only [equal] using duplicate
      · exact Or.inl
    constructor
    · intro other
      simpa [advance, stamped, unchanged] using hInv.membership other
    · simpa [advance, stamped] using hInv.noDuplicates
    · exact hTaut
    · simpa [advance, stamped] using hInv.stampsSize
    · intro other hOther
      simpa [advance, stamped, unchanged] using hInv.stampsValues other hOther
  · have unstamped : result.stamps[lit]! ≠ stamp :=
      fun h => duplicate ((stamped_iff_mem hFresh hInv hIndex).mp h)
    have absent : lit ∉ result.lits.toList := by
      intro member
      apply duplicate
      exact (hInv.membership lit).mp (by simpa using member)
    constructor
    · intro other
      simp [advance, unstamped, hInv.membership, List.mem_append]
    · simp only [advance, beq_eq_false_iff_ne.mpr unstamped, Bool.false_eq_true, ite_false,
        Array.toList_push, List.nodup_append]
      refine ⟨hInv.noDuplicates, by simp, ?_⟩
      intro a hA b hB equal
      have hB : b = lit := by simpa using hB
      apply absent
      simpa only [equal, hB] using hA
    · exact hTaut
    · simp [advance, unstamped, hInv.stampsSize]
    · intro other hOther
      by_cases equal : lit = other
      · subst other
        have inBounds : lit < result.stamps.size := by simpa [hInv.stampsSize] using hIndex
        rw [show (advance stamp result lit).stamps = result.stamps.set! lit stamp by
          simp [advance, unstamped]]
        rw [Array.getElem!_set!_self _ _ _ inBounds]
        simp
      · rw [show (advance stamp result lit).stamps = result.stamps.set! lit stamp by
          simp [advance, unstamped]]
        rw [Array.getElem!_set!_ne _ _ _ _ equal, hInv.stampsValues other hOther]
        simp only [List.mem_append, List.mem_singleton]
        have different : other ≠ lit := Ne.symm equal
        simp [different]

private theorem initial_invariant (stamp : Nat) (old : Array Nat) :
    LoopInvariant stamp old [] ⟨#[], old, false⟩ := by
  constructor
  · simp
  · simp
  · simp [ComplementPair]
  · rfl
  · simp

private theorem normalize_loop {numVars stamp : Nat} {old : Array Nat}
    (hCoverage : StampCoverage numVars old) (hFresh : FreshStamp stamp old)
    (remaining : List Lit) (hValid : ∀ lit ∈ remaining, LiteralBound numVars lit)
    (seen : List Lit) (initial : NormalizedClause)
    (hInv : LoopInvariant stamp old seen initial) :
    ∃ result, forIn remaining initial (normalizeBody numVars stamp) = .ok result ∧
      LoopInvariant stamp old (seen ++ remaining) result := by
  induction remaining generalizing seen initial with
  | nil => exact ⟨initial, rfl, by simpa using hInv⟩
  | cons lit tail ih =>
    have hLit : LiteralBound numVars lit := hValid lit (by simp)
    have hIndex : lit < old.size := Nat.lt_of_lt_of_le hLit.index hCoverage
    have hNeg : lit.negate < old.size := Nat.lt_of_lt_of_le hLit.negate.index hCoverage
    have hAdvanced := advance_invariant hFresh hInv hIndex hNeg
    obtain ⟨result, hRun, hResult⟩ := ih
      (by intro other hOther; exact hValid other (by simp [hOther]))
      (seen ++ [lit]) (advance stamp initial lit) hAdvanced
    refine ⟨result, ?_, ?_⟩
    · rw [List.forIn_cons, normalizeBody_valid hLit initial]
      exact hRun
    · simpa [List.append_assoc] using hResult

/-- Valid input clauses normalize successfully, preserving exact membership
and detecting precisely the complementary pairs that justify dropping a clause. -/
theorem normalizeClause_correct {numVars stamp : Nat} {old : Array Nat} {clause : Array Lit}
    (hCoverage : StampCoverage numVars old) (hFresh : FreshStamp stamp old)
    (hValid : ClauseWellFormed numVars clause) :
    ∃ result, normalizeClause numVars stamp old clause = .ok result ∧
      NormalizationSpec numVars stamp old clause result := by
  have hList : ∀ lit ∈ clause.toList, LiteralBound numVars lit := by
    intro lit hLit
    exact hValid lit (by simpa using hLit)
  obtain ⟨result, hRun, hInv⟩ := normalize_loop hCoverage hFresh clause.toList hList []
    ⟨#[], old, false⟩ (initial_invariant stamp old)
  refine ⟨result, ?_, ?_⟩
  · simpa only [normalizeClause_eq_forIn] using hRun
  · have hInv : LoopInvariant stamp old clause.toList result := by simpa using hInv
    constructor
    · intro lit; simpa using hInv.membership lit
    · exact hInv.noDuplicates
    · exact hInv.tautology
    · exact hInv.stampsSize
    · intro i hI; simpa using hInv.stampsValues i hI
    · intro lit hLit
      exact hValid lit (by simpa using (hInv.membership lit).mp hLit)

theorem normalizeClause_spec_of_success {numVars stamp : Nat} {old : Array Nat}
    {clause : Array Lit} {result : NormalizedClause}
    (hCoverage : StampCoverage numVars old) (hFresh : FreshStamp stamp old)
    (hValid : ClauseWellFormed numVars clause)
    (hSuccess : normalizeClause numVars stamp old clause = .ok result) :
    NormalizationSpec numVars stamp old clause result := by
  obtain ⟨actual, hRun, hSpec⟩ := normalizeClause_correct hCoverage hFresh hValid
  have equal : actual = result := Except.ok.inj (hRun.symm.trans hSuccess)
  exact equal ▸ hSpec

theorem NormalizationSpec.preserves_sat {numVars stamp : Nat} {old : Array Nat}
    {clause : Array Lit} {result : NormalizedClause}
    (hSpec : NormalizationSpec numVars stamp old clause result) (a : Nat → Bool) :
    Std.Sat.CNF.Clause.Sat a (clauseView result.lits) ↔
      Std.Sat.CNF.Clause.Sat a (clauseView clause) :=
  clauseView_sat_iff_of_mem_iff hSpec.membership a

theorem NormalizationSpec.tautology_sat {numVars stamp : Nat} {old : Array Nat}
    {clause : Array Lit} {result : NormalizedClause}
    (hSpec : NormalizationSpec numVars stamp old clause result)
    (hTautology : result.tautology = true) :
    ∀ a, Std.Sat.CNF.Clause.Sat a (clauseView clause) := by
  obtain ⟨lit, hLit, hNeg⟩ := hSpec.tautology.mp hTautology
  exact clauseView_sat_of_complement (by simpa using hLit) (by simpa using hNeg)

theorem NormalizationSpec.stamps_le {numVars stamp : Nat} {old : Array Nat}
    {clause : Array Lit} {result : NormalizedClause}
    (hSpec : NormalizationSpec numVars stamp old clause result)
    (hOld : ∀ i, i < old.size → old[i]! ≤ stamp) :
    ∀ i, i < result.stamps.size → result.stamps[i]! ≤ stamp := by
  intro i hI
  have hIndex : i < old.size := by simpa [hSpec.stampsSize] using hI
  rw [hSpec.stampsValues i hIndex]
  split
  · exact Nat.le_refl _
  · exact hOld i hIndex

theorem NormalizationSpec.stamped_iff_mem {numVars stamp : Nat} {old : Array Nat}
    {clause : Array Lit} {result : NormalizedClause}
    (hSpec : NormalizationSpec numVars stamp old clause result)
    (hFresh : FreshStamp stamp old) {lit : Lit} (hIndex : lit < old.size) :
    result.stamps[lit]! = stamp ↔ lit ∈ clause := by
  rw [hSpec.stampsValues lit hIndex]
  by_cases hMem : lit ∈ clause
  · simp [hMem]
  · simp [hMem, hFresh.2 lit hIndex]

/-- Successive clause indices provide fresh stamps when all old stamps are
bounded by the current index, as in the executable initialization loop. -/
theorem NormalizationSpec.fresh_next {numVars stamp : Nat} {old : Array Nat}
    {clause : Array Lit} {result : NormalizedClause}
    (hSpec : NormalizationSpec numVars stamp old clause result)
    (hOld : ∀ i, i < old.size → old[i]! ≤ stamp) :
    FreshStamp (stamp + 1) result.stamps := by
  constructor
  · omega
  · intro i hI
    have bound := hSpec.stamps_le hOld i hI
    omega

end MicrosatLean.Verification.Implementation.Native.Initialization
