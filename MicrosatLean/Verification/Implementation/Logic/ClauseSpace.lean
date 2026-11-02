import Std.Sat.CNF

namespace MicrosatLean.Verification.Implementation.Logic.ClauseSpace

open Std.Sat

/-!
A finite space of canonical, nontautological clauses. It is a proof-level
construction, not the executable clause representation. Connecting this bound
to the solver requires proving that learned clauses have bounded variables and
that simultaneously retained clauses have distinct canonical representatives.
-/

abbrev Literals := List (Std.Sat.Literal Nat)

def Bounded (n : Nat) (clause : Literals) : Prop :=
  ∀ lit ∈ clause, 1 ≤ lit.1 ∧ lit.1 ≤ n

def NoDuplicateVariables (clause : Literals) : Prop :=
  (clause.map Prod.fst).Nodup

/-- Repeated occurrences with the same polarity are permitted here. -/
def NoClash (clause : Literals) : Prop :=
  ∀ var, (var, true) ∈ clause → (var, false) ∉ clause

/-- Each variable is absent, positive, or negative. Variables are in descending
order, so every choice has a single canonical list representation. -/
def clauseUniverse : Nat → List Literals
  | 0 => [[]]
  | n + 1 => clauseUniverse n ++
      ((clauseUniverse n).map ((n + 1, true) :: ·) ++
       (clauseUniverse n).map ((n + 1, false) :: ·))

@[simp] theorem clauseUniverse_length (n : Nat) : (clauseUniverse n).length = 3 ^ n := by
  induction n with
  | zero => simp [clauseUniverse]
  | succ n ih =>
    simp [clauseUniverse, ih, Nat.pow_succ]
    omega

private def selected (clause : Literals) (var : Nat) : Option Bool :=
  if (var, true) ∈ clause then some true
  else if (var, false) ∈ clause then some false
  else none

/-- A deterministic representative independent of the original literal order.
For tautological inputs the positive polarity wins; coverage theorems therefore
state the explicit nonclashing precondition. -/
def canonicalize : Nat → Literals → Literals
  | 0, _ => []
  | n + 1, clause =>
    match selected clause (n + 1) with
    | none => canonicalize n clause
    | some pol => (n + 1, pol) :: canonicalize n clause

private theorem selected_eq_some_iff {clause : Literals} (h : NoClash clause)
    (var : Nat) (pol : Bool) : selected clause var = some pol ↔ (var, pol) ∈ clause := by
  cases pol <;> by_cases hp : (var, true) ∈ clause
  · simp [selected, hp, h var hp]
  · simp [selected, hp]
  · simp [selected, hp]
  · simp [selected, hp]

theorem canonicalize_mem_universe (n : Nat) (clause : Literals) :
    canonicalize n clause ∈ clauseUniverse n := by
  induction n with
  | zero => simp [canonicalize, clauseUniverse]
  | succ n ih =>
    unfold canonicalize
    cases hsel : selected clause (n + 1) with
    | none => exact List.mem_append_left _ ih
    | some pol =>
      cases pol
      · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_map.mpr ⟨_, ih, rfl⟩))
      · exact List.mem_append_right _ (List.mem_append_left _ (List.mem_map.mpr ⟨_, ih, rfl⟩))

private theorem mem_canonicalize_succ {clause : Literals} {lit : Std.Sat.Literal Nat}
    (n : Nat) :
    lit ∈ canonicalize (n + 1) clause ↔
      (lit.1 = n + 1 ∧ selected clause (n + 1) = some lit.2) ∨
        lit ∈ canonicalize n clause := by
  rcases lit with ⟨var, pol⟩
  cases hsel : selected clause (n + 1) with
  | none => simp [canonicalize, hsel]
  | some chosen => simp [canonicalize, hsel, Prod.mk.injEq, eq_comm]

theorem mem_canonicalize {clause : Literals} (h : NoClash clause)
    (n : Nat) (lit : Std.Sat.Literal Nat) :
    lit ∈ canonicalize n clause ↔ lit ∈ clause ∧ 1 ≤ lit.1 ∧ lit.1 ≤ n := by
  induction n with
  | zero => simp [canonicalize]; omega
  | succ n ih =>
    rw [mem_canonicalize_succ, selected_eq_some_iff h, ih]
    constructor
    · rintro (⟨hvar, hmem⟩ | ⟨hmem, hlo, hhi⟩)
      · have heq : lit = (n + 1, lit.2) := Prod.ext hvar rfl
        exact ⟨heq.symm ▸ hmem, by omega, by omega⟩
      · exact ⟨hmem, hlo, by omega⟩
    · rintro ⟨hmem, hlo, hhi⟩
      by_cases hvar : lit.1 = n + 1
      · apply Or.inl
        refine ⟨hvar, ?_⟩
        have heq : lit = (n + 1, lit.2) := Prod.ext hvar rfl
        exact heq ▸ hmem
      · exact Or.inr ⟨hmem, hlo, by omega⟩

theorem noClash_of_noDuplicateVariables {clause : Literals}
    (h : NoDuplicateVariables clause) : NoClash clause := by
  intro var hpos hneg
  obtain ⟨i, hi, hpositive⟩ := List.mem_iff_getElem.mp hpos
  obtain ⟨j, hj, hnegative⟩ := List.mem_iff_getElem.mp hneg
  have hi' : i < (clause.map Prod.fst).length := by simpa using hi
  have hj' : j < (clause.map Prod.fst).length := by simpa using hj
  have hij : i = j := h.eq_of_getElem_eq hi' hj' (by simp [hpositive, hnegative])
  subst j
  have hfalse : (var, true) = (var, false) := hpositive.symm.trans hnegative
  exact Bool.noConfusion (congrArg Prod.snd hfalse)

/-- Every bounded, nonclashing clause has a finite representative with exactly
the same literal membership, allowing duplicate removal and reordering. -/
theorem canonicalize_coverage {n : Nat} {clause : Literals}
    (hb : Bounded n clause) (hn : NoClash clause) :
    ∀ lit, lit ∈ canonicalize n clause ↔ lit ∈ clause := by
  intro lit
  rw [mem_canonicalize hn]
  exact ⟨And.left, fun hmem => ⟨hmem, hb lit hmem⟩⟩

/-- Canonicalization only inspects the membership of variables in its bound. -/
theorem canonicalize_eq_of_relevant_mem_iff (n : Nat) {left right : Literals}
    (h : ∀ var, var ≤ n → ∀ pol, (var, pol) ∈ left ↔ (var, pol) ∈ right) :
    canonicalize n left = canonicalize n right := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have htail := ih (fun var hv pol => h var (Nat.le.step hv) pol)
    have hpos := h (n + 1) (Nat.le_refl _) true
    have hneg := h (n + 1) (Nat.le_refl _) false
    simp only [canonicalize, selected, hpos, hneg, htail]

theorem canonicalize_eq_of_mem_iff (n : Nat) {left right : Literals}
    (h : ∀ lit, lit ∈ left ↔ lit ∈ right) :
    canonicalize n left = canonicalize n right :=
  canonicalize_eq_of_relevant_mem_iff n (fun var _ pol => h (var, pol))

/-- On bounded, nonclashing clauses, equality of representatives is exactly
equality of literal membership, independently of order and multiplicity. -/
theorem canonicalize_eq_iff {n : Nat} {left right : Literals}
    (hlb : Bounded n left) (hln : NoClash left)
    (hrb : Bounded n right) (hrn : NoClash right) :
    canonicalize n left = canonicalize n right ↔
      ∀ lit, lit ∈ left ↔ lit ∈ right := by
  constructor
  · intro heq lit
    rw [← canonicalize_coverage hlb hln lit, ← canonicalize_coverage hrb hrn lit, heq]
  · exact canonicalize_eq_of_mem_iff n

/-- A nonrepeating history of canonical clauses has at most `3^n` entries.
This is only the finite-space fact: actual solver freshness is a separate proof. -/
theorem distinct_canonicalized_length_le (n : Nat) (history : List Literals)
    (h : (history.map (canonicalize n)).Nodup) : history.length ≤ 3 ^ n := by
  have hbound : (history.map (canonicalize n)).length ≤ (clauseUniverse n).length :=
    h.length_le_of_subset (by
      intro clause hmem
      rcases List.mem_map.mp hmem with ⟨original, _, rfl⟩
      exact canonicalize_mem_universe n original)
  simpa using hbound

end MicrosatLean.Verification.Implementation.Logic.ClauseSpace
