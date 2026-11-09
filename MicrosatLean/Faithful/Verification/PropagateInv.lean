import MicrosatLean.Faithful.Verification.AddRecord
import MicrosatLean.Faithful.Verification.Push
import MicrosatLean.Faithful.Verification.LemmaCount
import MicrosatLean.Faithful.Verification.Assign

/-!
# The invariants of `propagate`'s loops (C:132–158)

`propagate` processes the trail literals from `processed` on (outer loop, C:135), visits
the watch list of each (watch loop, C:138), and scans each visited clause for a new
literal to watch (scan loop, C:143). `PMode` says when its `forced` flag (C:134) is set,
`Rel` relates the current state to the one `propagate` started from, and `WInv` is the
watch loop's invariant: the list is split at the cursor `watch`, and the watched-literal
invariant holds except for the records not yet visited.
-/

namespace MicrosatLean.Faithful.Verification

/-- `propagate`'s `forced` flag `f` is set exactly when the whole trail is at the root;
otherwise the root is below `forced` and the last decision is at or below position `P`,
the literal being processed. No decision is above `P`. -/
def PMode (S : solver) (f : CInt) (P : Nat) : Prop :=
  ((f ≠ 0 ∧ ∀ i < trailLen S, RootLevel S i) ∨
   (f = 0 ∧ (∀ i < trailLen S, RootLevel S i → i < forcedPos S) ∧
     (P < trailLen S → ∃ D, forcedPos S ≤ D ∧ D ≤ P ∧ IsDecision S D))) ∧
  ∀ k, P < k → k < trailLen S → ¬ IsDecision S k

/-- How the current state relates to `S0`, where `propagate` started: same `maxLemmas`;
either no conflict yet (the same order, the trail only extended) or new lemmas. -/
def Rel (S0 : solver) (vs0 : List CInt) (S : solver) (vs : List CInt) : Prop :=
  S.maxLemmas = S0.maxLemmas ∧
  ((S.nLemmas = S0.nLemmas ∧ vs = vs0 ∧ trailLen S0 ≤ trailLen S ∧
      ∀ i < trailLen S0, trailAt S i = trailAt S0 i) ∨ S0.nLemmas < S.nLemmas)

/-- The invariant of the outer loop (C:135) with flag `f`. -/
def OutInv (input : Input) (S0 : solver) (vs0 : List CInt) (S : solver) (f : CInt) : Prop :=
  ∃ db vs, Core input S db vs ∧ WatchedTrue S db ∧ PMode S f (processedPos S) ∧ Rel S0 vs0 S vs

/-- The watched-literal invariant, except at position `P` for records still in `rest`. -/
def WatchedExcept (S : solver) (db : Records) (P : Nat) (rest : List Ptr) : Prop :=
  ∀ r ∈ db.all, 2 ≤ r.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
    ∀ p < processedPos S, FalseAt S r.2[w]! p → (p = P → r.1 - 2 ∉ rest ∧ r.1 - 1 ∉ rest) →
      ∃ q, FalseAt S (- r.2[o]!) q ∧ SameOrLowerLevel S p q

/-- The invariant of the watch loop (C:138) while processing `lit`, at trail position `P`:
the list of `lit` is `visited ++ rest`, split at the cursor `watch`. -/
def WInv (input : Input) (S0 : solver) (vs0 : List CInt) (P : Nat) (lit : CInt) (S : solver)
    (f watch : CInt) : Prop :=
  ∃ db vs visited rest, Core input S db vs ∧ processedPos S = P + 1 ∧ P < trailLen S ∧
    trailAt S P = lit ∧ Path S (S.first + lit) visited watch ∧ ListFrom S watch rest ∧
    ((S.first + lit) :: (visited ++ rest)).Nodup ∧
    (∀ link, link ∈ visited ++ rest ↔ Watches db.all lit link db.flip) ∧
    WatchedExcept S db P rest ∧ PMode S f P ∧ Rel S0 vs0 S vs

/-- The state after the literal scan finds a non-false literal at `t` (C:144–150): it
moves to position 1, `lit` to position `t`, and the watch moves to its list. -/
def foundState (S : solver) (c t : CInt) (watch lit : CInt) : solver :=
  let S1 := S.st (c + 1) (S.ld (c + t))
  let S2 := S1.st (c + t) lit
  let store := S2.ld watch
  let S3 := S2.st watch (S2.ld (S2.ld watch))
  addWatch S3 (S3.ld (c + 1)) store

/-- The literal scan (C:143–152) of the clause at `c` (literals `c + 2 … c + L - 1`, then
0), from state `S` (after C:142): literals `2 … i-1` are false, or a non-false literal
`t` was found and moved (`foundState`). -/
def ScanInv (S : solver) (c watch lit N : CInt) (S' : solver) (unit i : CInt) : Prop :=
  ∃ L : CInt, 2 ≤ L ∧ L ≤ N ∧ S.ld (c + L) = 0 ∧ (∀ t, 2 ≤ t → t < L → S.ld (c + t) ≠ 0) ∧
  ((unit ≠ 0 ∧ S' = S ∧ 2 ≤ i ∧ i ≤ L ∧ ∀ t, 2 ≤ t → t < i → flag S (S.ld (c + t)) ≠ 0) ∨
   (unit = 0 ∧ ∃ t, 2 ≤ t ∧ i = t + 1 ∧ t < L ∧ (∀ t', 2 ≤ t' → t' < t → flag S (S.ld (c + t')) ≠ 0) ∧
     flag S (S.ld (c + t)) = 0 ∧ S' = foundState S c t watch lit))

/-- `toNat` keeps a strict decrease between nonnegative bounds. -/
theorem toNat_lt_toNat' {x y : Int} (h1 : x < y) (h2 : 0 ≤ x) : x.toNat < y.toNat := by omega

/-- A scan step that finds a non-false literal (C:144–150). -/
theorem ScanInv.found {S S' : solver} {c w lit N unit i : CInt} (h : ScanInv S c w lit N S' unit i)
    (hu : unit ≠ 0) (hz : S'.ld (c + i) ≠ 0) (hf : S'.ld (S'.false + S'.ld (c + i)) = 0) :
    ScanInv S c w lit N (foundState S' c i w lit) 0 (i + 1) ∧ N + 3 - (i + 1) < N + 3 - i ∧
      0 ≤ N + 3 - (i + 1) := by
  obtain ⟨L, h2, hL, hend, hnz, (⟨_, rfl, hi2, hiL, hfl⟩ | ⟨hu0, _⟩)⟩ := h
  · have hiL' : i < L := by
      rcases Int.lt_or_eq_of_le hiL with h' | h'
      · exact h'
      · subst h'; exact absurd hend hz
    exact ⟨⟨L, h2, hL, hend, hnz, Or.inr ⟨rfl, i, hi2, rfl, hiL', hfl, hf, rfl⟩⟩, by omega, by omega⟩
  · exact absurd hu0 hu

/-- A scan step past a false literal (C:144 fails). -/
theorem ScanInv.skip {S S' : solver} {c w lit N unit i : CInt} (h : ScanInv S c w lit N S' unit i)
    (hu : unit ≠ 0) (hz : S'.ld (c + i) ≠ 0) (hf : S'.ld (S'.false + S'.ld (c + i)) ≠ 0) :
    ScanInv S c w lit N S' unit (i + 1) ∧ N + 3 - (i + 1) < N + 3 - i ∧ 0 ≤ N + 3 - (i + 1) := by
  obtain ⟨L, h2, hL, hend, hnz, (⟨hu', rfl, hi2, hiL, hfl⟩ | ⟨hu0, _⟩)⟩ := h
  · have hiL' : i < L := by
      rcases Int.lt_or_eq_of_le hiL with h' | h'
      · exact h'
      · subst h'; exact absurd hend hz
    refine ⟨⟨L, h2, hL, hend, hnz, Or.inl ⟨hu', rfl, by omega, by omega, fun t h1 h3 => ?_⟩⟩, by omega, by omega⟩
    rcases Int.lt_or_eq_of_le (Int.lt_add_one_iff.mp h3) with h' | h'
    · exact hfl t h1 h'
    · subst h'; exact hf
  · exact absurd hu0 hu

/-- The scan ended without finding a literal to watch (C:152). -/
theorem ScanInv.unit_end {Ss S' : solver} {c w lit N unit i : CInt} (h : ScanInv Ss c w lit N S' unit i)
    (hu : unit ≠ 0) (hend : unit ≠ 0 → S'.ld (c + i) = 0) :
    S' = Ss ∧ ∃ L, Ss.ld (c + L) = 0 ∧ (∀ t, 2 ≤ t → t < L → Ss.ld (c + t) ≠ 0) ∧ 2 ≤ i ∧ i ≤ L ∧
      (∀ t, 2 ≤ t → t < i → flag Ss (Ss.ld (c + t)) ≠ 0) ∧ Ss.ld (c + i) = 0 := by
  obtain ⟨L, -, -, hL, hnz, (⟨-, rfl, hi2, hiL, hfl⟩ | ⟨hu0, -⟩)⟩ := h
  · exact ⟨rfl, L, hL, hnz, hi2, hiL, hfl, hend hu⟩
  · exact absurd hu0 hu

/-- The scan ended by finding a literal to watch (C:144–150). -/
theorem ScanInv.found_end {Ss S' : solver} {c w lit N unit i : CInt} (h : ScanInv Ss c w lit N S' unit i)
    (hu : unit = 0) :
    ∃ L t, Ss.ld (c + L) = 0 ∧ (∀ t', 2 ≤ t' → t' < L → Ss.ld (c + t') ≠ 0) ∧ 2 ≤ t ∧ t < L ∧
      flag Ss (Ss.ld (c + t)) = 0 ∧ S' = foundState Ss c t w lit := by
  obtain ⟨L, -, -, hL, hnz, (⟨hu', -⟩ | ⟨-, t, ht2, -, htL, -, hf, hS'⟩)⟩ := h
  · exact absurd hu hu'
  · exact ⟨L, t, hL, hnz, ht2, htL, hf, hS'⟩

/-- The measure of the outer loop: lemmas still to learn (at most `3^n`), then literals
still to process. A conflict learns a lemma but may move `processed` back. -/
def outMeasure (S : solver) : Nat :=
  (clauseBound S.nVars - S.nLemmas.toNat) * (S.nVars.toNat + 2) + (S.nVars.toNat + 1 - processedPos S)

/-- The outer loop's measure decreases: one more literal processed, or a new lemma. -/
theorem outMeasure_lt {So S : solver} (hv : S.nVars = So.nVars)
    (hb : S.nLemmas.toNat ≤ clauseBound S.nVars) (h0 : 0 ≤ So.nLemmas)
    (hpp : processedPos So < trailLen So) (hlen0 : trailLen So ≤ So.nVars.toNat)
    (hlen : processedPos S ≤ S.nVars.toNat)
    (h : (S.nLemmas = So.nLemmas ∧ processedPos S = processedPos So + 1) ∨ So.nLemmas < S.nLemmas) :
    outMeasure S < outMeasure So := by
  unfold outMeasure
  rw [hv] at hb hlen ⊢
  rcases h with ⟨hn, hp⟩ | hn
  · rw [hn, hp]; omega
  · generalize clauseBound So.nVars = B at hb ⊢
    generalize So.nVars.toNat = n at hlen0 hlen ⊢
    have hX : B - S.nLemmas.toNat + 1 ≤ B - So.nLemmas.toNat := by omega
    have := Nat.mul_le_mul_right (n + 2) hX
    rw [Nat.add_mul, Nat.one_mul] at this
    omega

/-- `Core` does not depend on `processed` beyond `forced ≤ processed ≤ assigned`. -/
theorem Core.withProcessed {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) (p : CInt) (h1 : S.forced ≤ p) (h2 : p ≤ S.assigned) :
    Core input { S with processed := p } db vs := by
  obtain ⟨valid, nv, mem, ml, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
    ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩, root,
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩, watches, reasons, units, ⟨o1, o2, o3, o4⟩⟩ := h
  exact ⟨valid, nv, mem, ml, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
    ⟨t1, h1, h2, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩, root,
    ⟨d1.frame fun _ _ _ _ => rfl, d2.frame fun _ _ _ _ => rfl, d3, d4, d5, d6, d7, d8, d9, d10⟩,
    fun lit hl => by
      obtain ⟨links, hlinks, hnd, hm⟩ := watches lit hl
      exact ⟨links, hlinks.frame fun _ _ => rfl, hnd, hm⟩,
    reasons, units, ⟨o1.congr fun _ _ => rfl, o2, o3, o4⟩⟩

/-- Moving `forced` up to the end of an all-root trail keeps `Core` (C:157). -/
theorem Core.withForced {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) (hpa : S.processed = S.assigned)
    (hroot : ∀ i < trailLen S, RootLevel S i) :
    Core input { S with forced := S.processed } db vs := by
  obtain ⟨valid, nv, mem, ml, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
    ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩, root,
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩, watches, reasons, units, ⟨o1, o2, o3, o4⟩⟩ := h
  refine ⟨valid, nv, mem, ml, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
    ⟨by show S.falseStack ≤ S.processed; omega, Int.le_refl _, t3, t4, t5, t6, t7, t8, t9, t10, t11,
      fun i hi => hroot i (by simp only [forcedPos, trailLen] at hi ⊢; rw [← hpa]; exact hi)⟩, root,
    ⟨d1.frame fun _ _ _ _ => rfl, d2.frame fun _ _ _ _ => rfl, d3, d4, d5, d6, d7, d8, d9, d10⟩,
    fun lit hl => by
      obtain ⟨links, hlinks, hnd, hm⟩ := watches lit hl
      exact ⟨links, hlinks.frame fun _ _ => rfl, hnd, hm⟩,
    fun i hi hfi => absurd hfi (by simp only [forcedPos, trailLen] at hi ⊢; rw [hpa]; omega),
    units, ⟨o1.congr fun _ _ => rfl, o2, o3, o4⟩⟩

end MicrosatLean.Faithful.Verification
