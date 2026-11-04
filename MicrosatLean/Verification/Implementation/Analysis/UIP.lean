import MicrosatLean.CDCL.Analysis

namespace MicrosatLean.Verification.Implementation.Analysis

open CDCL

private def scanLiteral (s : State) (candidate offset : Nat) : Lit :=
  s.trail[candidate - 1 - offset]!

private def uipScan : Nat → State → Nat → Nat → Bool
  | 0, _, _, _ => true
  | fuel + 1, s, candidate, offset =>
    let lit := scanLiteral s candidate offset
    if s.mark lit == 2 then false
    else if s.reason lit == 0 then true
    else uipScan fuel s candidate (offset + 1)

private def uipForLoop (s : State) (candidate start fuel : Nat) : Bool := Id.run do
  for offset in [start : start + fuel] do
    let lit := s.trail[candidate - 1 - offset]!
    if s.mark lit == 2 then return false
    if s.reason lit == 0 then return true
  return true

/-- The proof scan agrees with the concrete bounded loop on all inputs. No
trail bounds or CDCL invariants are assumed for this execution equation. -/
private theorem uipForLoop_eq_scan (fuel : Nat) (s : State) (candidate start : Nat) :
    uipForLoop s candidate start fuel = uipScan fuel s candidate start := by
  induction fuel generalizing start with
  | zero => simp [uipForLoop, Std.Legacy.Range.forIn_eq_forIn_range', uipScan]
  | succ fuel ih =>
    simp only [uipForLoop, Std.Legacy.Range.forIn_eq_forIn_range',
      Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
    rw [show start + (fuel + 1) - start = fuel + 1 by omega]
    simp only [List.range'_succ, List.forIn_cons, uipScan, scanLiteral]
    split
    · simp_all
    · split
      · simp_all
      · have tail := ih (start + 1)
        simp only [uipForLoop, Std.Legacy.Range.forIn_eq_forIn_range'] at tail
        simpa [*] using tail

private theorem firstUIP_eq_scan (s : State) (candidate : Nat) :
    firstUIP s candidate = uipScan candidate s candidate 0 := by
  simpa only [uipForLoop, Nat.zero_add, firstUIP] using
    uipForLoop_eq_scan candidate s candidate 0

/-- An offset contributes to the test until an earlier scanned decision stops
the loop. The decision literal itself is checked for MARK before stopping. -/
private def ClearScan (s : State) (candidate start fuel : Nat) : Prop :=
  ∀ offset, start ≤ offset → offset < start + fuel →
    (∀ earlier, start ≤ earlier → earlier < offset →
      s.reason (scanLiteral s candidate earlier) ≠ 0) →
    s.mark (scanLiteral s candidate offset) ≠ 2

private theorem uipScan_true_iff_clear (fuel : Nat) (s : State) (candidate start : Nat) :
    uipScan fuel s candidate start = true ↔ ClearScan s candidate start fuel := by
  induction fuel generalizing start with
  | zero =>
    constructor
    · intro _ offset hLower hUpper; omega
    · intro _; rfl
  | succ fuel ih =>
    constructor
    · intro hRun offset hLower hUpper hBefore
      have hMark : s.mark (scanLiteral s candidate start) ≠ 2 := by
        intro equal
        simp [uipScan, equal] at hRun
      by_cases equal : offset = start
      · simpa only [equal] using hMark
      · have hReason : s.reason (scanLiteral s candidate start) ≠ 0 :=
          hBefore start (by omega) (by omega)
        have hTail : uipScan fuel s candidate (start + 1) = true := by
          simpa [uipScan, hMark, hReason] using hRun
        exact (ih (start + 1)).mp hTail offset (by omega) (by omega)
          (fun earlier hStart hEnd => hBefore earlier (by omega) hEnd)
    · intro hClear
      have hMark : s.mark (scanLiteral s candidate start) ≠ 2 :=
        hClear start (by omega) (by omega) (by intro earlier hLower hUpper; omega)
      by_cases hReason : s.reason (scanLiteral s candidate start) = 0
      · simp [uipScan, hMark, hReason]
      · have hTailClear : ClearScan s candidate (start + 1) fuel := by
          intro offset hLower hUpper hBefore
          apply hClear offset (by omega) (by omega)
          intro earlier hStart hEnd
          by_cases equal : earlier = start
          · simpa only [equal] using hReason
          · exact hBefore earlier (by omega) hEnd
        have hTail := (ih (start + 1)).mpr hTailClear
        simpa [uipScan, hMark, hReason] using hTail

/-- Positions below the candidate and at or after its nearest earlier decision.
If no earlier decision exists, every earlier trail position is included. -/
def InScannedDecisionBlock (s : State) (candidate position : Nat) : Prop :=
  position < candidate ∧ ∀ later, position < later → later < candidate →
    s.reason s.trail[later]! ≠ 0

/-- The actual `firstUIP` loop returns true exactly when no earlier MARK occurs
before reaching the nearest decision. The nearest decision is included, since
the implementation tests its MARK before inspecting its reason. -/
theorem firstUIP_true_iff_no_earlier_mark (s : State) (candidate : Nat) :
    firstUIP s candidate = true ↔
      ∀ position, InScannedDecisionBlock s candidate position →
        s.mark s.trail[position]! ≠ 2 := by
  rw [firstUIP_eq_scan, uipScan_true_iff_clear]
  constructor
  · intro hClear position hBlock
    have hPosition : position < candidate := hBlock.1
    have hOffset : candidate - 1 - position < candidate := by omega
    have hBefore : ∀ earlier, 0 ≤ earlier → earlier < candidate - 1 - position →
        s.reason (scanLiteral s candidate earlier) ≠ 0 := by
      intro earlier _ hEarlier
      exact hBlock.2 (candidate - 1 - earlier) (by omega) (by omega)
    have hMark := hClear (candidate - 1 - position) (by omega) (by omega) hBefore
    simpa only [scanLiteral, show candidate - 1 - (candidate - 1 - position) = position by
      omega] using hMark
  · intro hBlock offset hLower hUpper hBefore
    apply hBlock (candidate - 1 - offset)
    constructor
    · omega
    · intro later hLater hEnd
      have hReason := hBefore (candidate - 1 - later) (by omega) (by omega)
      simpa only [scanLiteral, show candidate - 1 - (candidate - 1 - later) = later by
        omega] using hReason

/-- A concrete nearest-decision interval; this is a trail-index relation and
does not require a separately stored decision-level array. -/
structure DecisionBlock (s : State) (decision candidate : Nat) : Prop where
  before : decision < candidate
  decisionReason : s.reason s.trail[decision]! = 0
  noLaterDecision : ∀ later, decision < later → later < candidate →
    s.reason s.trail[later]! ≠ 0

theorem inScannedDecisionBlock_iff {s : State} {decision candidate position : Nat}
    (hBlock : DecisionBlock s decision candidate) :
    InScannedDecisionBlock s candidate position ↔ decision ≤ position ∧ position < candidate := by
  constructor
  · intro hScanned
    constructor
    · by_cases hBefore : decision ≤ position
      · exact hBefore
      · have := hScanned.2 decision (by omega) hBlock.before
        exact False.elim (this hBlock.decisionReason)
    · exact hScanned.1
  · intro hBounds
    exact ⟨hBounds.2, fun later hLater hEnd =>
      hBlock.noLaterDecision later (by omega) hEnd⟩

theorem firstUIP_true_iff_decision_block_clear {s : State} {decision candidate : Nat}
    (hBlock : DecisionBlock s decision candidate) :
    firstUIP s candidate = true ↔
      ∀ position, decision ≤ position → position < candidate → s.mark s.trail[position]! ≠ 2 := by
  rw [firstUIP_true_iff_no_earlier_mark]
  constructor
  · intro h position hLower hUpper
    exact h position ((inScannedDecisionBlock_iff hBlock).mpr ⟨hLower, hUpper⟩)
  · intro h position hPosition
    have bounds := (inScannedDecisionBlock_iff hBlock).mp hPosition
    exact h position bounds.1 bounds.2

end MicrosatLean.Verification.Implementation.Analysis
