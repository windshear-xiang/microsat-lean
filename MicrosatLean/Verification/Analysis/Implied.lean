import MicrosatLean.CDCL.Analysis
import MicrosatLean.Verification.Representation.State
import Std.Do.Triple.SpecLemmas

namespace MicrosatLean.Verification.Analysis

open CDCL

/-!
Properties of the actual recursive minimizer `CDCL.implied`. The loop-body
definition below only names the anonymous function produced by elaborating
that function's `for` loop; the main theorem unfolds the executable definition.
-/

private def withoutMarks (s : State) : State := { s with marks := #[] }

/-- Every state component except mark values is unchanged. Even the mark array
dimension is preserved, including on malformed states and exhausted fuel. -/
structure MarkFrame (before after : State) : Prop where
  nonMarks : withoutMarks after = withoutMarks before
  marksSize : after.marks.size = before.marks.size

theorem MarkFrame.refl (s : State) : MarkFrame s s := ⟨rfl, rfl⟩

theorem MarkFrame.trans {first middle last : State}
    (hfirst : MarkFrame first middle) (hlast : MarkFrame middle last) :
    MarkFrame first last :=
  ⟨hlast.nonMarks.trans hfirst.nonMarks, hlast.marksSize.trans hfirst.marksSize⟩

theorem markFrame_setMark (s : State) (lit value : Nat) :
    MarkFrame s (s.setMark lit value) := by
  constructor
  · rfl
  · simp [State.setMark]

/-- An explicit record equality usable to transport structural invariants. -/
theorem MarkFrame.restore {before after : State} (h : MarkFrame before after) :
    { after with marks := before.marks } = before := by
  have heq := congrArg (fun s => { s with marks := before.marks }) h.nonMarks
  cases before
  cases after
  simpa only [withoutMarks] using heq

theorem MarkFrame.arena {before after : State} (h : MarkFrame before after) :
    after.arena = before.arena := by
  simpa only [withoutMarks] using congrArg State.arena h.nonMarks

theorem MarkFrame.reasons {before after : State} (h : MarkFrame before after) :
    after.reasons = before.reasons := by
  simpa only [withoutMarks] using congrArg State.reasons h.nonMarks

theorem MarkFrame.trail {before after : State} (h : MarkFrame before after) :
    after.trail = before.trail := by
  simpa only [withoutMarks] using congrArg State.trail h.nonMarks

theorem MarkFrame.arrayBounds {before after : State} (h : MarkFrame before after)
    (bounds : Representation.ArrayBounds before) : Representation.ArrayBounds after := by
  have restored : Representation.ArrayBounds { after with marks := before.marks } := by
    rw [h.restore]
    exact bounds
  exact ⟨restored.firstSize, h.marksSize.trans restored.marksSize,
    restored.reasonsSize, restored.phasesSize, restored.trailSize,
    restored.previousSize, restored.nextSize⟩

theorem MarkFrame.trailBounds {before after : State} (h : MarkFrame before after)
    (bounds : Representation.TrailBounds before) : Representation.TrailBounds after := by
  have restored : Representation.TrailBounds { after with marks := before.marks } := by
    rw [h.restore]
    exact bounds
  exact ⟨restored.forcedProcessed, restored.processedAssigned, restored.assignedVars⟩

theorem MarkFrame.packedClause {before after : State} (h : MarkFrame before after)
    {clauseId : Nat} {lits : Array Lit} (packed : Representation.PackedClause before clauseId lits) :
    Representation.PackedClause after clauseId lits := by
  have restored : Representation.PackedClause { after with marks := before.marks } clauseId lits := by
    rw [h.restore]
    exact packed
  exact ⟨restored.startLower, restored.endBound, restored.literals,
    restored.terminator, restored.wellFormed⟩

private theorem list_forIn_invariant {α β : Type} (xs : List α) (body : α → β → Id (ForInStep β))
    (p : β → Prop) (step : ∀ x b, p b → p (body x b).value)
    (initial : β) (h : p initial) : p (forIn xs initial body : Id β) := by
  induction xs generalizing initial with
  | nil => exact h
  | cons head tail ih =>
    rw [List.forIn_cons]
    change p (match body head initial with
      | .done b => b
      | .yield b => (forIn tail b body : Id β))
    have hp := step head initial h
    cases heq : body head initial with
    | done b => simpa only [heq, ForInStep.value_done] using hp
    | yield b => exact ih b (by simpa only [heq, ForInStep.value_yield] using hp)

private theorem range_forIn_invariant {β : Type} (range : Std.Legacy.Range)
    (body : Nat → β → Id (ForInStep β)) (p : β → Prop)
    (step : ∀ x b, p b → p (body x b).value)
    (initial : β) (h : p initial) : p (forIn range initial body : Id β) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  exact list_forIn_invariant _ body p step initial h

abbrev ImpliedScanState := Option (State × Bool) × State

/-- The anonymous loop body in the executable minimizer, exposed only in the
proof subtree so structural and semantic invariants can share the same body. -/
def impliedScanBody (recurse : State → Lit → State × Bool) (lit : Lit)
    (i : Nat) (acc : ImpliedScanState) : Id (ForInStep ImpliedScanState) :=
  let s := acc.2
  let antecedent := s.db i
  if antecedent == 0 then .done (none, s)
  else if s.mark antecedent != 2 then
    let next := (recurse s antecedent).1
    let follows := (recurse s antecedent).2
    if !follows then .done (some (next.setMark lit 5, false), next)
    else .yield (none, next)
  else .yield (none, s)

private def ScanFrame (before : State) (acc : ImpliedScanState) : Prop :=
  MarkFrame before acc.2 ∧
    ∀ result, acc.1 = some result → MarkFrame before result.1 ∧ result.2 = false

private theorem scanBody_frame (recurse : State → Lit → State × Bool)
    (hrec : ∀ s lit, MarkFrame s (recurse s lit).1)
    (before : State) (lit i : Nat) (acc : ImpliedScanState) (h : ScanFrame before acc) :
    ScanFrame before (impliedScanBody recurse lit i acc).value := by
  simp only [impliedScanBody]
  split
  · exact ⟨h.1, by intro result hr; cases hr⟩
  · split
    · cases hresult : recurse acc.2 (acc.2.db i) with
      | mk next follows =>
        have hn := h.1.trans (by simpa only [hresult] using hrec acc.2 (acc.2.db i))
        split
        · refine ⟨hn, ?_⟩
          intro result hr
          cases hr
          exact ⟨hn.trans (markFrame_setMark next lit 5), rfl⟩
        · exact ⟨hn, by intro result hr; cases hr⟩
    · exact ⟨h.1, by intro result hr; cases hr⟩

/-- Exhaustion is a conservative failure and performs no mutation. -/
@[simp] theorem implied_zero (s : State) (lit : Lit) :
    implied 0 s lit = (s, false) := rfl

/-- A cached tag is returned exactly, without revisiting the reason graph. -/
theorem implied_cached (fuel : Nat) (s : State) (lit : Lit) (h : 2 < s.mark lit) :
    implied (fuel + 1) s lit = (s, s.mark lit &&& 2 != 0) := by
  rw [implied.eq_2]
  simp only [h, ↓reduceIte, Id.run, pure]

theorem implied_cached_true (fuel : Nat) (s : State) (lit : Lit) (h : s.mark lit = 6) :
    implied (fuel + 1) s lit = (s, true) := by
  simpa [h] using implied_cached fuel s lit (by omega)

theorem implied_cached_false (fuel : Nat) (s : State) (lit : Lit) (h : s.mark lit = 5) :
    implied (fuel + 1) s lit = (s, false) := by
  simpa [h] using implied_cached fuel s lit (by omega)

theorem implied_decision (fuel : Nat) (s : State) (lit : Lit)
    (hmark : s.mark lit ≤ 2) (hreason : s.reason lit = 0) :
    implied (fuel + 1) s lit = (s, false) := by
  rw [implied.eq_2]
  simp [Nat.not_lt.mpr hmark, hreason]

/-- The actual minimizer changes only mark values. No well-formedness, reason
acyclicity, successful return, or semantic correctness is assumed here. -/
theorem implied_markFrame (fuel : Nat) (s : State) (lit : Lit) :
    MarkFrame s (implied fuel s lit).1 := by
  induction fuel generalizing s lit with
  | zero => exact MarkFrame.refl s
  | succ fuel ih =>
    rw [implied.eq_2]
    dsimp only [Id.run]
    split
    · exact MarkFrame.refl s
    · split
      · exact MarkFrame.refl s
      · simp only [bind, pure]
        unfold Break.runK.match_1
        let range : Std.Legacy.Range := [s.reason lit + 1 : s.arena.size]
        let result : ImpliedScanState := forIn (m := Id) range (none, s) (impliedScanBody (implied fuel) lit)
        have hr : ScanFrame s result :=
          range_forIn_invariant range (impliedScanBody (implied fuel) lit) (ScanFrame s)
            (scanBody_frame _ ih s lit) (none, s) ⟨MarkFrame.refl s, by
              intro result hr
              cases hr⟩
        change MarkFrame s
          (Option.casesOn (motive := fun _ => State × Bool) result.1
            (result.2.setMark lit 6, true) (fun r => r)).1
        cases heq : result.1 with
        | none => exact hr.1.trans (markFrame_setMark result.2 lit 6)
        | some r => exact (hr.2 r heq).1

private def ScanMarked (keptLit : Lit) (acc : ImpliedScanState) : Prop :=
  acc.2.mark keptLit = 2 ∧
    ∀ result, acc.1 = some result → result.1.mark keptLit = 2

private theorem scanBody_marked (recurse : State → Lit → State × Bool)
    (hrec : ∀ s target keptLit, keptLit ≠ target → s.mark keptLit = 2 →
      (recurse s target).1.mark keptLit = 2)
    (target keptLit i : Nat) (different : keptLit ≠ target)
    (acc : ImpliedScanState) (h : ScanMarked keptLit acc) :
    ScanMarked keptLit (impliedScanBody recurse target i acc).value := by
  simp only [impliedScanBody]
  split
  · exact ⟨h.1, by intro result impossible; cases impossible⟩
  · split
    · have notMarked : acc.2.mark (acc.2.db i) ≠ 2 := by
        simpa using ‹(acc.2.mark (acc.2.db i) != 2) = true›
      have notProtected : keptLit ≠ acc.2.db i := by
        intro equal
        exact notMarked (equal ▸ h.1)
      have preserved := hrec acc.2 (acc.2.db i) keptLit notProtected h.1
      cases hr : recurse acc.2 (acc.2.db i) with
      | mk next follows =>
        have nextMarked : next.mark keptLit = 2 := by simpa only [hr] using preserved
        split
        · refine ⟨nextMarked, ?_⟩
          intro result returned
          cases returned
          simpa only [Representation.setMark_mark_other (Ne.symm different)] using nextMarked
        · exact ⟨nextMarked, by intro result impossible; cases impossible⟩
    · exact ⟨h.1, by intro result impossible; cases impossible⟩

/-- Recursive minimization never overwrites another original MARK leaf:
the recursive branch explicitly skips any antecedent whose tag is 2. This
holds for every state, including exhausted fuel and malformed reason data. -/
theorem implied_preserves_mark_two (fuel : Nat) (s : State) (target keptLit : Lit)
    (different : keptLit ≠ target) (marked : s.mark keptLit = 2) :
    (implied fuel s target).1.mark keptLit = 2 := by
  induction fuel generalizing s target keptLit with
  | zero => exact marked
  | succ fuel ih =>
    rw [implied.eq_2]
    dsimp only [Id.run]
    split
    · exact marked
    · split
      · exact marked
      · simp only [bind, pure]
        unfold Break.runK.match_1
        let range : Std.Legacy.Range := [s.reason target + 1 : s.arena.size]
        let result : ImpliedScanState :=
          forIn (m := Id) range (none, s) (impliedScanBody (implied fuel) target)
        have hr : ScanMarked keptLit result :=
          range_forIn_invariant range (impliedScanBody (implied fuel) target)
            (ScanMarked keptLit) (scanBody_marked _ ih target keptLit · different)
            (none, s) ⟨marked, by intro result impossible; cases impossible⟩
        change (Option.casesOn (motive := fun _ => State × Bool) result.1
          (result.2.setMark target 6, true) (fun r => r)).1.mark keptLit = 2
        cases returned : result.1 with
        | none =>
          simpa only [Representation.setMark_mark_other (Ne.symm different)] using hr.1
        | some answer => exact hr.2 answer returned

/-- Calls made on an unmarked antecedent preserve all existing MARK leaves. -/
theorem implied_preserves_marks_of_target_not_two (fuel : Nat) (s : State) (target : Lit)
    (notMarked : s.mark target ≠ 2) (keptLit : Lit) (marked : s.mark keptLit = 2) :
    (implied fuel s target).1.mark keptLit = 2 := by
  apply implied_preserves_mark_two fuel s target keptLit _ marked
  intro equal
  exact notMarked (equal ▸ marked)

end MicrosatLean.Verification.Analysis
