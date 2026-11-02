import MicrosatLean.Verification.Implementation.Native.Analysis.Resolution
import MicrosatLean.Verification.Implementation.Native.Analysis.Learned

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation

/-- Resolution can remove or retain cached root marks, but cannot create them. -/
def SixSubset (before after : State) : Prop :=
  ∀ lit, after.mark lit = 6 → before.mark lit = 6

theorem SixSubset.refl (s : State) : SixSubset s s := fun _ h => h

theorem SixSubset.trans {before middle after : State}
    (first : SixSubset before middle) (last : SixSubset middle after) : SixSubset before after :=
  fun lit mark => first lit (last lit mark)

theorem setMark_sixSubset (s : State) (lit value : Nat) (different : value ≠ 6) :
    SixSubset s (s.setMark lit value) := by
  intro query marked
  by_cases same : lit = query
  · subst query
    by_cases bound : lit < s.marks.size
    · have read := Array.getElem!_set!_self s.marks lit value bound
      change (s.marks.set! lit value)[lit]! = 6 at marked
      exact False.elim (different (read.symm.trans marked))
    · simpa only [State.mark, State.setMark, Array.set!_eq_setIfInBounds,
        Array.setIfInBounds, bound, ↓reduceDIte] using marked
  · simpa only [State.mark, State.setMark, Array.getElem!_set!_ne _ _ _ _ same] using marked

private theorem bump_sixSubset (s : State) (lit : Lit) : SixSubset s (s.bump lit) := by
  simp only [State.bump, Id.run, pure]
  split
  · exact .refl _
  · split <;> exact setMark_sixSubset s lit 2 (by omega)

private def markBody (index : Nat) (s : State) : Id (ForInStep State) :=
  if s.db index == 0 then .done s else .yield (s.bump (s.db index))

private theorem markClause_eq_body (s : State) (start : Nat) :
    markClause s start = forIn (m := Id) [start:s.arena.size] s markBody := by rfl

private theorem list_sixSubset (xs : List Nat) (body : Nat → State → Id (ForInStep State))
    (step : ∀ index s, SixSubset s (body index s).value) (s : State) :
    SixSubset s (forIn (m := Id) xs s body) := by
  induction xs generalizing s with
  | nil => exact .refl _
  | cons head tail ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    have frame := step head s
    cases result : body head s with
    | done next => simpa only [result, ForInStep.value_done] using frame
    | yield next =>
      have nextFrame : SixSubset s next := by simpa only [result, ForInStep.value_yield] using frame
      exact nextFrame.trans (ih next)

theorem markClause_sixSubset (s : State) (start : Nat) : SixSubset s (markClause s start) := by
  rw [markClause_eq_body, Std.Legacy.Range.forIn_eq_forIn_range']
  apply list_sixSubset
  intro index current
  simp only [markBody]
  split
  · exact .refl _
  · exact bump_sixSubset _ _

private theorem resolutionBody_sixSubset (s : State) : SixSubset s (resolutionBody s).value := by
  have popped : SixSubset s { s with assigned := s.assigned - 1 } := .refl s
  simp only [resolutionBody, Id.run, pure]
  split
  · exact popped
  · split
    · split
      · exact popped
      · exact (popped.trans (markClause_sixSubset _ _)).trans (setMark_sixSubset _ _ 0 (by omega))
    · exact popped.trans (setMark_sixSubset _ _ 0 (by omega))

private theorem resolutionScan_sixSubset (fuel : Nat) (s : State) : SixSubset s (resolutionScan fuel s) := by
  induction fuel generalizing s with
  | zero => exact .refl _
  | succ fuel ih =>
    have step := resolutionBody_sixSubset s
    cases body : resolutionBody s with
    | done next => simpa only [resolutionScan, body, ForInStep.value_done] using step
    | yield next =>
      have nextFrame : SixSubset s next := by simpa only [body, ForInStep.value_yield] using step
      simpa only [resolutionScan, body] using nextFrame.trans (ih next)

theorem resolveToUIP_no_new_six (s : State) (lit : Lit) :
    (resolveToUIP s).mark lit = 6 → s.mark lit = 6 := by
  rw [resolveToUIP_eq_scan]
  exact resolutionScan_sixSubset _ _ lit

/-- Recursive minimization and learned construction never create MARK tags. -/
def TwoSubset (before after : State) : Prop :=
  ∀ lit, after.mark lit = 2 → before.mark lit = 2

theorem TwoSubset.refl (s : State) : TwoSubset s s := fun _ h => h

theorem TwoSubset.trans {before middle after : State}
    (first : TwoSubset before middle) (last : TwoSubset middle after) : TwoSubset before after :=
  fun lit mark => first lit (last lit mark)

private theorem setMark_twoSubset (s : State) (lit value : Nat) (different : value ≠ 2) :
    TwoSubset s (s.setMark lit value) := by
  intro query marked
  by_cases same : lit = query
  · subst query
    by_cases bound : lit < s.marks.size
    · rw [setMark_mark_same bound] at marked
      exact False.elim (different marked)
    · simpa only [State.mark, State.setMark, Array.set!_eq_setIfInBounds,
        Array.setIfInBounds, bound, ↓reduceDIte] using marked
  · rw [setMark_mark_other same] at marked
    exact marked

private theorem list_invariant {α β : Type} (xs : List α) (body : α → β → Id (ForInStep β))
    (p : β → Prop) (step : ∀ x b, p b → p (body x b).value)
    (initial : β) (h : p initial) : p (forIn xs initial body : Id β) := by
  induction xs generalizing initial with
  | nil => exact h
  | cons head tail ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    have hp := step head initial h
    cases heq : body head initial with
    | done b => simpa only [heq, ForInStep.value_done] using hp
    | yield b => exact ih b (by simpa only [heq, ForInStep.value_yield] using hp)

private def ScanTwo (before : State) (acc : ImpliedScanState) : Prop :=
  TwoSubset before acc.2 ∧ ∀ result, acc.1 = some result → TwoSubset before result.1

private theorem impliedBody_twoSubset (recurse : State → Lit → State × Bool)
    (recursive : ∀ s lit, TwoSubset s (recurse s lit).1) (before : State) (target i : Nat)
    (acc : ImpliedScanState) (inv : ScanTwo before acc) :
    ScanTwo before (impliedScanBody recurse target i acc).value := by
  simp only [impliedScanBody]
  split
  · exact ⟨inv.1, by intro result impossible; cases impossible⟩
  · split
    · cases execute : recurse acc.2 (acc.2.db i) with
      | mk next follows =>
        have after : TwoSubset before next := inv.1.trans
          (by simpa only [execute] using recursive acc.2 (acc.2.db i))
        split
        · refine ⟨after, ?_⟩
          intro result returned
          cases returned
          exact after.trans (setMark_twoSubset next target 5 (by decide))
        · exact ⟨after, by intro result impossible; cases impossible⟩
    · exact ⟨inv.1, by intro result impossible; cases impossible⟩

theorem implied_twoSubset (fuel : Nat) (s : State) (target : Lit) :
    TwoSubset s (implied fuel s target).1 := by
  induction fuel generalizing s target with
  | zero => exact .refl s
  | succ fuel ih =>
    rw [implied.eq_2]
    dsimp only [Id.run]
    split
    · exact .refl s
    · split
      · exact .refl s
      · simp only [bind, pure]
        unfold Break.runK.match_1
        let range : Std.Legacy.Range := [s.reason target + 1 : s.arena.size]
        let result : ImpliedScanState :=
          forIn (m := Id) range (none, s) (impliedScanBody (implied fuel) target)
        have inv : ScanTwo s result := by
          dsimp only [result]
          rw [Std.Legacy.Range.forIn_eq_forIn_range']
          exact list_invariant _ _ (ScanTwo s) (impliedBody_twoSubset _ ih s target) (none, s)
            ⟨.refl s, by intro result impossible; cases impossible⟩
        change TwoSubset s (Option.casesOn (motive := fun _ => State × Bool) result.1
          (result.2.setMark target 6, true) (fun r => r)).1
        cases returned : result.1 with
        | none => exact inv.1.trans (setMark_twoSubset result.2 target 6 (by decide))
        | some answer => exact inv.2 answer returned

theorem implied_no_new_two (fuel : Nat) (s : State) (target query : Lit) :
    (implied fuel s target).1.mark query = 2 → s.mark query = 2 :=
  implied_twoSubset fuel s target query

private def OriginalMarks (original : State) (acc : LearnedAcc) : Prop :=
  TwoSubset original acc.1 ∧ ∀ lit ∈ acc.2.1, original.mark lit = 2

private theorem finish_originalMarks {original s : State} {lits : Array Lit} {lbd : Nat} {used : Bool}
    (inv : OriginalMarks original (s, lits, lbd, used)) (p target : Nat) :
    OriginalMarks original (finishBody p target s lits lbd used).value := by
  simp only [finishBody, Id.run, pure]
  split <;> repeat first
    | split
    | exact ⟨inv.1.trans (setMark_twoSubset s target 1 (by decide)), inv.2⟩

private theorem learnedBody_originalMarks (original : State) (candidate offset : Nat) (acc : LearnedAcc)
    (inv : OriginalMarks original acc) : OriginalMarks original (learnedBody candidate offset acc).value := by
  rw [learnedBody_eq]
  dsimp only
  split
  · have marked : acc.1.mark acc.1.trail[candidate - offset]! = 2 := by
      simpa using ‹(acc.1.mark acc.1.trail[candidate - offset]! == 2) = true›
    have originalMark := inv.1 _ marked
    have after := inv.1.trans (implied_twoSubset (acc.1.nVars + 1) acc.1 acc.1.trail[candidate - offset]!)
    split
    · apply finish_originalMarks
      refine ⟨after, ?_⟩
      intro lit member
      rcases Array.mem_push.mp member with old | equal
      · exact inv.2 lit old
      · simpa only [equal] using originalMark
    · exact finish_originalMarks ⟨after, inv.2⟩ _ _
  · exact finish_originalMarks inv _ _

/-- Every literal appended by the actual learned constructor was already
MARKed at its entry. This is unconditional and independent of semantic cache
invariants, because the minimizer writes only tags five and six. -/
theorem buildLearned_original_marks (s : State) (candidate : Nat) :
    ∀ lit ∈ (buildLearned s candidate).2.1, s.mark lit = 2 := by
  rw [buildLearned_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  dsimp only
  have inv := list_invariant (List.range' 0 [:candidate + 1 - s.forced].size)
    (learnedBody candidate) (OriginalMarks s) (learnedBody_originalMarks s candidate)
    ({ s with processed := candidate }, #[], 0, false)
    ⟨TwoSubset.refl s, by intro lit impossible; simp at impossible⟩
  exact inv.2

end MicrosatLean.Verification.Implementation.Native.Analysis
