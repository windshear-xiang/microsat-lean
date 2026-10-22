import MicrosatLean.Verification.Analysis.ReasonGraph

namespace MicrosatLean.Verification.Analysis

open CDCL Representation Std.Sat

/-- A minimization call changes only allowed false literals and never clears
an existing mark. The complement of any active literal is thereby protected. -/
structure MarkSupport (allowed : Lit → Prop) (before after : State) : Prop where
  frame : MarkFrame before after
  outside : ∀ lit, ¬ allowed lit → after.mark lit = before.mark lit
  nonzero : ∀ lit, before.mark lit ≠ 0 → after.mark lit ≠ 0

theorem MarkSupport.refl (allowed : Lit → Prop) (s : State) : MarkSupport allowed s s :=
  ⟨.refl s, fun _ _ => rfl, fun _ h => h⟩

theorem MarkSupport.trans {allowed : Lit → Prop} {first middle last : State}
    (before : MarkSupport allowed first middle) (after : MarkSupport allowed middle last) :
    MarkSupport allowed first last :=
  ⟨before.frame.trans after.frame, fun lit outside =>
    (after.outside lit outside).trans (before.outside lit outside),
    fun lit marked => after.nonzero lit (before.nonzero lit marked)⟩

theorem markSupport_setMark {allowed : Lit → Prop} (s : State) (target value : Nat)
    (member : allowed target) (positive : value ≠ 0) : MarkSupport allowed s (s.setMark target value) := by
  constructor
  · exact markFrame_setMark _ _ _
  · intro lit outside
    exact setMark_mark_other (by intro same; exact outside (same ▸ member))
  · intro lit marked
    by_cases same : target = lit
    · subst lit
      by_cases bound : target < s.marks.size
      · rw [setMark_mark_same bound]
        exact positive
      · simpa [State.setMark, Array.setIfInBounds, bound] using marked
    · simpa only [setMark_mark_other same] using marked

private def supportStepPost {β : Type} (inv : Nat → β → Prop) (post : β → Prop)
    (next : Nat) (result : ForInStep β) : Prop :=
  match result with
  | .done b => post b
  | .yield b => inv next b

private theorem supportRange_post {β : Type} (body : Nat → β → Id (ForInStep β))
    (inv : Nat → β → Prop) (post : β → Prop)
    (step : ∀ i b, inv i b → supportStepPost inv post (i + 1) (body i b)) (fuel : Nat) :
    ∀ start initial, inv start initial → (∀ b, inv (start + fuel) b → post b) →
      post (forIn (m := Id) (List.range' start fuel) initial body) := by
  induction fuel with
  | zero => intro start initial h finish; exact finish initial h
  | succ fuel ih =>
    intro start initial h finish
    rw [List.range'_succ, List.forIn_cons]
    change post (match body start initial with
      | .done b => b
      | .yield b => forIn (m := Id) (List.range' (start + 1) fuel) b body)
    have hs := step start initial h
    cases hb : body start initial with
    | done b => simpa only [hb, supportStepPost] using hs
    | yield b =>
      apply ih (start + 1) b (by simpa only [hb, supportStepPost] using hs)
      intro final hf
      apply finish final
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf

private structure SupportContext (snapshot : State) (count : Nat) where
  initial : State
  target : Lit
  reasonId : Nat
  lits : Array Lit
  storage : ReasonStorage snapshot initial
  packed : PackedClause snapshot reasonId lits
  nonempty : 0 < lits.size
  member : TrailMember snapshot count target
  tails : ∀ j, 0 < j → j < lits.size → TrailMember snapshot count lits[j]!

private structure SupportInv {snapshot : State} {count : Nat}
    (c : SupportContext snapshot count) (cursor : Nat) (acc : ImpliedScanState) : Prop where
  support : MarkSupport (TrailMember snapshot count) c.initial acc.2
  noReturn : acc.1 = none
  lower : c.reasonId + 1 ≤ cursor
  upper : cursor ≤ c.reasonId + c.lits.size

private structure SupportPost {snapshot : State} {count : Nat}
    (c : SupportContext snapshot count) (acc : ImpliedScanState) : Prop where
  support : MarkSupport (TrailMember snapshot count) c.initial acc.2
  returned : ∀ result, acc.1 = some result →
    MarkSupport (TrailMember snapshot count) c.initial result.1

private theorem support_scan_step {snapshot : State} {count : Nat}
    (c : SupportContext snapshot count) (recurse : State → Lit → State × Bool)
    (recursive : ∀ s lit, ReasonStorage snapshot s → TrailMember snapshot count lit →
      MarkSupport (TrailMember snapshot count) s (recurse s lit).1)
    (cursor : Nat) (acc : ImpliedScanState) (inv : SupportInv c cursor acc) :
    supportStepPost (SupportInv c) (SupportPost c) (cursor + 1)
      (impliedScanBody recurse c.target cursor acc) := by
  simp only [impliedScanBody]
  split
  · exact ⟨inv.support, by intro result impossible; cases impossible⟩
  · rename_i nonzero
    have storage := c.storage.markFrame inv.support.frame
    have before : cursor < c.reasonId + c.lits.size := by
      by_cases before : cursor < c.reasonId + c.lits.size
      · exact before
      · have equal : cursor = c.reasonId + c.lits.size := by have := inv.upper; omega
        have zero : acc.2.db cursor = 0 := by rw [storage.db, equal]; exact c.packed.terminator
        simp only [zero, beq_self_eq_true, not_true_eq_false] at nonzero
    let j := cursor - c.reasonId
    have positive : 0 < j := by have := inv.lower; omega
    have within : j < c.lits.size := by have := inv.lower; omega
    have position : cursor = c.reasonId + j := by have := inv.lower; omega
    have read : acc.2.db cursor = c.lits[j]! := by rw [storage.db, position]; exact c.packed.literals j within
    have member : TrailMember snapshot count (acc.2.db cursor) := read.symm ▸ c.tails j positive within
    split
    · have nextSupport := recursive acc.2 (acc.2.db cursor) storage member
      cases execute : recurse acc.2 (acc.2.db cursor) with
      | mk next follows =>
        have nextSupport' : MarkSupport (TrailMember snapshot count) acc.2 next := by
          simpa only [execute] using nextSupport
        have combined := inv.support.trans nextSupport'
        split
        · refine ⟨combined, ?_⟩
          intro result returned
          cases returned
          exact combined.trans (markSupport_setMark _ _ 5 c.member (by decide))
        · exact ⟨combined, rfl, by have := inv.lower; omega, by omega⟩
    · exact ⟨inv.support, rfl, by have := inv.lower; omega, by omega⟩

private theorem support_scan_post {snapshot : State} {count : Nat}
    (c : SupportContext snapshot count) (recurse : State → Lit → State × Bool)
    (recursive : ∀ s lit, ReasonStorage snapshot s → TrailMember snapshot count lit →
      MarkSupport (TrailMember snapshot count) s (recurse s lit).1) :
    SupportPost c (forIn (m := Id) [c.reasonId + 1 : c.initial.arena.size]
      (none, c.initial) (impliedScanBody recurse c.target)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  apply supportRange_post _ (SupportInv c) (SupportPost c) (support_scan_step c recurse recursive)
  · change SupportInv c (c.reasonId + 1) (none, c.initial)
    exact ⟨.refl _ _, rfl, Nat.le_refl _, by have := c.nonempty; omega⟩
  · intro acc inv
    have arenaSize := congrArg Array.size c.storage.arena
    have endBound := c.packed.endBound
    have upper := inv.upper
    simp only [Std.Legacy.Range.size, Nat.div_one] at upper
    exact False.elim (by omega)

/-- For a concrete reason DAG, the actual recursive minimizer only tags its
snapshot's false literals and preserves every existing nonzero mark. -/
theorem implied_markSupport {formula : CNF Nat} {snapshot : State} {count : Nat} {rank : Lit → Nat}
    (graph : ReasonGraph formula snapshot count rank) (fuel : Nat) (s : State) (lit : Lit)
    (storage : ReasonStorage snapshot s) (member : TrailMember snapshot count lit) :
    MarkSupport (TrailMember snapshot count) s (implied fuel s lit).1 := by
  induction fuel generalizing s lit with
  | zero => exact .refl _ _
  | succ fuel ih =>
    by_cases cached : 2 < s.mark lit
    · rw [implied_cached fuel s lit cached]
      exact .refl _ _
    · by_cases decision : s.reason lit = 0
      · rw [implied_decision fuel s lit (Nat.le_of_not_lt cached) decision]
        exact .refl _ _
      · have nondecision : snapshot.reason lit ≠ 0 := by simpa only [storage.reason lit] using decision
        obtain ⟨lits, packed, nonempty, _, _, tails⟩ := graph.clause_of_member member nondecision
        let c : SupportContext snapshot count :=
          ⟨s, lit, snapshot.reason lit, lits, storage, packed, nonempty, member,
            fun j positive within => (tails j positive within).1⟩
        let result : ImpliedScanState := forIn (m := Id) [c.reasonId + 1 : s.arena.size]
          (none, s) (impliedScanBody (implied fuel) lit)
        have post : SupportPost c result := support_scan_post c (implied fuel) ih
        rw [implied.eq_2]
        dsimp only [Id.run]
        rw [ite_eq_right cached]
        have decisionBool : ¬ (s.reason lit == 0) = true := by simpa using decision
        rw [ite_eq_right decisionBool]
        simp only [bind, pure]
        unfold Break.runK.match_1
        rw [storage.reason lit]
        change MarkSupport (TrailMember snapshot count) s
          (Option.casesOn (motive := fun _ => State × Bool) result.1
            (result.2.setMark lit 6, true) (fun r => r)).1
        cases returned : result.1 with
        | none => exact post.support.trans (markSupport_setMark _ _ 6 member (by decide))
        | some answer => exact post.returned answer returned

end MicrosatLean.Verification.Analysis
