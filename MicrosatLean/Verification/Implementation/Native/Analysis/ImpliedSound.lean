import MicrosatLean.Verification.Implementation.Native.Analysis.ReasonGraph

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation
open Std.Sat

/-!
Soundness of the actual `CDCL.implied` recursion. Original MARK leaves and
their trail ranks are fixed throughout a call. The cache invariant gives tag 6
its meaning independently of the candidate under examination. The range-loop
invariant also proves that successful completion reaches the reason's real
zero terminator; mere exhaustion of the arena is never used as a proof step.
-/

private def stepPost {β : Type} (inv : Nat → β → Prop) (post : β → Prop)
    (next : Nat) (result : ForInStep β) : Prop :=
  match result with
  | .done b => post b
  | .yield b => inv next b

private theorem rangeList_post {β : Type} (body : Nat → β → Id (ForInStep β))
    (inv : Nat → β → Prop) (post : β → Prop)
    (step : ∀ i b, inv i b → stepPost inv post (i + 1) (body i b)) (fuel : Nat) :
    ∀ start initial, inv start initial →
      (∀ b, inv (start + fuel) b → post b) →
      post (forIn (m := Id) (List.range' start fuel) initial body) := by
  induction fuel with
  | zero =>
    intro start initial h finish
    exact finish initial h
  | succ fuel ih =>
    intro start initial h finish
    rw [List.range'_succ, List.forIn_cons]
    change post (match body start initial with
      | .done b => b
      | .yield b => forIn (m := Id) (List.range' (start + 1) fuel) b body)
    have hs := step start initial h
    cases hb : body start initial with
    | done b => simpa only [hb, stepPost] using hs
    | yield b =>
      apply ih (start + 1) b (by simpa only [hb, stepPost] using hs)
      intro final hf
      apply finish final
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hf

private structure ScanContext (formula : Std.Sat.CNF Nat) (snapshot : State) (count : Nat)
    (rank : Lit → Nat) (leaves : Lit → Prop) where
  initial : State
  target : Lit
  reasonId : Nat
  lits : Array Lit
  storage : ReasonStorage snapshot initial
  packed : PackedClause snapshot reasonId lits
  nonempty : 0 < lits.size
  head : lits[0]! = target.negate
  entailed : CNF.EntailsClause formula (clauseView lits)
  earlier : ∀ j, 0 < j → j < lits.size →
    TrailMember snapshot count lits[j]! ∧ rank lits[j]! < rank target

private structure ScanInv {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (c : ScanContext formula snapshot count rank leaves) (cursor : Nat) (acc : ImpliedScanState) : Prop where
  frame : MarkFrame c.initial acc.2
  cache : ImpliedCache formula snapshot count rank leaves acc.2
  noReturn : acc.1 = none
  lower : c.reasonId + 1 ≤ cursor
  upper : cursor ≤ c.reasonId + c.lits.size
  tails : ∀ j, 0 < j → j < c.lits.size → c.reasonId + j < cursor →
    LeafConsequence formula rank leaves (rank c.target) c.lits[j]!

private structure ScanPost {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (c : ScanContext formula snapshot count rank leaves) (acc : ImpliedScanState) : Prop where
  frame : MarkFrame c.initial acc.2
  cache : ImpliedCache formula snapshot count rank leaves acc.2
  returned : ∀ result, acc.1 = some result →
    MarkFrame c.initial result.1 ∧ ImpliedCache formula snapshot count rank leaves result.1 ∧
      result.2 = false
  tails : acc.1 = none → ∀ j, 0 < j → j < c.lits.size →
    LeafConsequence formula rank leaves (rank c.target) c.lits[j]!

private theorem cursor_read {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    {c : ScanContext formula snapshot count rank leaves} {cursor : Nat} {acc : ImpliedScanState}
    (inv : ScanInv c cursor acc) {j : Nat} (bound : j < c.lits.size)
    (position : cursor = c.reasonId + j) : acc.2.db cursor = c.lits[j]! := by
  rw [(c.storage.markFrame inv.frame).db cursor, position]
  exact c.packed.literals j bound

private theorem cursor_lt_end_of_nonzero {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    {c : ScanContext formula snapshot count rank leaves} {cursor : Nat} {acc : ImpliedScanState}
    (inv : ScanInv c cursor acc) (nonzero : acc.2.db cursor ≠ 0) :
    cursor < c.reasonId + c.lits.size := by
  by_cases before : cursor < c.reasonId + c.lits.size
  · exact before
  · have equal : cursor = c.reasonId + c.lits.size := by have := inv.upper; omega
    apply False.elim
    apply nonzero
    rw [(c.storage.markFrame inv.frame).db cursor, equal]
    exact c.packed.terminator

private theorem cursor_eq_end_of_zero {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    {c : ScanContext formula snapshot count rank leaves} {cursor : Nat} {acc : ImpliedScanState}
    (inv : ScanInv c cursor acc) (zero : acc.2.db cursor = 0) :
    cursor = c.reasonId + c.lits.size := by
  by_cases equal : cursor = c.reasonId + c.lits.size
  · exact equal
  · have before : cursor < c.reasonId + c.lits.size := by have := inv.upper; omega
    let j := cursor - c.reasonId
    have bound : j < c.lits.size := by have := inv.lower; omega
    have position : cursor = c.reasonId + j := by have := inv.lower; omega
    have member : c.lits[j]! ∈ c.lits := by
      simpa only [getElem!_pos c.lits j bound] using Array.getElem_mem bound
    have nz := (c.packed.wellFormed _ member).nonzero
    exact False.elim (nz ((cursor_read inv bound position).symm.trans zero))

private theorem scan_advance {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    {c : ScanContext formula snapshot count rank leaves} {cursor : Nat} {acc : ImpliedScanState}
    (inv : ScanInv c cursor acc) (before : cursor < c.reasonId + c.lits.size)
    (next : State) (frame : MarkFrame acc.2 next)
    (cache : ImpliedCache formula snapshot count rank leaves next)
    (current : LeafConsequence formula rank leaves (rank c.target) (acc.2.db cursor)) :
    ScanInv c (cursor + 1) (none, next) := by
  refine ⟨inv.frame.trans frame, cache, rfl, ?_, ?_, ?_⟩
  · have := inv.lower
    omega
  · omega
  · intro j positive bound visited
    by_cases old : c.reasonId + j < cursor
    · exact inv.tails j positive bound old
    · have position : cursor = c.reasonId + j := by omega
      exact cursor_read inv bound position ▸ current

private theorem scan_step {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (c : ScanContext formula snapshot count rank leaves) (recurse : State → Lit → State × Bool)
    (frame : ∀ s lit, MarkFrame s (recurse s lit).1)
    (sound : ∀ s lit, ReasonStorage snapshot s → ImpliedCache formula snapshot count rank leaves s →
      TrailMember snapshot count lit →
      ImpliedCache formula snapshot count rank leaves (recurse s lit).1 ∧
        ((recurse s lit).2 = true → DerivedLiteral formula rank leaves lit))
    (cursor : Nat) (acc : ImpliedScanState) (inv : ScanInv c cursor acc) :
    stepPost (ScanInv c) (ScanPost c) (cursor + 1)
      (impliedScanBody recurse c.target cursor acc) := by
  simp only [impliedScanBody]
  split
  · rename_i hz
    have atEnd := cursor_eq_end_of_zero inv (by simpa using hz)
    refine ⟨inv.frame, inv.cache, ?_, ?_⟩
    · intro result impossible
      cases impossible
    · intro _ j positive bound
      apply inv.tails j positive bound
      omega
  · rename_i hnz
    have before := cursor_lt_end_of_nonzero inv (by simpa using hnz)
    let j := cursor - c.reasonId
    have positive : 0 < j := by have := inv.lower; omega
    have bound : j < c.lits.size := by have := inv.lower; omega
    have position : cursor = c.reasonId + j := by have := inv.lower; omega
    have read := cursor_read inv bound position
    obtain ⟨member, earlier⟩ := c.earlier j positive bound
    have member' : TrailMember snapshot count (acc.2.db cursor) := read.symm ▸ member
    have earlier' : rank (acc.2.db cursor) < rank c.target := read.symm ▸ earlier
    split
    · have recursive := sound acc.2 (acc.2.db cursor)
        (c.storage.markFrame inv.frame) inv.cache member'
      cases heq : recurse acc.2 (acc.2.db cursor) with
      | mk next follows =>
        have nextFrame : MarkFrame acc.2 next := by simpa only [heq] using frame acc.2 (acc.2.db cursor)
        have nextCache : ImpliedCache formula snapshot count rank leaves next := by
          simpa only [heq] using recursive.1
        split
        · refine ⟨inv.frame.trans nextFrame, nextCache, ?_, ?_⟩
          · intro result hr
            cases hr
            exact ⟨(inv.frame.trans nextFrame).trans (markFrame_setMark next c.target 5),
              nextCache.setMark_failed c.target, rfl⟩
          · intro impossible
            cases impossible
        · have followsTrue : follows = true := by simpa using ‹¬ (!follows) = true›
          have derived : DerivedLiteral formula rank leaves (acc.2.db cursor) := by
            apply recursive.2
            simpa only [heq] using followsTrue
          exact scan_advance inv before next nextFrame nextCache
            (derived.mono (Nat.le_of_lt earlier'))
    · have marked : acc.2.mark (acc.2.db cursor) = 2 := by
        simpa using ‹¬ (acc.2.mark (acc.2.db cursor) != 2) = true›
      exact scan_advance inv before acc.2 (MarkFrame.refl _) inv.cache
        (leafConsequence_of_leaf (inv.cache.marked _ member' marked) earlier')

private theorem scan_post {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (c : ScanContext formula snapshot count rank leaves) (recurse : State → Lit → State × Bool)
    (frame : ∀ s lit, MarkFrame s (recurse s lit).1)
    (sound : ∀ s lit, ReasonStorage snapshot s → ImpliedCache formula snapshot count rank leaves s →
      TrailMember snapshot count lit →
      ImpliedCache formula snapshot count rank leaves (recurse s lit).1 ∧
        ((recurse s lit).2 = true → DerivedLiteral formula rank leaves lit))
    (cache : ImpliedCache formula snapshot count rank leaves c.initial) :
    ScanPost c (forIn (m := Id) [c.reasonId + 1 : c.initial.arena.size]
      (none, c.initial) (impliedScanBody recurse c.target)) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  apply rangeList_post (impliedScanBody recurse c.target) (ScanInv c) (ScanPost c)
    (scan_step c recurse frame sound) (c.initial.arena.size - (c.reasonId + 1))
  · refine ⟨MarkFrame.refl _, cache, rfl, Nat.le_refl _, ?_, ?_⟩
    · have := c.nonempty
      omega
    · intro j positive _ visited
      omega
  · intro acc inv
    have arenaSize : c.initial.arena.size = snapshot.arena.size := congrArg Array.size c.storage.arena
    have endBound := c.packed.endBound
    have upper := inv.upper
    have nonempty := c.nonempty
    have lower := c.packed.startLower
    exact False.elim (by omega)

/-- Actual minimization preserves valid caches and a successful answer derives
the candidate from the input and strictly earlier original MARK leaves.
The fixed reason graph and initial cache are independent hypotheses; neither
assumes the candidate false or assumes correctness of this function call. -/
theorem implied_sound {formula : Std.Sat.CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop} (graph : ReasonGraph formula snapshot count rank)
    (fuel : Nat) (s : State) (lit : Lit) (storage : ReasonStorage snapshot s)
    (cache : ImpliedCache formula snapshot count rank leaves s)
    (member : TrailMember snapshot count lit) :
    ImpliedCache formula snapshot count rank leaves (implied fuel s lit).1 ∧
      ((implied fuel s lit).2 = true → DerivedLiteral formula rank leaves lit) := by
  induction fuel generalizing s lit with
  | zero => exact ⟨cache, by intro impossible; cases impossible⟩
  | succ fuel ih =>
    by_cases cached : 2 < s.mark lit
    · rw [implied_cached fuel s lit cached]
      refine ⟨cache, ?_⟩
      intro successful
      rcases cache.tags lit member with tag | tag | tag | tag | tag
      · omega
      · omega
      · omega
      · simp [tag] at successful
      · exact cache.cached lit member tag
    · by_cases decision : s.reason lit = 0
      · rw [implied_decision fuel s lit (Nat.le_of_not_lt cached) decision]
        exact ⟨cache, by intro impossible; cases impossible⟩
      · have nondecision : snapshot.reason lit ≠ 0 := by simpa only [storage.reason lit] using decision
        obtain ⟨lits, packed, nonempty, head, entailed, earlier⟩ := graph.clause_of_member member nondecision
        let c : ScanContext formula snapshot count rank leaves :=
          ⟨s, lit, snapshot.reason lit, lits, storage, packed, nonempty, head, entailed, earlier⟩
        let result : ImpliedScanState := forIn (m := Id) [c.reasonId + 1 : s.arena.size]
          (none, s) (impliedScanBody (implied fuel) lit)
        have post : ScanPost c result := scan_post c (implied fuel) (implied_markFrame fuel) ih cache
        rw [implied.eq_2]
        dsimp only [Id.run]
        rw [ite_eq_right cached]
        have decisionBool : ¬ (s.reason lit == 0) = true := by simpa using decision
        rw [ite_eq_right decisionBool]
        simp only [bind, pure]
        unfold Break.runK.match_1
        rw [storage.reason lit]
        change ImpliedCache formula snapshot count rank leaves
            (Option.casesOn (motive := fun _ => State × Bool) result.1
              (result.2.setMark lit 6, true) (fun r => r)).1 ∧
          ((Option.casesOn (motive := fun _ => State × Bool) result.1
              (result.2.setMark lit 6, true) (fun r => r)).2 = true →
            DerivedLiteral formula rank leaves lit)
        cases returned : result.1 with
        | none =>
          have derived := derived_of_reason c.nonempty c.head c.entailed (post.tails returned)
          exact ⟨post.cache.setMark_implied derived, fun _ => derived⟩
        | some answer =>
          have final := post.returned answer returned
          exact ⟨final.2.1, by intro impossible; rw [final.2.2] at impossible; cases impossible⟩

end MicrosatLean.Verification.Implementation.Native.Analysis
