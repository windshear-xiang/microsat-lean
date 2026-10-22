import MicrosatLean.Verification.Analysis.ImpliedSound
import MicrosatLean.Verification.Logic.Minimization

namespace MicrosatLean.Verification.Analysis

open CDCL Representation
open Std.Sat

/-!
Semantic refinement of the actual backward learned-clause construction.
The original MARK leaves and their trail ranks are frozen. A processed leaf
is either retained in the concrete output or derived from strictly earlier
original leaves. The latter certificates remain valid after later MARK tags
are cleared, because their assumptions refer to the frozen original set.
-/

abbrev LearnedAcc := State × Array Lit × Nat × Bool

/-- A proof-only name for the elaborated body of `CDCL.buildLearned`. -/
def learnedBody (candidate offset : Nat) (acc : LearnedAcc) :
    Id (ForInStep LearnedAcc) := Id.run do
  let mut s := acc.1
  let mut learned := acc.2.1
  let mut lbd := acc.2.2.1
  let mut levelUsed := acc.2.2.2
  let p := candidate - offset
  let lit := s.trail[p]!
  if s.mark lit == 2 then
    let (next, follows) := implied (s.nVars + 1) s lit
    s := next
    if !follows then
      learned := learned.push lit
      levelUsed := true
  if s.reason lit == 0 then
    if levelUsed then
      lbd := lbd + 1
    levelUsed := false
    if learned.size == 1 then
      s := { s with processed := p }
  s := s.setMark lit 1
  return .yield (s, learned, lbd, levelUsed)

theorem buildLearned_eq_loop (s : State) (candidate : Nat) :
    buildLearned s candidate =
      let result := forIn (m := Id) [:candidate + 1 - s.forced]
        ({ s with processed := candidate }, #[], 0, false) (learnedBody candidate)
      (result.1, result.2.1, result.2.2.1) := by
  rfl

private theorem rangeList_invariant {β : Type} (body : Nat → β → Id (ForInStep β))
    (yields : ∀ i b, ∃ next, body i b = .yield next)
    (inv : Nat → β → Prop)
    (limit : Nat)
    (step : ∀ i b, i < limit → inv i b → inv (i + 1) (body i b).value) (fuel : Nat) :
    ∀ start initial, start + fuel ≤ limit → inv start initial →
      inv (start + fuel) (forIn (m := Id) (List.range' start fuel) initial body) := by
  induction fuel with
  | zero => intro _ _ _ h; exact h
  | succ fuel ih =>
    intro start initial bound h
    rw [List.range'_succ, List.forIn_cons]
    change inv (start + (fuel + 1)) (match body start initial with
      | .done b => b
      | .yield b => forIn (m := Id) (List.range' (start + 1) fuel) b body)
    obtain ⟨b, hb⟩ := yields start initial
    have next := step start initial (by omega) h
    rw [hb]
    have tail := ih (start + 1) b (by omega)
      (by simpa only [hb, ForInStep.value_yield] using next)
    simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using tail

private structure LearnedContext (formula : CNF Nat) (snapshot : State) (count : Nat)
    (rank : Lit → Nat) (leaves : Lit → Prop) where
  graph : ReasonGraph formula snapshot count rank
  candidate : Nat
  candidateBound : candidate < count
  lower : Nat
  leafRange : ∀ lit, leaves lit →
    TrailMember snapshot count lit ∧ lower ≤ rank lit ∧ rank lit ≤ candidate

private structure LearnedInv {formula : CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (c : LearnedContext formula snapshot count rank leaves) (offset : Nat) (acc : LearnedAcc) : Prop where
  storage : ReasonStorage snapshot acc.1
  trail : acc.1.trail = snapshot.trail
  cache : ImpliedCache formula snapshot count rank leaves acc.1
  unprocessed : ∀ lit, leaves lit → rank lit + offset ≤ c.candidate → acc.1.mark lit = 2
  processed : ∀ lit, leaves lit → c.candidate < rank lit + offset →
    lit ∈ acc.2.1 ∨ DerivedLiteral formula rank leaves lit
  retained : ∀ lit ∈ acc.2.1, leaves lit

private theorem LearnedInv.retuple {formula : CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    {c : LearnedContext formula snapshot count rank leaves} {offset : Nat} {acc : LearnedAcc}
    (inv : LearnedInv c offset acc) (p lbd : Nat) (used : Bool) :
    LearnedInv c offset ({ acc.1 with processed := p }, acc.2.1, lbd, used) :=
  ⟨⟨inv.storage.arena, inv.storage.reasons⟩, inv.trail,
    ⟨inv.cache.tags, inv.cache.marked, inv.cache.cached⟩,
    inv.unprocessed, inv.processed, inv.retained⟩

private def finishBody (p lit : Nat) (s : State) (learned : Array Lit) (lbd : Nat) (used : Bool) :
    Id (ForInStep LearnedAcc) := Id.run do
  let mut s := s
  let mut lbd := lbd
  let mut used := used
  if s.reason lit == 0 then
    if used then
      lbd := lbd + 1
    used := false
    if learned.size == 1 then
      s := { s with processed := p }
  return .yield (s.setMark lit 1, learned, lbd, used)

private theorem learnedBody_eq (candidate offset : Nat) (acc : LearnedAcc) :
    learnedBody candidate offset acc =
      let lit := acc.1.trail[candidate - offset]!
      if acc.1.mark lit == 2 then
        let result := implied (acc.1.nVars + 1) acc.1 lit
        finishBody (candidate - offset) lit result.1
          (if !result.2 then acc.2.1.push lit else acc.2.1) acc.2.2.1
          (if !result.2 then true else acc.2.2.2)
      else finishBody (candidate - offset) lit acc.1 acc.2.1 acc.2.2.1 acc.2.2.2 := by
  simp only [learnedBody, finishBody, Id.run, pure]
  split
  · split <;> rfl
  · rfl

private theorem finishBody_yields (p lit : Nat) (s : State) (learned : Array Lit)
    (lbd : Nat) (used : Bool) : ∃ next, finishBody p lit s learned lbd used = .yield next := by
  simp only [finishBody, Id.run, pure]
  split <;> repeat first | split | exact ⟨_, rfl⟩

private theorem learnedBody_yields (candidate offset : Nat) (acc : LearnedAcc) :
    ∃ next, learnedBody candidate offset acc = .yield next := by
  rw [learnedBody_eq]
  dsimp only
  split <;> exact finishBody_yields ..

private theorem finishBody_inv {formula : CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    {c : LearnedContext formula snapshot count rank leaves} {offset p lit : Nat}
    {s : State} {learned : Array Lit} {lbd : Nat} {used : Bool}
    (inv : LearnedInv c offset (s.setMark lit 1, learned, lbd, used)) :
    LearnedInv c offset (finishBody p lit s learned lbd used).value := by
  simp only [finishBody, Id.run, pure]
  split <;> repeat first
    | split
    | exact inv
    | exact inv.retuple _ _ _

private theorem advance {formula : CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    {c : LearnedContext formula snapshot count rank leaves} {offset : Nat} {acc : LearnedAcc}
    (inv : LearnedInv c offset acc) (within : offset < c.candidate + 1 - c.lower)
    (next : State) (learned : Array Lit) (lbd : Nat) (used : Bool)
    (frame : MarkFrame acc.1 next)
    (cache : ImpliedCache formula snapshot count rank leaves next)
    (included : ∀ lit ∈ acc.2.1, lit ∈ learned)
    (retained : ∀ lit ∈ learned, leaves lit)
    (earlier : ∀ lit, leaves lit → rank lit + offset < c.candidate → next.mark lit = 2)
    (current : leaves acc.1.trail[c.candidate - offset]! →
      acc.1.trail[c.candidate - offset]! ∈ learned ∨
        DerivedLiteral formula rank leaves acc.1.trail[c.candidate - offset]!) :
    LearnedInv c (offset + 1)
      (next.setMark acc.1.trail[c.candidate - offset]! 1, learned, lbd, used) := by
  let lit := acc.1.trail[c.candidate - offset]!
  have indexBound : c.candidate - offset < count := by have := c.candidateBound; omega
  have offsetBound : offset ≤ c.candidate := by omega
  have read : lit = snapshot.trail[c.candidate - offset]! := by simp only [lit, inv.trail]
  have rankLit : rank lit = c.candidate - offset := by rw [read]; exact c.graph.ranks _ indexBound
  refine ⟨(inv.storage.markFrame frame).markFrame (markFrame_setMark next lit 1), ?_,
    cache.setMark_one lit, ?_, ?_, retained⟩
  · exact frame.trail.trans inv.trail
  · intro other leaf pending
    have strictlyEarlier : rank other + offset < c.candidate := by omega
    have different : lit ≠ other := by
      intro equal
      rw [equal] at rankLit
      omega
    rw [setMark_mark_other different]
    exact earlier other leaf strictlyEarlier
  · intro other leaf visited
    by_cases wasVisited : c.candidate < rank other + offset
    · rcases inv.processed other leaf wasVisited with kept | derived
      · exact Or.inl (included other kept)
      · exact Or.inr derived
    · have equalRank : rank other = c.candidate - offset := by omega
      have equal : other = lit :=
        (c.graph.member_eq_of_rank (c.leafRange other leaf).1 equalRank).trans read.symm
      have leafLit : leaves lit := by rw [← equal]; exact leaf
      simpa only [equal] using current leafLit

private theorem learnedBody_step {formula : CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (c : LearnedContext formula snapshot count rank leaves) (offset : Nat) (acc : LearnedAcc)
    (within : offset < c.candidate + 1 - c.lower) (inv : LearnedInv c offset acc) :
    LearnedInv c (offset + 1) (learnedBody c.candidate offset acc).value := by
  let lit := acc.1.trail[c.candidate - offset]!
  have indexBound : c.candidate - offset < count := by have := c.candidateBound; omega
  have offsetBound : offset ≤ c.candidate := by omega
  have read : lit = snapshot.trail[c.candidate - offset]! := by simp only [lit, inv.trail]
  have member : TrailMember snapshot count lit := ⟨_, indexBound, read.symm⟩
  have rankLit : rank lit = c.candidate - offset := by rw [read]; exact c.graph.ranks _ indexBound
  have differentEarlier : ∀ other, rank other + offset < c.candidate → other ≠ lit := by
    intro other earlier equal
    rw [equal, rankLit] at earlier
    omega
  rw [learnedBody_eq]
  dsimp only
  change LearnedInv c (offset + 1)
    (if acc.1.mark lit == 2 then
      let result := implied (acc.1.nVars + 1) acc.1 lit
      finishBody (c.candidate - offset) lit result.1
        (if !result.2 then acc.2.1.push lit else acc.2.1) acc.2.2.1
        (if !result.2 then true else acc.2.2.2)
    else finishBody (c.candidate - offset) lit acc.1 acc.2.1 acc.2.2.1 acc.2.2.2).value
  split
  · have marked : acc.1.mark lit = 2 := by simpa using ‹(acc.1.mark lit == 2) = true›
    have leaf := inv.cache.marked lit member marked
    have sound := implied_sound c.graph (acc.1.nVars + 1) acc.1 lit inv.storage inv.cache member
    have frame := implied_markFrame (acc.1.nVars + 1) acc.1 lit
    have preserve : ∀ other, leaves other → rank other + offset < c.candidate →
        (implied (acc.1.nVars + 1) acc.1 lit).1.mark other = 2 := by
      intro other original earlier
      exact implied_preserves_mark_two _ _ _ _ (differentEarlier other earlier)
        (inv.unprocessed other original (Nat.le_of_lt earlier))
    cases result : implied (acc.1.nVars + 1) acc.1 lit with
    | mk next follows =>
      simp only [result] at sound frame preserve ⊢
      cases follows with
      | false =>
        simp only [Bool.not_false, ↓reduceIte]
        apply finishBody_inv
        apply advance inv within next (acc.2.1.push lit) _ _ frame sound.1
        · intro other old
          exact Array.mem_push.mpr (Or.inl old)
        · intro other retained
          rcases Array.mem_push.mp retained with old | equal
          · exact inv.retained other old
          · exact equal ▸ leaf
        · exact preserve
        · intro _
          exact Or.inl (Array.mem_push.mpr (Or.inr rfl))
      | true =>
        simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
        apply finishBody_inv
        apply advance inv within next acc.2.1 _ _ frame sound.1
        · exact fun _ h => h
        · exact inv.retained
        · exact preserve
        · intro _
          exact Or.inr (sound.2 rfl)
  · have notMarked : acc.1.mark lit ≠ 2 := by simpa using ‹¬ (acc.1.mark lit == 2) = true›
    apply finishBody_inv
    apply advance inv within acc.1 acc.2.1 _ _ (MarkFrame.refl _) inv.cache
    · exact fun _ h => h
    · exact inv.retained
    · intro other leaf earlier
      exact inv.unprocessed other leaf (Nat.le_of_lt earlier)
    · intro leaf
      exact False.elim (notMarked (inv.unprocessed lit leaf (by omega)))

/-- The actual output contains only original MARK leaves. Every original leaf
not retained has a derivation from strictly earlier original leaves. The
original leaves are precisely bounded by the scanned interval; sound initial
tag-6 caches are supplied independently through `ImpliedCache`. -/
theorem buildLearned_certificate {formula : CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop}
    (graph : ReasonGraph formula snapshot count rank) (s : State) (candidate : Nat)
    (candidateBound : candidate < count) (storage : ReasonStorage snapshot s)
    (trail : s.trail = snapshot.trail) (cache : ImpliedCache formula snapshot count rank leaves s)
    (marked : ∀ lit, leaves lit → s.mark lit = 2)
    (leafRange : ∀ lit, leaves lit →
      TrailMember snapshot count lit ∧ s.forced ≤ rank lit ∧ rank lit ≤ candidate) :
    let result := buildLearned s candidate
    ReasonStorage snapshot result.1 ∧ result.1.trail = snapshot.trail ∧
      ImpliedCache formula snapshot count rank leaves result.1 ∧
      (∀ lit, leaves lit → lit ∈ result.2.1 ∨ DerivedLiteral formula rank leaves lit) ∧
      (∀ lit ∈ result.2.1, leaves lit) := by
  let c : LearnedContext formula snapshot count rank leaves :=
    ⟨graph, candidate, candidateBound, s.forced, leafRange⟩
  let initial : LearnedAcc := ({ s with processed := candidate }, #[], 0, false)
  let limit := candidate + 1 - s.forced
  let result : LearnedAcc := forIn (m := Id) [:limit] initial (learnedBody candidate)
  have first : LearnedInv c 0 initial := by
    refine ⟨⟨storage.arena, storage.reasons⟩, trail,
      ⟨cache.tags, cache.marked, cache.cached⟩, ?_, ?_, ?_⟩
    · intro lit leaf _
      exact marked lit leaf
    · intro lit leaf visited
      change candidate < rank lit + 0 at visited
      have := (leafRange lit leaf).2.2
      have : False := by omega
      exact this.elim
    · intro lit impossible
      simp only [initial, Array.not_mem_empty] at impossible
  have last : LearnedInv c limit result := by
    dsimp only [result]
    rw [Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
    simpa only [Nat.zero_add] using rangeList_invariant (learnedBody candidate) (learnedBody_yields candidate)
      (LearnedInv c) limit (learnedBody_step c) limit 0 initial (by omega) first
  rw [buildLearned_eq_loop]
  change ReasonStorage snapshot result.1 ∧ result.1.trail = snapshot.trail ∧
    ImpliedCache formula snapshot count rank leaves result.1 ∧
    (∀ lit, leaves lit → lit ∈ result.2.1 ∨ DerivedLiteral formula rank leaves lit) ∧
    (∀ lit ∈ result.2.1, leaves lit)
  refine ⟨last.storage, last.trail, last.cache, ?_, last.retained⟩
  intro lit leaf
  apply last.processed lit leaf
  have lower := (leafRange lit leaf).2.1
  have upper := (leafRange lit leaf).2.2
  change candidate < rank lit + (candidate + 1 - s.forced)
  omega

/-- A ranked form of ordered elimination, specialized to the encoded actual
clause arrays. A retained clause falsifies every original leaf by forward rank
induction. Removed leaves only consume strictly earlier facts from that
induction, never their own falsity as a premise. -/
theorem entails_of_leaf_certificates {formula : CNF Nat} {rank : Lit → Nat}
    {leaves : Lit → Prop} {original learned : Array Lit}
    (originalLeaves : ∀ lit, leaves lit ↔ lit ∈ original)
    (entailed : CNF.EntailsClause formula (clauseView original))
    (certificate : ∀ lit, leaves lit → lit ∈ learned ∨ DerivedLiteral formula rank leaves lit) :
    CNF.EntailsClause formula (clauseView learned) := by
  intro a model
  by_cases satisfied : CNF.Clause.Sat a (clauseView learned)
  · exact satisfied
  · have retained : ∀ lit ∈ learned, Falsifies a lit := by
      intro lit member
      apply CNF.Clause.not_sat_iff_forall_mem_ne.mp satisfied (literalView lit)
      exact clauseView_mem.mpr ⟨lit, member, rfl⟩
    have byRank : ∀ position lit, rank lit = position → leaves lit → Falsifies a lit := by
      intro position
      induction position using Nat.strongRecOn with
      | ind position ih =>
        intro lit ranked leaf
        rcases certificate lit leaf with kept | derived
        · exact retained lit kept
        · apply derived a model
          intro earlier original before
          apply ih (rank earlier) (by omega) earlier rfl original
    have allFalse : ¬ CNF.Clause.Sat a (clauseView original) := by
      apply CNF.Clause.not_sat_iff_forall_mem_ne.mpr
      intro viewed member
      obtain ⟨lit, originalMember, rfl⟩ := clauseView_mem.mp member
      exact byRank (rank lit) lit rfl ((originalLeaves lit).mpr originalMember)
    exact False.elim (allFalse (entailed a model))

/-- The actual learned array remains entailed by the input when its original
MARK clause is entailed. All removal hypotheses are discharged by the actual
`implied` recursion and actual backward loop above. Establishing this entry
state from reachable first-UIP analysis remains a separate obligation. -/
theorem buildLearned_entails {formula : CNF Nat} {snapshot : State} {count : Nat}
    {rank : Lit → Nat} {leaves : Lit → Prop} {original : Array Lit}
    (graph : ReasonGraph formula snapshot count rank) (s : State) (candidate : Nat)
    (candidateBound : candidate < count) (storage : ReasonStorage snapshot s)
    (trail : s.trail = snapshot.trail) (cache : ImpliedCache formula snapshot count rank leaves s)
    (marked : ∀ lit, leaves lit → s.mark lit = 2)
    (leafRange : ∀ lit, leaves lit →
      TrailMember snapshot count lit ∧ s.forced ≤ rank lit ∧ rank lit ≤ candidate)
    (originalLeaves : ∀ lit, leaves lit ↔ lit ∈ original)
    (entailed : CNF.EntailsClause formula (clauseView original)) :
    CNF.EntailsClause formula (clauseView (buildLearned s candidate).2.1) := by
  apply entails_of_leaf_certificates originalLeaves entailed
  exact (buildLearned_certificate graph s candidate candidateBound storage trail cache marked leafRange).2.2.2.1

end MicrosatLean.Verification.Analysis
