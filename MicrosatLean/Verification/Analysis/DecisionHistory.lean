import MicrosatLean.Verification.Analysis.OriginMigration
import MicrosatLean.Verification.Analysis.AssertionLevel

namespace MicrosatLean.Verification.Analysis

open CDCL Representation

/-- Exact literal values in a retained prefix, independently of stale slots. -/
def PrefixLiterals (before after : State) (count : Nat) : Prop :=
  ∀ i, i < count → after.trail[i]! = before.trail[i]!

theorem PrefixLiterals.refl (s : State) (count : Nat) : PrefixLiterals s s count :=
  fun _ _ => rfl

theorem PrefixLiterals.variables {before after : State} {count : Nat}
    (savedPrefix : PrefixLiterals before after count) : PrefixVariablesPreserved before after count :=
  fun i bound => congrArg Lit.var (savedPrefix i bound)

theorem FalseBefore.transfer {before after : State} {count : Nat} {lit : Lit}
    (savedPrefix : PrefixLiterals before after count) (falseLit : FalseBefore before count lit) :
    FalseBefore after count lit := by
  obtain ⟨i, bound, value⟩ := falseLit
  exact ⟨i, bound, (savedPrefix i bound).trans value⟩

theorem PrefixUnitClosed.transfer {before after : State} {count : Nat} {lits : Array Lit}
    (closed : PrefixUnitClosed before count lits) (savedPrefix : PrefixLiterals before after count) :
    PrefixUnitClosed after count lits := by
  intro head member tails
  apply FalseBefore.transfer savedPrefix
  apply closed head member
  intro tail member different
  exact FalseBefore.transfer (fun i bound => (savedPrefix i bound).symm) (tails tail member different)

theorem PrefixUnitClosed.sameLiterals {s : State} {count : Nat} {old next : Array Lit}
    (closed : PrefixUnitClosed s count old) (same : SameLiterals next old) :
    PrefixUnitClosed s count next := by
  intro head member tails
  apply closed head ((same head).mp member)
  intro tail member different
  exact tails tail ((same tail).mpr member) different

/-- A concrete saved predecision state, its retained literal prefix, and the
unit closure of every clause there. No freshness or future preservation is a
field. Clause IDs and watch permutations do not affect this evidence. -/
def DecisionPrefix (s : State) (entries : List StoredClause) (decision : Nat) : Prop :=
  ∃ savedPrefix : State, savedPrefix.assigned = decision ∧ PrefixLiterals savedPrefix s decision ∧
    ∀ entry ∈ entries, PrefixUnitClosed savedPrefix decision entry.lits

/-- Every actual nonroot `reason = 0` trail boundary has a saved closed prefix.
Root assignments below `forced` are deliberately outside this quantification. -/
def DecisionHistory (s : State) (entries : List StoredClause) : Prop :=
  ∀ decision, s.forced ≤ decision → decision < s.assigned →
    s.reason s.trail[decision]! = 0 → DecisionPrefix s entries decision

/-- The propagation phase must establish this concrete predicate before the
next decision. Watch coverage alone is insufficient to establish it. -/
def PropagationClosed (s : State) (entries : List StoredClause) : Prop :=
  ∀ entry ∈ entries, PrefixUnitClosed s s.assigned entry.lits

theorem DecisionPrefix.closed {s : State} {entries : List StoredClause} {decision : Nat}
    (saved : DecisionPrefix s entries decision) :
    ∀ entry ∈ entries, PrefixUnitClosed s decision entry.lits := by
  obtain ⟨savedPrefix, _, equal, closed⟩ := saved
  exact fun entry member => (closed entry member).transfer equal

theorem DecisionHistory.of_closed {s : State} {entries : List StoredClause}
    (closed : ∀ decision, s.forced ≤ decision → decision < s.assigned →
      s.reason s.trail[decision]! = 0 →
      ∀ entry ∈ entries, PrefixUnitClosed s decision entry.lits) : DecisionHistory s entries := by
  intro decision lower before reason
  exact ⟨{ s with assigned := decision }, rfl, fun _ _ => rfl, closed decision lower before reason⟩

theorem DecisionHistory.origins {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (decision : Nat) (lower : s.forced ≤ decision)
    (before : decision < s.assigned) (reason : s.reason s.trail[decision]! = 0) :
    ∀ entry ∈ entries, ClauseOrigin s decision entry :=
  fun entry member => .beforeDecision ((history decision lower before reason).closed entry member)

theorem DecisionHistory.no_decisions {s : State} {entries : List StoredClause}
    (root : s.assigned ≤ s.forced) : DecisionHistory s entries := by
  intro decision lower before
  omega

/-- Retaining a literal prefix and its decision boundaries retains every
saved predecision state. Raising the root boundary merely removes records. -/
theorem DecisionHistory.truncate {before after : State} {entries : List StoredClause}
    (history : DecisionHistory before entries) (cursor : after.assigned ≤ before.assigned)
    (root : before.forced ≤ after.forced)
    (savedPrefix : PrefixLiterals before after after.assigned)
    (reasons : ∀ i, i < after.assigned →
      after.reason after.trail[i]! = before.reason before.trail[i]!) :
    DecisionHistory after entries := by
  intro decision lower bound zero
  obtain ⟨saved, count, oldPrefix, closed⟩ := history decision (by omega) (by omega)
    ((reasons decision bound).symm.trans zero)
  refine ⟨saved, count, ?_, closed⟩
  exact fun i beforeDecision => (savedPrefix i (by omega)).trans (oldPrefix i beforeDecision)

theorem DecisionHistory.frame {before after : State} {entries : List StoredClause}
    (history : DecisionHistory before entries) (cursor : after.assigned = before.assigned)
    (root : after.forced = before.forced) (trail : after.trail = before.trail)
    (reasons : after.reasons = before.reasons) : DecisionHistory after entries := by
  apply DecisionHistory.truncate history (Nat.le_of_eq cursor) (Nat.le_of_eq root.symm)
  · exact fun i _ => congrArg (fun words : Array Lit => words[i]!) trail
  · intro i _
    simp only [State.reason, trail, reasons]

/-- Clause deletion, relocation, and literal permutation preserve history
whenever each remaining clause has the same literals as a prior entry. -/
theorem DecisionHistory.restrict {s : State} {old next : List StoredClause}
    (history : DecisionHistory s old)
    (retained : ∀ entry ∈ next, ∃ prior ∈ old, SameLiterals entry.lits prior.lits) :
    DecisionHistory s next := by
  intro decision lower before reason
  obtain ⟨savedPrefix, count, equal, closed⟩ := history decision lower before reason
  refine ⟨savedPrefix, count, equal, ?_⟩
  intro entry member
  obtain ⟨prior, oldMember, same⟩ := retained entry member
  exact (closed prior oldMember).sameLiterals same

theorem DecisionHistory.append {s : State} {entries : List StoredClause} {entry : StoredClause}
    (history : DecisionHistory s entries)
    (birth : ∀ decision, s.forced ≤ decision → decision < s.assigned →
      s.reason s.trail[decision]! = 0 → PrefixUnitClosed s decision entry.lits) :
    DecisionHistory s (entries ++ [entry]) := by
  apply DecisionHistory.of_closed
  intro decision lower before reason old member
  rcases List.mem_append.mp member with oldMember | last
  · exact (history decision lower before reason).closed old oldMember
  · have equal : old = entry := by simpa only [List.mem_singleton] using last
    subst old
    exact birth decision lower before reason

/-- Real unit assignment appends a nondecision. Freshness protects all old
reason entries; the nonzero genuine clause ID excludes a new boundary. -/
theorem DecisionHistory.assign {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (id : Nat) (root : Bool)
    (nonzero : id ≠ 0) (space : s.assigned < s.trail.size)
    (reasonBound : Lit.var (s.db id) < s.reasons.size)
    (fresh : FreshVariable s (Lit.var (s.db id))) : DecisionHistory (s.assign id root) entries := by
  intro decision lower before zero
  have limit : decision < s.assigned + 1 := before
  have old : decision < s.assigned := by
    by_cases last : decision = s.assigned
    · subst decision
      rw [assign_trail_last space] at zero
      have actual : (s.assign id root).reason (Lit.negate (s.db id)) = id := by
        simpa only [State.reason, negate_var] using (assign_reason (root := root) reasonBound)
      exact False.elim (nonzero (actual.symm.trans zero))
    · omega
  have oldReason : s.reason s.trail[decision]! = 0 := by
    rw [assign_trail_prefix old] at zero
    change (s.reasons.set! (Lit.var (s.db id)) id)[s.trail[decision]!.var]! = 0 at zero
    rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm (fresh decision old))] at zero
    exact zero
  obtain ⟨savedPrefix, count, equal, closed⟩ := history decision lower old oldReason
  refine ⟨savedPrefix, count, ?_, closed⟩
  intro i bound
  exact (assign_trail_prefix (by omega : i < s.assigned)).trans (equal i bound)

/-- A real decision saves the genuinely quiescent old prefix. Older records
survive the fresh-variable append and the corresponding reason write. -/
theorem DecisionHistory.decide {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (closed : PropagationClosed s entries)
    (var : Nat) (fresh : FreshVariable s var) : DecisionHistory (s.decide var) entries := by
  intro decision lower before zero
  have limit : decision < s.assigned + 1 := before
  by_cases last : decision = s.assigned
  · subst decision
    exact ⟨s, rfl, fun _ before => decide_trail_prefix before, closed⟩
  · have old : decision < s.assigned := by omega
    have oldReason : s.reason s.trail[decision]! = 0 := by
      rw [decide_trail_prefix old] at zero
      change (s.reasons.set! var 0)[s.trail[decision]!.var]! = 0 at zero
      rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm (fresh decision old))] at zero
      exact zero
    obtain ⟨savedPrefix, count, equal, oldClosed⟩ := history decision lower old oldReason
    exact ⟨savedPrefix, count, fun i bound =>
      (decide_trail_prefix (by omega : i < s.assigned)).trans (equal i bound), oldClosed⟩

theorem DecisionHistory.restart {s : State} {entries : List StoredClause}
    (_history : DecisionHistory s entries) (bounds : TrailBounds s) : DecisionHistory s.restart entries := by
  apply DecisionHistory.no_decisions
  rw [restart_assigned bounds, restart_forced]
  exact Nat.le_refl _

theorem DecisionHistory.backjump {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (candidate : Nat) (cursor : s.processed ≤ s.assigned) :
    DecisionHistory (backjump s candidate) entries := by
  apply DecisionHistory.truncate history (by rw [backjump_assigned]; exact cursor) (by rw [backjump_forced]; exact Nat.le_refl _)
  · exact fun _ _ => by rw [backjump_trail]
  · intro i _
    simp only [State.reason, backjump_reasons, backjump_trail]

theorem DecisionHistory.addClause {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (lits : Array Lit) (original : Bool) :
    DecisionHistory (s.addClause lits original).1 entries :=
  DecisionHistory.frame history addClause_assigned addClause_forced addClause_trail addClause_reasons

end MicrosatLean.Verification.Analysis
