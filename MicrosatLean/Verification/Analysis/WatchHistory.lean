import MicrosatLean.Verification.Analysis.RootTags
import MicrosatLean.Verification.Propagation.WatchSettlement

namespace MicrosatLean.Verification.Analysis

open CDCL Representation Propagation

/-- The watch facts saved before every actual decision include truth below
that same boundary. The weaker active-trail witness alone loses the level
information needed by a later backjump. -/
def DecisionWatchHistory (s : State) (entries : List StoredClause)
    (heads : Nat → List Nat) : Prop :=
  ∀ decision, s.forced ≤ decision → decision < s.assigned →
    s.reason s.trail[decision]! = 0 → SettledWatches s entries heads decision

theorem settledWatches_transfer {before after : State} {entries : List StoredClause}
    {heads : Nat → List Nat} {count : Nat} (settled : SettledWatches before entries heads count)
    (equal : PrefixLiterals before after count) : SettledWatches after entries heads count := by
  intro lit falseLit ref watched entry member id
  have oldFalse := FalseBefore.transfer (fun i bound => (equal i bound).symm) falseLit
  exact FalseBefore.transfer equal (settled lit oldFalse ref watched entry member id)

theorem DecisionWatchHistory.no_decisions {s : State} {entries : List StoredClause} {heads : Nat → List Nat}
    (root : s.assigned ≤ s.forced) : DecisionWatchHistory s entries heads := by
  intro decision lower before
  omega

theorem DecisionWatchHistory.truncate {before after : State} {entries : List StoredClause}
    {heads : Nat → List Nat} (history : DecisionWatchHistory before entries heads)
    (cursor : after.assigned ≤ before.assigned) (root : before.forced ≤ after.forced)
    (equal : PrefixLiterals before after after.assigned)
    (decisions : ∀ i, i < after.assigned → after.reason after.trail[i]! = 0 →
      before.reason before.trail[i]! = 0) : DecisionWatchHistory after entries heads := by
  intro decision lower before zero
  have old := history decision (by omega) (by omega) (decisions decision before zero)
  exact settledWatches_transfer old (fun i bound => equal i (by omega))

theorem DecisionWatchHistory.frame {before after : State} {entries : List StoredClause}
    {heads : Nat → List Nat} (history : DecisionWatchHistory before entries heads)
    (cursor : after.assigned = before.assigned) (root : after.forced = before.forced)
    (trail : after.trail = before.trail) (reasons : after.reasons = before.reasons) :
    DecisionWatchHistory after entries heads := by
  apply DecisionWatchHistory.truncate history (Nat.le_of_eq cursor) (Nat.le_of_eq root.symm)
  · exact fun i _ => congrArg (fun words : Array Lit => words[i]!) trail
  · intro i _ zero
    simpa only [State.reason, trail, reasons] using zero

theorem DecisionWatchHistory.assign {s : State} {entries : List StoredClause} {heads : Nat → List Nat}
    (history : DecisionWatchHistory s entries heads) (id : Nat) (root : Bool)
    (nonzero : id ≠ 0) (space : s.assigned < s.trail.size)
    (reasonBound : Lit.var (s.db id) < s.reasons.size) (fresh : FreshVariable s (Lit.var (s.db id))) :
    DecisionWatchHistory (s.assign id root) entries heads := by
  intro decision lower before zero
  have limit : decision < s.assigned + 1 := before
  have old : decision < s.assigned := by
    by_cases last : decision = s.assigned
    · subst decision
      rw [assign_trail_last space] at zero
      have actual : (s.assign id root).reason (Lit.negate (s.db id)) = id := by
        simpa only [State.reason, negate_var] using assign_reason (root := root) reasonBound
      exact False.elim (nonzero (actual.symm.trans zero))
    · omega
  have prior : s.reason s.trail[decision]! = 0 := by
    rw [assign_trail_prefix old, assign_reason_prefix fresh old] at zero
    exact zero
  exact settledWatches_transfer (history decision lower old prior) (fun i bound => assign_trail_prefix (by omega))

/-- A new decision records the completed watch witnesses at the genuine old
quiescent boundary. Earlier decision records retain exactly their prefixes. -/
theorem DecisionWatchHistory.decide {s : State} {entries : List StoredClause} {heads : Nat → List Nat}
    (history : DecisionWatchHistory s entries heads) (settled : SettledWatches s entries heads s.assigned)
    (var : Nat) (fresh : FreshVariable s var) : DecisionWatchHistory (s.decide var) entries heads := by
  intro decision lower before zero
  have limit : decision < s.assigned + 1 := before
  by_cases last : decision = s.assigned
  · subst decision
    exact settledWatches_transfer settled (fun _ bound => decide_trail_prefix bound)
  · have old : decision < s.assigned := by omega
    have prior : s.reason s.trail[decision]! = 0 := by
      rw [decide_trail_prefix old, decide_reason_prefix fresh old] at zero
      exact zero
    exact settledWatches_transfer (history decision lower old prior) (fun i bound => decide_trail_prefix (by omega))

theorem DecisionWatchHistory.restart {s : State} {entries : List StoredClause} {heads : Nat → List Nat}
    (_history : DecisionWatchHistory s entries heads) (bounds : TrailBounds s) :
    DecisionWatchHistory s.restart entries heads := by
  apply DecisionWatchHistory.no_decisions
  rw [restart_assigned bounds, restart_forced]
  exact Nat.le_refl _

end MicrosatLean.Verification.Analysis
