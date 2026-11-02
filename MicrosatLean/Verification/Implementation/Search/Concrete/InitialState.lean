import MicrosatLean.Verification.Implementation.Analysis.LearnedHistory
import MicrosatLean.Verification.Implementation.Search.Concrete.StateCertificate
import MicrosatLean.Verification.Implementation.Search.Concrete.Decision
import MicrosatLean.Verification.Implementation.Propagation.WatchSettled
import MicrosatLean.Verification.Implementation.Search.Concrete.DecisionCursor
import MicrosatLean.Verification.Implementation.Search.Concrete.WatchUnitState

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Analysis Initialization Propagation Std.Sat

/-- Successful actual initialization has no decision boundaries: every active
assignment has a genuine singleton reason with a nonzero arena identifier. -/
theorem initState_some_history {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (success : initState formula config = .ok (some s))
    (entries : List StoredClause) : DecisionHistory s entries := by
  have data := initState_some_analysisData wellFormed success
  intro decision _ before zero
  obtain ⟨_, packed, _, _, _⟩ := data.units decision before
  have nonzero := packed.startLower
  omega

end MicrosatLean.Verification.Implementation.Search.Concrete

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Propagation Analysis Initialization Std.Sat

/-- Every genuine singleton stored by the actual initializer has its true
literal on the active trail. The common packed layout aligns this result
with any independently obtained base certificate. -/
theorem initState_some_unitTruth {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (success : initState formula config = .ok (some s))
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate (formulaView formula) s original learned heads rank) :
    ∀ entry ∈ original ++ learned, entry.lits.size = 1 → TrueBefore s s.assigned entry.lits[0]! := by
  obtain ⟨actual, _, database, _, _, _, units⟩ := initState_some_watchReasons_units wellFormed success
  obtain ⟨sameOriginal, sameLearned⟩ := certificate.database.unique database
  subst original learned
  intro entry member unit
  apply certificate.marked
  exact units entry (by simpa only [List.append_nil] using member) unit

theorem initState_some_cursors {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (success : initState formula config = .ok (some s)) :
    s.processed = 0 ∧ s.forced = 0 := by
  have data := initState_some_analysisData wellFormed success
  exact ⟨data.processed, data.forced⟩

theorem initState_some_rootTrail {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (success : initState formula config = .ok (some s)) (root : Bool) :
    RootWatchTrail s root := by
  have data := initState_some_analysisData wellFormed success
  have valid := initState_some_representation wellFormed success
  intro _ i before
  rcases data.tags s.trail[i]! with zero | six
  · exact False.elim ((valid.active i before).2.1 zero)
  · exact six

theorem initState_some_nondecision {formula : Formula} (wellFormed : WellFormed formula)
    {config : Config} {s : State} (success : initState formula config = .ok (some s))
    (i : Nat) (before : i < s.assigned) : s.reason s.trail[i]! ≠ 0 := by
  obtain ⟨_, packed, _, _, _⟩ := (initState_some_analysisData wellFormed success).units i before
  have := packed.startLower
  omega

end MicrosatLean.Verification.Implementation.Search.Concrete
