import MicrosatLean.Verification.Implementation.Native.Analysis.LearnedHistory
import MicrosatLean.Verification.Implementation.Native.Search.StateCertificate
import MicrosatLean.Verification.Implementation.Native.Search.Decision
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchSettled

namespace MicrosatLean.Verification.Implementation.Native.Search

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

/-- The propagation certificate's concrete completed-watch witnesses supply
the closure predicate needed when appending the next decision. Establishing
those witnesses through real traversal remains a separate phase obligation. -/
theorem StateCertificate.propagationClosed {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (units : ∀ entry ∈ original ++ learned, entry.lits.size = 1 →
      TrueBefore s s.assigned entry.lits[0]!)
    (settled : SettledWatches s (original ++ learned) heads s.assigned) :
    PropagationClosed s (original ++ learned) :=
  prefixUnitClosed_of_settled certificate.active (Nat.le_refl _) certificate.watches
    certificate.nonempty units settled

/-- The executable decision scan supplies freshness for the actual selected
variable. Only genuine propagation closure must be supplied by that phase. -/
theorem StateCertificate.decide_history {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned))
    (closed : PropagationClosed s (original ++ learned)) (cursor : Nat)
    (nonzero : nextDecision s cursor ≠ 0) :
    DecisionHistory (s.decide (nextDecision s cursor)) (original ++ learned) := by
  have unassigned : UnassignedVariable s (nextDecision s cursor) := by
    rcases nextDecision_zero_or_unassigned s cursor with zero | unassigned
    · exact False.elim (nonzero zero)
    · exact unassigned
  exact DecisionHistory.decide history closed _
    (freshVariable_of_unmarked certificate.active unassigned.1 unassigned.2)

/-- Base certificate data and maintained history discharge all clause-origin
and canonical-space inputs of the actual analyzer's numeric learned bound. -/
theorem StateCertificate.analyze_count_bound {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {conflict decision : Nat} {lits : Array Lit}
    (certificate : StateCertificate formula s original learned heads rank)
    (history : DecisionHistory s (original ++ learned))
    (entry : DecisionAnalysisEntry formula s conflict lits rank decision) :
    (CDCL.analyze s conflict).1.nLemmas ≤ 3 ^ s.nVars :=
  DecisionHistory.analyze_count_bound history entry certificate.database certificate.noClash
    certificate.learnedDistinct

end MicrosatLean.Verification.Implementation.Native.Search
