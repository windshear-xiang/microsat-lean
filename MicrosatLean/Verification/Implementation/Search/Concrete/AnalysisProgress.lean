import MicrosatLean.Verification.Implementation.Analysis.Resolution
import MicrosatLean.Verification.Implementation.Analysis.LearnedFrame
import MicrosatLean.Verification.Implementation.Analysis.Backjump
import MicrosatLean.Verification.Implementation.Representation.Database
import MicrosatLean.Verification.Implementation.Search.Concrete.Measure

namespace MicrosatLean.Verification.Implementation.Search.Concrete

open CDCL Representation Analysis

/-!
Counter projections of the actual complete conflict analyzer. These hold on
all states, so the numeric progress rule below does not assume its own count
increase. The finite clause bound still requires reachable-state freshness.
-/

private theorem markClause_nLemmas (s : State) (start : Nat) :
    (markClause s start).nLemmas = s.nLemmas := by
  simpa only using congrArg State.nLemmas (markClause_frame s start).restore

private theorem markClause_maxLemmas (s : State) (start : Nat) :
    (markClause s start).maxLemmas = s.maxLemmas := by
  simpa only using congrArg State.maxLemmas (markClause_frame s start).restore

private theorem markClause_nVars (s : State) (start : Nat) :
    (markClause s start).nVars = s.nVars := by
  simpa only using congrArg State.nVars (markClause_frame s start).restore

private theorem backjump_nLemmas (s : State) (candidate : Nat) :
    (backjump s candidate).nLemmas = s.nLemmas := by
  simpa only using congrArg State.nLemmas (backjump_frame s candidate).restore

private theorem backjump_maxLemmas (s : State) (candidate : Nat) :
    (backjump s candidate).maxLemmas = s.maxLemmas := by
  simpa only using congrArg State.maxLemmas (backjump_frame s candidate).restore

private theorem addClause_maxLemmas (s : State) (lits : Array Lit) (original : Bool) :
    (s.addClause lits original).1.maxLemmas = s.maxLemmas := by
  by_cases watches : 1 < lits.size <;> cases original <;>
    simp [State.addClause, State.addWatch, watches]

theorem analyze_nLemmas (s : State) (conflict : Nat) :
    (analyze s conflict).1.nLemmas = s.nLemmas + 1 := by
  simp only [analyze, Id.run, pure, addClause_learnedCount, backjump_nLemmas,
    LearnedFrame.nLemmas (buildLearned_frame ..),
    ResolutionFrame.nLemmas (resolveToUIP_frame ..), markClause_nLemmas]
  rfl

theorem analyze_maxLemmas (s : State) (conflict : Nat) :
    (analyze s conflict).1.maxLemmas = s.maxLemmas := by
  simp only [analyze, Id.run, pure, addClause_maxLemmas, backjump_maxLemmas,
    LearnedFrame.maxLemmas (buildLearned_frame ..),
    ResolutionFrame.maxLemmas (resolveToUIP_frame ..), markClause_maxLemmas]

theorem analyze_nVars (s : State) (conflict : Nat) :
    (analyze s conflict).1.nVars = s.nVars := by
  simp only [analyze, Id.run, pure, addClause_nVars, backjump_nVars,
    LearnedFrame.nVars (buildLearned_frame ..),
    ResolutionFrame.nVars (resolveToUIP_frame ..), markClause_nVars]

end MicrosatLean.Verification.Implementation.Search.Concrete
