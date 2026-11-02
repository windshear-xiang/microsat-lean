import MicrosatLean.Verification.Implementation.Native.Search.WatchRank

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Std.Sat

/-- The four actual control phases share one well-founded rank. Only watch
cursor evidence and reused decision-cursor declaration are phase-specific.
The finite learned bound is a consequence of preserved base certificates. -/
theorem step_rank_of_certificates {formula : Std.Sat.CNF Nat} (variables : Nat)
    {before after : Machine} {original learned : List StoredClause}
    {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula before.solver original learned heads rank)
    (afterCertificate : HasStateCertificate formula after.solver)
    (variablesEq : before.solver.nVars = variables)
    (decision : before.phase = .choose → ¬before.solver.nLemmas > before.oldLemmas →
      before.decision = 0 ∨ (1 ≤ before.decision ∧ before.decision ≤ before.solver.nVars))
    (watch : before.phase = .watch → ∃ remaining,
      LiteralBound before.solver.nVars before.currentLit ∧ before.solver.mark before.currentLit ≠ 0 ∧
      WatchCursor heads before.currentLit before.previousWatch remaining)
    (running : step before = .running after) :
    RankLT (controlRank (3 ^ variables) variables after)
      (controlRank (3 ^ variables) variables before) := by
  cases phase : before.phase with
  | beginPropagation => exact step_beginPropagation_rank _ _ phase running
  | nextLiteral => exact step_nextLiteral_rank _ _ phase running certificate.bounds variablesEq
  | choose =>
    apply step_choose_rank (3 ^ variables) variables phase running certificate
    · simpa only [variablesEq] using certificate.learnedCount_bound
    · exact variablesEq
    · exact decision phase
  | watch =>
    obtain ⟨remaining, literal, marked, cursor⟩ := watch phase
    exact step_watch_rank phase running certificate afterCertificate variables variablesEq literal marked remaining cursor

end MicrosatLean.Verification.Implementation.Native.Search
