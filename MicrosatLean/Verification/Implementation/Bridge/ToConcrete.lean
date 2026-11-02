import MicrosatLean.Verification.Implementation.Bridge.Control

namespace MicrosatLean.Verification.Implementation.Bridge

/-!
The readable invariant entails the concrete invariant used by the reused
implementation proofs. Its witnesses are derived from present clauses, trail,
reasons and cursors; no reachability or future preservation is assumed here.
-/

theorem phase_concrete {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Search.Concrete.PhaseInvariant m (w.original ++ w.learned)
      w.heads := by
  have represented := certificate.representation
  have phaseFacts := certificate.control.phase
  cases phase : m.phase with
  | beginPropagation =>
    simp only [PhaseInv, phase] at phaseFacts
    rcases phaseFacts with ⟨evidence, cursor, old, root, literal, previous, settled⟩
    simp only [Search.Concrete.PhaseInvariant, phase]
    exact ⟨begin_concrete represented evidence, decisionCursor_concrete represented cursor,
      old, root, literal, previous,
      settledPrefix_concrete represented represented.cursors.2.1 settled⟩
  | nextLiteral =>
    simp only [PhaseInv, phase] at phaseFacts
    rcases phaseFacts with ⟨mode, literal, previous, settled⟩
    simp only [Search.Concrete.PhaseInvariant, phase]
    exact ⟨nextMode_concrete represented mode, literal, previous,
      settledPrefix_concrete represented represented.cursors.2.1 settled⟩
  | watch =>
    simp only [PhaseInv, phase] at phaseFacts
    rcases phaseFacts with ⟨mode, positive, literal, remaining, cursor, visited, settled⟩
    simp only [Search.Concrete.PhaseInvariant, phase]
    exact ⟨mode_concrete represented mode, positive, literal,
      ⟨remaining, watchCursor_concrete represented cursor,
        settledCursor_concrete represented visited,
        settledPrefix_concrete represented
          (Nat.le_trans (Nat.sub_le _ _) represented.cursors.2.1) settled⟩⟩
  | choose =>
    simp only [PhaseInv, phase] at phaseFacts
    rcases phaseFacts with ⟨complete, literal, previous, levels, six, settled⟩
    simp only [Search.Concrete.PhaseInvariant, phase]
    exact ⟨complete, literal, previous, levelCover_concrete represented levels, six,
      settledPrefix_concrete represented represented.cursors.2.1 settled⟩

theorem machineCertificate_concrete {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Search.Concrete.MachineCertificate formula m w.original
      w.learned w.heads (trailRank m.solver) := by
  refine ⟨stateCertificate_concrete certificate, ?_, history_concrete certificate,
    saved_concrete certificate, units_concrete certificate, ?_, phase_concrete certificate,
    certificate.control.oldCount⟩
  · have variables := certificate.variables
    rw [certificate.representation.variables] at variables
    omega
  · intro noLearning
    exact decisionCursor_concrete certificate.representation (certificate.control.cursor noLearning)

theorem concrete_of_certificate {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Search.Concrete.MachineInvariant formula m :=
  ⟨w.original, w.learned, w.heads,
    trailRank m.solver, machineCertificate_concrete certificate⟩

theorem concrete_of_inv {formula : Formula} {m : CDCL.Machine} (valid : Inv formula m) :
    Search.Concrete.MachineInvariant formula m := by
  obtain ⟨a, w, certificate⟩ := valid
  exact concrete_of_certificate certificate

end MicrosatLean.Verification.Implementation.Bridge
