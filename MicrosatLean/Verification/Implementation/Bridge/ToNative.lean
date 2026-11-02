import MicrosatLean.Verification.Implementation.Bridge.ToNativeControl

namespace MicrosatLean.Verification.Implementation.Bridge

/-!
The readable invariant entails the concrete invariant used by the reused
implementation proofs. Its witnesses are derived from present clauses, trail,
reasons and cursors; no reachability or future preservation is assumed here.
-/

theorem phase_toNative {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Native.Search.PhaseInvariant m (w.original ++ w.learned)
      w.heads := by
  have represented := certificate.representation
  have phaseFacts := certificate.control.phase
  cases phase : m.phase with
  | beginPropagation =>
    simp only [PhaseInv, phase] at phaseFacts
    rcases phaseFacts with ⟨evidence, cursor, old, root, literal, previous, settled⟩
    simp only [Native.Search.PhaseInvariant, phase]
    exact ⟨begin_toNative represented evidence, decisionCursor_toNative represented cursor,
      old, root, literal, previous,
      settledPrefix_toNative represented represented.cursors.2.1 settled⟩
  | nextLiteral =>
    simp only [PhaseInv, phase] at phaseFacts
    rcases phaseFacts with ⟨mode, literal, previous, settled⟩
    simp only [Native.Search.PhaseInvariant, phase]
    exact ⟨nextMode_toNative represented mode, literal, previous,
      settledPrefix_toNative represented represented.cursors.2.1 settled⟩
  | watch =>
    simp only [PhaseInv, phase] at phaseFacts
    rcases phaseFacts with ⟨mode, positive, literal, remaining, cursor, visited, settled⟩
    simp only [Native.Search.PhaseInvariant, phase]
    exact ⟨mode_toNative represented mode, positive, literal,
      ⟨remaining, watchCursor_toNative represented cursor,
        settledCursor_toNative represented visited,
        settledPrefix_toNative represented
          (Nat.le_trans (Nat.sub_le _ _) represented.cursors.2.1) settled⟩⟩
  | choose =>
    simp only [PhaseInv, phase] at phaseFacts
    rcases phaseFacts with ⟨complete, literal, previous, levels, six, settled⟩
    simp only [Native.Search.PhaseInvariant, phase]
    exact ⟨complete, literal, previous, levelCover_toNative represented levels, six,
      settledPrefix_toNative represented represented.cursors.2.1 settled⟩

theorem machineCertificate_toNative {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Native.Search.MachineCertificate formula m (w.original)
      (w.learned) w.heads (trailRank m.solver) := by
  refine ⟨stateCertificate_toNative certificate, ?_, history_toNative certificate,
    saved_toNative certificate, units_toNative certificate, ?_, phase_toNative certificate,
    certificate.control.oldCount⟩
  · have variables := certificate.variables
    rw [certificate.representation.variables] at variables
    omega
  · intro noLearning
    exact decisionCursor_toNative certificate.representation (certificate.control.cursor noLearning)

theorem native_of_certificate {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Native.Search.MachineInvariant formula m :=
  ⟨w.original, w.learned, w.heads,
    trailRank m.solver, machineCertificate_toNative certificate⟩

theorem native_of_inv {formula : Formula} {m : CDCL.Machine} (valid : Inv formula m) :
    Native.Search.MachineInvariant formula m := by
  obtain ⟨a, w, certificate⟩ := valid
  exact native_of_certificate certificate

end MicrosatLean.Verification.Implementation.Bridge
