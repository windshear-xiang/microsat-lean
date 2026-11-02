import MicrosatLean.Verification.Contracts
import MicrosatLean.Verification.Implementation.Bridge.Identity

namespace MicrosatLean.Verification.Implementation.Search

theorem rep_change_machine {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) (after : CDCL.Machine) (same : m.solver = after.solver) : Rep after a w :=
  Bridge.rep_frame_solver same represented

private theorem next_packed_frame {before after : CDCL.State} {entry : StoredClause}
    (packed : PackedClause before entry) (variables : after.nVars = before.nVars)
    (arena : after.arena = before.arena) : PackedClause after entry := by
  refine ⟨packed.startLower, ?_, ?_, ?_, ?_⟩
  · simpa only [arena] using packed.endBound
  · simpa only [CDCL.State.db, arena] using packed.literals
  · simpa only [CDCL.State.db, arena] using packed.terminator
  · simpa only [variables] using packed.wellFormed

private theorem next_layout_frame {before after : CDCL.State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom before start entries) (variables : after.nVars = before.nVars)
    (arena : after.arena = before.arena) : DatabaseFrom after start entries := by
  induction entries generalizing start with
  | nil => simpa only [DatabaseFrom, Native.Representation.DatabaseFrom, arena] using layout
  | cons entry rest ih =>
    exact ⟨layout.1, next_packed_frame layout.2.1 variables arena, ih layout.2.2⟩

private theorem next_watches_frame {before after : CDCL.State} {w : RepresentationWitness}
    (watches : WatchRepresentation before w) (arena : after.arena = before.arena)
    (heads : after.first = before.first) : WatchRepresentation after w := by
  refine ⟨?_, watches.references, watches.covered, watches.unique⟩
  intro lit
  simpa only [Native.Propagation.WatchLinks, arena, heads, CDCL.State.db] using watches.links lit

/-- Processing changes only a cursor, not the logical assignment. -/
theorem rep_set_processed {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (r : Rep m a w) (processed : Nat) (lower : m.solver.forced ≤ processed)
    (upper : processed ≤ m.solver.assigned) :
    Rep { m with solver := { m.solver with processed := processed } } a w :=
  ⟨r.variables, ⟨r.arrays.firstSize, r.arrays.marksSize, r.arrays.reasonsSize, r.arrays.phasesSize,
      r.arrays.trailSize, r.arrays.previousSize, r.arrays.nextSize⟩,
    r.reserved, next_layout_frame r.layout rfl rfl, r.fixed, r.count, r.original, r.learned,
    r.trailLength, r.rootSize, ⟨lower, upper, r.cursors.2.2⟩, r.trail, r.active,
    r.marks, r.phases, r.reasons, next_watches_frame r.watches rfl rfl, r.order⟩

/-- Committing root propagation changes the physical and logical boundary
together. Root soundness is established separately from root tags. -/
theorem rep_set_forced {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (r : Rep m a w) (forced : Nat) (lower : forced ≤ m.solver.processed) :
    Rep { m with solver := { m.solver with forced := forced } } { a with rootSize := forced } w :=
  ⟨r.variables, ⟨r.arrays.firstSize, r.arrays.marksSize, r.arrays.reasonsSize, r.arrays.phasesSize,
      r.arrays.trailSize, r.arrays.previousSize, r.arrays.nextSize⟩,
    r.reserved, next_layout_frame r.layout rfl rfl, r.fixed, r.count, r.original, r.learned,
    r.trailLength, rfl, ⟨lower, r.cursors.2⟩, r.trail, r.active,
    r.marks, r.phases, r.reasons, next_watches_frame r.watches rfl rfl, r.order⟩

theorem next_mode_pending {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (r : Rep m a w) (mode : NextMode m a)
    (pending : m.solver.processed < m.solver.assigned) : PropagationMode m a := by
  refine ⟨mode.1, ?_⟩
  intro nonroot
  rcases mode.2 nonroot with empty | active
  · have forced := r.cursors.1
    rw [r.trailLength, r.rootSize] at empty
    omega
  · exact active

theorem root_commit_sound {formula : Formula} {m : CDCL.Machine}
    {a : LogicalState} {w : RepresentationWitness} (certificate : Certificate formula m a w)
    (mode : NextMode m a) (root : m.root = true)
    (complete : m.solver.processed = m.solver.assigned) :
    ∀ lit ∈ prefixLiterals a m.solver.processed, ∀ valuation,
      Std.Sat.CNF.Sat valuation (formulaView formula) → valuation lit.1 = lit.2 := by
  intro lit member valuation model
  have bound : m.solver.processed ≤ a.trail.length := by
    rw [certificate.representation.trailLength, complete]
    exact Nat.le_refl _
  obtain ⟨i, before, equal⟩ := (Bridge.prefix_mem_iff bound lit).mp member
  have active : i < m.solver.assigned := by omega
  have marked := mode.1 root i active
  have truth := certificate.control.rootTags i
    (by simpa only [certificate.representation.trailLength] using active) marked valuation model
  simpa only [equal] using truth

end MicrosatLean.Verification.Implementation.Search
