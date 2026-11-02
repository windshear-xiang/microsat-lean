import MicrosatLean.Verification.Implementation.Bridge.Semantics
import MicrosatLean.Verification.Implementation.Bridge.TrailData
import MicrosatLean.Verification.Implementation.Bridge.Identity

namespace MicrosatLean.Verification.Implementation.Bridge

theorem unitClosed_of_concrete {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {count : Nat} (bound : count ≤ m.solver.assigned)
    {lits : Array Lit} (closed : Analysis.PrefixUnitClosed m.solver count lits) :
    UnitClosed (prefixLiterals a count) (clauseView lits) := by
  intro head member tails
  obtain ⟨encoded, contained, equal⟩ := clauseView_mem.mp member
  rw [← equal]
  apply (trueBefore_iff represented bound encoded).mpr
  apply closed encoded contained
  intro tail tailMember different
  apply (falseBefore_iff represented bound tail).mp
  exact tails (literalView tail) (clauseView_mem.mpr ⟨tail, tailMember, rfl⟩)
    (fun same => different (literalView_injective (same.trans equal.symm)))

theorem view_levelCover {formula : Formula} {m : CDCL.Machine}
    {original learned : List Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    {order : List Nat} (ordered : Representation.MTFOrder m.solver order)
    (levels : Analysis.LevelCover m.solver) :
    LevelCover (logicalView m.solver original learned) := by
  have represented := view_rep base ordered
  intro i lower before
  have active : i < m.solver.assigned := by simpa [logicalView] using before
  obtain ⟨decision, roots, earlier, zero⟩ := levels i lower active
  exact ⟨decision, roots, earlier, (reason_none_iff represented (by omega)).mpr zero⟩

theorem view_nonroot {formula : Formula} {m : CDCL.Machine}
    {original learned : List Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    {order : List Nat} (ordered : Representation.MTFOrder m.solver order)
    (phase : Search.Concrete.NonrootPhase m.solver) :
    NonrootMode m (logicalView m.solver original learned) :=
  ⟨by simpa [logicalView] using phase.nonroot, view_levelCover base ordered phase.levels, phase.caches⟩

theorem view_assigned {formula : Formula} {m : CDCL.Machine}
    {original learned : List Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    {order : List Nat} (ordered : Representation.MTFOrder m.solver order)
    {var : Nat} (assigned : Search.Concrete.AssignedVariable m.solver var) :
    Assigned (logicalView m.solver original learned) var := by
  have represented := view_rep base ordered
  have fromMark (lit : Lit) (marked : m.solver.mark lit ≠ 0) (sameVar : lit.var = var) :
      Assigned (logicalView m.solver original learned) var := by
    obtain ⟨i, before, value⟩ := base.marked lit marked
    have active : i < (logicalView m.solver original learned).trail.length := by
      simpa [logicalView] using before
    refine ⟨(logicalView m.solver original learned).trail[i]!.literal, ?_, ?_⟩
    · apply List.mem_map.mpr
      exact ⟨(logicalView m.solver original learned).trail[i]'active,
        List.getElem_mem active,
        by simp only [getElem!_pos (logicalView m.solver original learned).trail i active]⟩
    · rw [trail_var represented before, value, sameVar]
  rcases assigned with positive | negative
  · exact fromMark (2 * var) positive (by simp [Lit.var])
  · exact fromMark (2 * var + 1) negative (by simp [Lit.var, Nat.add_div])

theorem view_decisionCursor {formula : Formula} {m : CDCL.Machine}
    {original learned : List Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    {order : List Nat} (ordered : Representation.MTFOrder m.solver order)
    {cursor : Nat} (valid : Search.Concrete.DecisionCursor m.solver cursor) :
    DecisionCursor (logicalView m.solver original learned)
      (representationWitness original learned heads order) cursor := by
  obtain ⟨other, start, otherOrder, value, earlierAssigned⟩ := valid
  have same : other = order := rep_order_unique (view_rep base otherOrder) (view_rep base ordered)
  subst other
  refine ⟨min start order.length, Nat.min_le_right _ _, ?_, ?_⟩
  · change cursor = order.getD (min start order.length) 0
    rw [value]
    by_cases within : start ≤ order.length
    · rw [Nat.min_eq_left within]
    · have beyond : order.length ≤ start := by omega
      simp [Nat.min_eq_right beyond, List.getD_eq_getElem?_getD, List.getElem?_eq_none beyond]
  · intro i before
    have bounds : i < start ∧ i < order.length := Nat.lt_min.mp before
    exact view_assigned base ordered (earlierAssigned i bounds.1 bounds.2)

theorem view_settledWatch {formula : Formula} {m : CDCL.Machine}
    {original learned : List Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    {order : List Nat} (ordered : Representation.MTFOrder m.solver order)
    {count lit ref : Nat} (bound : count ≤ m.solver.assigned)
    (settled : Propagation.SettledWatch m.solver (original ++ learned) count lit ref) :
    SettledWatch (logicalView m.solver original learned) (representationWitness original learned heads order)
      count lit ref := by
  intro entry member id
  have mapped : (representationWitness original learned heads order).entries =
      (original ++ learned) := by simp [representationWitness, RepresentationWitness.entries]
  rw [mapped] at member
  exact (trueBefore_iff (view_rep base ordered) bound _).mpr (settled entry member id)

theorem view_settledPrefix {formula : Formula} {m : CDCL.Machine}
    {original learned : List Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (base : Search.Concrete.StateCertificate (formulaView formula) m.solver original learned heads rank)
    {order : List Nat} (ordered : Representation.MTFOrder m.solver order)
    {count : Nat} (bound : count ≤ m.solver.assigned)
    (settled : Propagation.SettledPrefix m.solver (original ++ learned) heads count) :
    SettledPrefix (logicalView m.solver original learned) (representationWitness original learned heads order) count := by
  intro lit falseLit ref member
  have visited := settled lit ((falseBefore_iff (view_rep base ordered) bound lit).mp falseLit) ref member
  simpa only [logicalView, trailView_length] using
    view_settledWatch base ordered (Nat.le_refl _) visited

theorem cursor_of_concrete {w : RepresentationWitness} {lit previous : Nat} {remaining : List Nat}
    (cursor : Propagation.WatchCursor w.heads lit previous remaining) :
    WatchCursor w lit previous remaining := by
  cases cursor with
  | head rest same => exact Or.inl ⟨rfl, same.symm⟩
  | after previous initial rest _ same => exact Or.inr ⟨initial, same⟩

theorem view_control {formula : Formula} {m : CDCL.Machine}
    {original learned : List Representation.StoredClause} {heads : Lit → List Nat}
    {rank : Lit → Nat}
    (certificate : Search.Concrete.MachineCertificate formula m original learned heads rank)
    {order : List Nat} (ordered : Representation.MTFOrder m.solver order) :
    ControlInv (formulaView formula) m (logicalView m.solver original learned)
      (representationWitness original learned heads order) := by
  let a := logicalView m.solver original learned
  let w := representationWitness original learned heads order
  have base := certificate.base
  have represented := view_rep base ordered
  refine ⟨?_, ?_, ?_, ?_, certificate.oldCount, ?_, ?_, base.rootPrefix, ?_⟩
  · intro i roots before none clause member
    have active : i < m.solver.assigned := by simpa [logicalView] using before
    have zero := (reason_none_iff represented active).mp none
    rw [logicalView_database] at member
    obtain ⟨entry, stored, rfl⟩ := List.mem_map.mp member
    exact unitClosed_of_concrete represented (Nat.le_of_lt active)
      ((certificate.history i roots active zero).closed entry stored)
  · intro i roots before none lit falseLit ref member
    have active : i < m.solver.assigned := by simpa [logicalView] using before
    have zero := (reason_none_iff represented active).mp none
    apply view_settledWatch base ordered (Nat.le_of_lt active)
    exact certificate.saved i roots active zero lit
      ((falseBefore_iff represented (Nat.le_of_lt active) lit).mp falseLit) ref member
  · intro clause member single lit contains
    rw [logicalView_database] at member
    obtain ⟨entry, stored, rfl⟩ := List.mem_map.mp member
    have width : entry.lits.size = 1 := by
      simpa [Representation.StoredClause.view, clauseView_literals,
        clauseView_literals] using single
    obtain ⟨encoded, inside, view⟩ := clauseView_mem.mp contains
    have equal : encoded = entry.lits[0]! := by
      obtain ⟨i, before, value⟩ := Array.mem_iff_getElem.mp inside
      have first : i = 0 := by omega
      subst i
      simpa only [getElem!_pos entry.lits 0 (by omega)] using value.symm
    rw [← view, equal]
    have truth := (trueBefore_iff represented (Nat.le_refl _) _).mpr
      (certificate.units entry stored width)
    change literalView entry.lits[0]! ∈ prefixLiterals a m.solver.assigned at truth
    rw [← represented.trailLength] at truth
    change literalView entry.lits[0]! ∈ prefixLiterals
      (logicalView m.solver original learned) (logicalView m.solver original learned).trail.length at truth
    simpa only [prefixLiterals, List.take_length, LogicalState.trueTrail, TrueIn,
      literalView, literalView] using truth
  · intro noLearning
    exact view_decisionCursor base ordered (certificate.cursor noLearning)
  · intro i before
    rcases base.tags m.solver.trail[i]! ⟨i, before, rfl⟩ with zero | one | two | five | six
    · exact False.elim ((base.active i before).2.1 zero)
    · exact Or.inl one
    · exact Or.inr (Or.inl two)
    · exact Or.inr (Or.inr (Or.inl five))
    · exact Or.inr (Or.inr (Or.inr six))
  · intro i before six valuation model
    have active : i < m.solver.assigned := by simpa [logicalView] using before
    rw [represented.trail i active]
    exact view_true_of_falsifies valuation _ (base.roots _ ⟨i, active, rfl⟩ six valuation model)
  · cases phase : m.phase with
    | beginPropagation =>
      have facts := certificate.phase
      rw [Search.Concrete.PhaseInvariant, phase] at facts
      rw [PhaseInv, phase]
      change BeginEvidence m a ∧ DecisionCursor a w m.decision ∧ _
      refine ⟨?_, view_decisionCursor base ordered facts.2.1, facts.2.2.1, facts.2.2.2.1,
        facts.2.2.2.2.1, facts.2.2.2.2.2.1,
        view_settledPrefix base ordered base.bounds.processedAssigned facts.2.2.2.2.2.2⟩
      rcases facts.1 with ⟨processed, forced, roots, reasons⟩ | ⟨nonroot, pending, decision⟩
      · exact Or.inl ⟨processed, forced, fun i before => ⟨roots i before, reasons i before⟩⟩
      · exact Or.inr ⟨view_nonroot base ordered nonroot, pending, decision⟩
    | nextLiteral =>
      have facts := certificate.phase
      rw [Search.Concrete.PhaseInvariant, phase] at facts
      rw [PhaseInv, phase]
      change NextMode m a ∧ _
      refine ⟨⟨facts.1.roots, ?_⟩, facts.2.1, facts.2.2.1,
        view_settledPrefix base ordered base.bounds.processedAssigned facts.2.2.2⟩
      intro nonroot
      rcases facts.1.nonroot nonroot with empty | active
      · exact Or.inl (by simpa [a, logicalView] using empty)
      · exact Or.inr (view_nonroot base ordered active)
    | choose =>
      have facts := certificate.phase
      rw [Search.Concrete.PhaseInvariant, phase] at facts
      rw [PhaseInv, phase]
      change m.solver.processed = m.solver.assigned ∧ _
      exact ⟨facts.1, facts.2.1, facts.2.2.1, view_levelCover base ordered facts.2.2.2.1,
        facts.2.2.2.2.1, view_settledPrefix base ordered base.bounds.processedAssigned facts.2.2.2.2.2⟩
    | watch =>
      have facts := certificate.phase
      rw [Search.Concrete.PhaseInvariant, phase] at facts
      rw [PhaseInv, phase]
      change PropagationMode m a ∧ _
      refine ⟨⟨facts.mode.roots, fun nonroot => view_nonroot base ordered (facts.mode.nonroot nonroot)⟩,
        facts.positive, facts.literal, ?_⟩
      obtain ⟨remaining, cursor, visited, completedPrefix⟩ := facts.cursor
      refine ⟨remaining, ?_, ?_, view_settledPrefix base ordered
        (Nat.le_trans (Nat.sub_le _ _) base.bounds.processedAssigned) completedPrefix⟩
      · exact cursor_of_concrete cursor
      · intro ref member unseen
        simpa only [logicalView, trailView_length] using
          view_settledWatch base ordered (Nat.le_refl _) (visited ref member unseen)

end MicrosatLean.Verification.Implementation.Bridge
