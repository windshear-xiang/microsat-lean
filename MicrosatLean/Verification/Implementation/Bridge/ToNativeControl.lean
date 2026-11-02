import MicrosatLean.Verification.Implementation.Bridge.ToNativeCertificate

namespace MicrosatLean.Verification.Implementation.Bridge

theorem unitClosed_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {count : Nat} (bound : count ≤ m.solver.assigned)
    {lits : Array Lit} (closed : UnitClosed (prefixLiterals a count) (clauseView lits)) :
    Native.Analysis.PrefixUnitClosed m.solver count lits := by
  intro head member tails
  apply (trueBefore_iff represented bound head).mp
  apply closed (literalView head) (clauseView_mem.mpr ⟨head, member, rfl⟩)
  intro lit contained different
  obtain ⟨encoded, original, equal⟩ := clauseView_mem.mp contained
  have notHead : encoded ≠ head := by
    intro same
    subst encoded
    exact different equal.symm
  have falseEncoded := (falseBefore_iff represented bound encoded).mpr (tails encoded original notHead)
  simpa only [FalseBefore, equal] using falseEncoded

theorem history_toNative {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Native.Analysis.DecisionHistory m.solver
      (w.original ++ w.learned) := by
  apply Native.Analysis.DecisionHistory.of_closed
  intro decision lower before reason entry member
  obtain ⟨source, stored, rfl⟩ := native_entry_source member
  have represented := certificate.representation
  have closed := certificate.control.history decision
    (by simpa only [represented.rootSize] using lower)
    (by simpa only [represented.trailLength] using before)
    ((reason_none_iff represented before).mpr reason)
    source.view (stored_view_mem represented stored)
  exact unitClosed_toNative represented (Nat.le_of_lt before) closed

theorem settledWatch_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {count lit ref : Nat} (bound : count ≤ m.solver.assigned)
    (settled : SettledWatch a w count lit ref) :
    Native.Propagation.SettledWatch m.solver
      (w.original ++ w.learned) count lit ref := by
  intro entry member id
  obtain ⟨source, stored, rfl⟩ := native_entry_source member
  exact (trueBefore_iff represented bound (otherWatch source lit)).mp (settled source stored id)

theorem settledPrefix_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {count : Nat} (bound : count ≤ m.solver.assigned)
    (settled : SettledPrefix a w count) : Native.Propagation.SettledPrefix m.solver
      (w.original ++ w.learned) w.heads count := by
  intro lit falseLit ref watched
  apply settledWatch_toNative represented (Nat.le_refl _)
  simpa only [represented.trailLength] using
    settled lit ((falseBefore_iff represented bound lit).mpr falseLit) ref watched

theorem settledCursor_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {lit : Lit} {remaining : List Nat}
    (settled : SettledCursor a w lit remaining) : Native.Propagation.SettledCursor m.solver
      (w.original ++ w.learned) w.heads lit remaining := by
  intro ref watched visited
  apply settledWatch_toNative represented (Nat.le_refl _)
  simpa only [represented.trailLength] using settled ref watched visited

theorem saved_toNative {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Native.Analysis.DecisionWatchHistory m.solver
      (w.original ++ w.learned) w.heads := by
  intro decision lower before reason lit falseLit ref watched
  have represented := certificate.representation
  apply settledWatch_toNative represented (Nat.le_of_lt before)
  exact certificate.control.saved decision
    (by simpa only [represented.rootSize] using lower)
    (by simpa only [represented.trailLength] using before)
    ((reason_none_iff represented before).mpr reason)
    lit ((falseBefore_iff represented (Nat.le_of_lt before) lit).mpr falseLit) ref watched

theorem units_toNative {formula : Formula} {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (certificate : Certificate formula m a w) :
    Native.Search.UnitTruth m.solver
      (w.original ++ w.learned) := by
  intro entry member single
  obtain ⟨source, stored, rfl⟩ := native_entry_source member
  have positive : 0 < source.lits.size := by change source.lits.size = 1 at single; omega
  have firstMember : literalView source.lits[0]! ∈ source.view :=
    clauseView_mem.mpr ⟨source.lits[0]!, (by simpa only [getElem!_pos source.lits 0 positive]
      using (Array.getElem_mem positive)), rfl⟩
  have represented := certificate.representation
  apply (trueBefore_iff represented (Nat.le_refl _) source.lits[0]!).mp
  have truth := certificate.control.units source.view (stored_view_mem represented stored)
    (by simpa only [Native.Representation.StoredClause.view, clauseView_literals, List.length_map, Array.length_toList]
      using single) _ firstMember
  simpa only [TrueBefore, prefixLiterals, ← represented.trailLength, List.take_length,
    LogicalState.trueTrail] using truth

theorem assigned_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {var : Nat} (assigned : Assigned a var) :
    Native.Search.AssignedVariable m.solver var := by
  obtain ⟨lit, member, variableEq⟩ := assigned
  have inPrefix : lit ∈ prefixLiterals a a.trail.length := by
    simpa only [prefixLiterals, List.take_length, LogicalState.trueTrail] using member
  obtain ⟨i, active, equal⟩ := (prefix_mem_iff (Nat.le_refl _) lit).mp inPrefix
  have before : i < m.solver.assigned := by simpa only [represented.trailLength] using active
  have variableEq' : m.solver.trail[i]!.var = var :=
    (trail_var represented before).symm.trans ((congrArg Prod.fst equal).trans variableEq)
  have marked := (represented.active i before).1
  rcases Native.Representation.literal_encoding m.solver.trail[i]! with positive | negative
  · have equal : m.solver.trail[i]! = 2 * var := positive.trans (congrArg (2 * ·) variableEq')
    exact Or.inl (equal ▸ marked)
  · have equal : m.solver.trail[i]! = 2 * var + 1 :=
      negative.trans (congrArg (fun v => 2 * v + 1) variableEq')
    exact Or.inr (equal ▸ marked)

theorem decisionCursor_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {cursor : Nat} (valid : DecisionCursor a w cursor) :
    Native.Search.DecisionCursor m.solver cursor := by
  obtain ⟨position, _, value, assigned⟩ := valid
  exact ⟨w.order, position, order_toNative represented, value,
    fun i before _ => assigned_toNative represented (assigned i before)⟩

theorem levelCover_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) (cover : LevelCover a) : Native.Analysis.LevelCover m.solver := by
  intro i lower before
  obtain ⟨decision, root, bound, absent⟩ := cover i
    (by simpa only [represented.rootSize] using lower)
    (by simpa only [represented.trailLength] using before)
  exact ⟨decision, by simpa only [represented.rootSize] using root, bound,
    (reason_none_iff represented (Nat.lt_of_le_of_lt bound before)).mp absent⟩

theorem nonroot_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) (mode : NonrootMode m a) : Native.Search.NonrootPhase m.solver :=
  ⟨levelCover_toNative represented mode.2.1, mode.2.2,
    by simpa only [represented.rootSize, represented.trailLength] using mode.1⟩

theorem mode_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) (mode : PropagationMode m a) :
    Native.Search.PropagationMode m.solver m.root :=
  ⟨mode.1, fun nonroot => nonroot_toNative represented (mode.2 nonroot)⟩

theorem nextMode_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) (mode : NextMode m a) : Native.Search.NextMode m.solver m.root := by
  refine ⟨mode.1, ?_⟩
  intro nonroot
  rcases mode.2 nonroot with empty | active
  · exact Or.inl (by simpa only [represented.trailLength, represented.rootSize] using empty)
  · exact Or.inr (nonroot_toNative represented active)

theorem begin_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) (evidence : BeginEvidence m a) : Native.Search.BeginEvidence m.solver := by
  rcases evidence with initial | decision
  · exact Or.inl ⟨initial.1, initial.2.1, fun i before => (initial.2.2 i before).1,
      fun i before => (initial.2.2 i before).2⟩
  · exact Or.inr ⟨nonroot_toNative represented decision.1, decision.2⟩

theorem watchCursor_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {lit previous : Nat} {remaining : List Nat}
    (cursor : WatchCursor w lit previous remaining) :
    Native.Propagation.WatchCursor w.heads lit previous remaining := by
  rcases cursor with ⟨zero, same⟩ | ⟨visited, same⟩
  · subst previous
    exact .head remaining same.symm
  · have member : previous ∈ w.heads lit := by rw [same]; simp
    obtain ⟨entry, stored, id, _⟩ := represented.watches.references lit previous member
    have lower := (represented.layout.packed stored).startLower
    have nonzero : previous ≠ 0 := by
      intro zero
      simp only [zero, CDCL.watchClause, Nat.zero_div] at id
      omega
    exact .after previous visited remaining nonzero same

end MicrosatLean.Verification.Implementation.Bridge
