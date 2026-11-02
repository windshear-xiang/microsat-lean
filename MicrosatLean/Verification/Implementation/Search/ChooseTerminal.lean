import MicrosatLean.Verification.Implementation.Search.ChooseDecision

namespace MicrosatLean.Verification.Implementation.Search

open Bridge
private abbrev NEntry := Native.Representation.StoredClause

/-- The SAT gate is derived at the completed prepared boundary: the actual
cursor covers every variable and saved phases agree with the current trail. -/
theorem choose_sat_gate {formula : Formula} {m : CDCL.Machine}
    {original learned : List NEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate (formulaView formula) m.solver original learned heads rank)
    (variables : formula.numVars ≤ m.solver.nVars)
    (closed : Native.Analysis.PropagationClosed m.solver (original ++ learned))
    {cursor : Nat} (covered : Native.Search.DecisionCursor m.solver cursor)
    (finished : CDCL.nextDecision m.solver cursor = 0) :
    Terminal formula (nativeState m.solver original learned) (.sat m.solver.phases m.solver.stats) := by
  obtain ⟨order, ordered⟩ := base.order
  have represented := native_rep base ordered
  refine ⟨?_, ?_, ?_, closed_from_native base closed⟩
  · change formula.numVars < m.solver.phases.size
    rw [base.arrays.phasesSize]
    omega
  · intro lit member
    have declared := (native_semantic base ordered).declaredTrail lit member
    have phaseBound : lit.1 < m.solver.phases.size := by
      rw [base.arrays.phasesSize]
      change 0 < lit.1 ∧ lit.1 ≤ m.solver.nVars at declared
      omega
    obtain ⟨entry, contained, equal⟩ := List.mem_map.mp member
    obtain ⟨i, before, value⟩ := List.mem_iff_getElem.mp contained
    have get : (nativeState m.solver original learned).trail[i]! = entry := by
      rw [getElem!_pos _ i before]
      exact value
    have saved := represented.phases i before
    rw [get, equal] at saved
    change Native.assignment m.solver.phases lit.1 = lit.2
    rw [Native.assignment_eq_getElem _ phaseBound]
    simpa only [getElem!_pos m.solver.phases lit.1 phaseBound] using saved
  · intro var lower upper
    exact native_assigned base ordered (covered.zero_all_assigned finished var lower upper)

end MicrosatLean.Verification.Implementation.Search
