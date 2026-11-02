import MicrosatLean.Verification.Implementation.Native.Search.AnalysisState
import MicrosatLean.Verification.Implementation.Native.Search.WatchUnitState
import MicrosatLean.Verification.Implementation.Native.Analysis.AssertionBoundary

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Std.Sat

/-- Root and nonroot invocations carry their concrete trail conditions. The
Boolean mode can change only at an asserting singleton learned clause. -/
structure PropagationMode (s : State) (root : Bool) : Prop where
  roots : RootWatchTrail s root
  nonroot : root = false → NonrootPhase s

theorem RootWatchTrail.assign {s : State} {root : Bool} (roots : RootWatchTrail s root)
    (id : Nat) (space : s.assigned < s.trail.size)
    (fresh : FreshVariable s (Lit.var (s.db id)))
    (bound : Lit.negate (s.db id) < s.marks.size) : RootWatchTrail (s.assign id root) root := by
  intro isRoot i before
  have upper : i < s.assigned + 1 := before
  by_cases last : i = s.assigned
  · subst i
    rw [assign_trail_last space]
    have newMark : (s.assign id root).mark (Lit.negate (s.db id)) = if root then 6 else 1 :=
      Array.getElem!_set!_self _ _ _ bound
    simpa only [isRoot, ite_true] using newMark
  · have earlier : i < s.assigned := by omega
    rw [assign_trail_prefix earlier, assign_mark_other (fresh.ne_literal earlier (negate_var _))]
    exact roots isRoot i earlier

theorem PropagationMode.assign {s : State} {root : Bool} (mode : PropagationMode s root)
    (id : Nat) (space : s.assigned < s.trail.size)
    (fresh : FreshVariable s (Lit.var (s.db id)))
    (bound : Lit.negate (s.db id) < s.marks.size) : PropagationMode (s.assign id root) root := by
  refine ⟨RootWatchTrail.assign mode.roots id space fresh bound, ?_⟩
  intro nonroot
  subst root
  exact (mode.nonroot rfl).assign id space bound fresh

theorem PropagationMode.restoreWatchArrays {s : State} {root : Bool}
    (mode : PropagationMode s root) (arena first : Array Nat) :
    PropagationMode (CDCL.restoreWatchArrays s arena first) root := by
  refine ⟨mode.roots, ?_⟩
  intro nonroot
  have phase := mode.nonroot nonroot
  exact ⟨phase.levels, phase.caches, phase.nonroot⟩

/-- Actual singleton learning erases all nonroot levels before assigning its
new root literal. Every other learned clause returns to a genuine nonroot
level, with transient cache tags cleared by the actual minimization scan. -/
theorem PropagationMode.analyze_assign {formula : Std.Sat.CNF Nat} {s : State}
    {conflict decision : Nat} {lits : Array Lit} {rank : Lit → Nat}
    (phase : NonrootPhase s) (entry : AnalysisTransitionEntry formula s conflict lits rank decision) :
    let result := CDCL.analyze s conflict
    let root := result.1.db (result.2 + 1) == 0
    PropagationMode (result.1.assign result.2 root) root := by
  dsimp only
  let result := CDCL.analyze s conflict
  let root := result.1.db (result.2 + 1) == 0
  have ready := entry.ready
  have first : result.1.db result.2 = (analysisLearned s conflict)[0]! := by
    simpa only [result, Nat.add_zero] using ready.packed.literals 0 ready.nonempty
  have member : result.1.db result.2 ∈ analysisLearned s conflict := by
    rw [first]
    simpa only [getElem!_pos (analysisLearned s conflict) 0 ready.nonempty] using Array.getElem_mem ready.nonempty
  have literal := ready.packed.wellFormed _ member
  have fresh := freshVariable_of_unmarked_literal ready.active ready.head ready.opposite
  have room := assigned_lt_of_fresh ready.active ready.distinct fresh literal.1 literal.2
  have space : result.1.assigned < result.1.trail.size := by
    change (CDCL.analyze s conflict).1.assigned < (CDCL.analyze s conflict).1.trail.size
    rw [ready.arrays.trailSize]
    omega
  refine ⟨?_, ?_⟩
  · intro rootTrue
    have unit := (analyze_root_iff_unit entry).mp rootTrue
    have onlyRoots := analyze_unit_root_prefix phase.levels entry.decisionEntry unit
    have roots : RootWatchTrail result.1 root := by
      intro _ i before
      exact analyze_rootPrefix entry.decisionEntry i (by simpa only [result, ← onlyRoots] using before)
    exact RootWatchTrail.assign roots result.2 space fresh (ready.arrays.literal_index literal.negate).1 rootTrue
  · intro rootFalse
    change root = false at rootFalse
    have notUnit : (analysisLearned s conflict).size ≠ 1 := by
      intro unit
      have isRoot := (analyze_root_iff_unit entry).mpr unit
      change root = true at isRoot
      rw [rootFalse] at isRoot
      cases isRoot
    have many : 1 < (analysisLearned s conflict).size := by have := ready.nonempty; omega
    change NonrootPhase (result.1.assign result.2 root)
    rw [rootFalse]
    exact phase.analyze_assign entry many

end MicrosatLean.Verification.Implementation.Native.Search
