import MicrosatLean.Verification.Implementation.Native.Analysis.Tags
import MicrosatLean.Verification.Implementation.Native.Analysis.LearnedFrame
import MicrosatLean.Verification.Implementation.Native.Analysis.Backjump
import MicrosatLean.Verification.Implementation.Native.Representation.DatabaseUpdates
import MicrosatLean.Verification.Implementation.Native.Representation.Meaning

namespace MicrosatLean.Verification.Implementation.Native.Analysis

open CDCL Representation
open Std.Sat

/-!
Composition of the actual executable analyzer. These proof-only stage names
expose its real intermediate states and learned array without changing the
implementation. Incoming reason-graph and trail/root invariants are concrete
reachability obligations; learned-clause entailment is proved here rather than
assumed at any outer analysis entry.
-/

def analysisStart (s : State) : State :=
  { s with res := s.res + 1, stats := { s.stats with conflicts := s.stats.conflicts + 1 } }

def analysisMarked (s : State) (conflict : Nat) : State := markClause (analysisStart s) conflict

def analysisResolved (s : State) (conflict : Nat) : State := resolveToUIP (analysisMarked s conflict)

def analysisBuilt (s : State) (conflict : Nat) : State × Array Lit × Nat :=
  let resolved := analysisResolved s conflict
  buildLearned resolved resolved.assigned

def analysisLearned (s : State) (conflict : Nat) : Array Lit := (analysisBuilt s conflict).2.1

def analysisBeforeStore (s : State) (conflict : Nat) : State :=
  let resolved := analysisResolved s conflict
  let built := analysisBuilt s conflict
  let averaged := { built.1 with
    fast := built.1.fast - (built.1.fast >>> 5) + (built.2.2 <<< 15)
    slow := built.1.slow - (built.1.slow >>> 15) + (built.2.2 <<< 5) }
  backjump averaged resolved.assigned

theorem analyze_eq_addClause (s : State) (conflict : Nat) :
    analyze s conflict = (analysisBeforeStore s conflict).addClause (analysisLearned s conflict) false := by
  cases built : analysisBuilt s conflict with
  | mk next rest =>
    cases rest with
    | mk learned lbd =>
      have concrete := built
      unfold analysisBuilt analysisResolved analysisMarked analysisStart at concrete
      simp only [analysisBeforeStore, analysisLearned, built]
      simp only [analyze, Id.run, pure, concrete]
      rfl

private theorem analysisResolved_projection {α : Type} (project : State → α) (s : State) (conflict : Nat)
    (mark : ∀ before start, project (markClause before start) = project before)
    (resolve : ∀ before, project (resolveToUIP before) = project before)
    (start : project (analysisStart s) = project s) :
    project (analysisResolved s conflict) = project s :=
  (resolve _).trans ((mark _ _).trans start)

theorem analysisBeforeStore_arena (s : State) (conflict : Nat) :
    (analysisBeforeStore s conflict).arena = s.arena := by
  simp only [analysisBeforeStore, backjump_arena]
  have built := congrArg State.arena (buildLearned_frame (analysisResolved s conflict)
    (analysisResolved s conflict).assigned).restore
  have resolved := analysisResolved_projection State.arena s conflict markClause_arena
    (fun before => (resolveToUIP_frame before).reasonStorage (ReasonStorage.refl before) |>.arena) rfl
  exact built.trans resolved

theorem analysisBeforeStore_nVars (s : State) (conflict : Nat) :
    (analysisBeforeStore s conflict).nVars = s.nVars := by
  simp only [analysisBeforeStore, backjump_nVars]
  have built := (buildLearned_frame (analysisResolved s conflict) (analysisResolved s conflict).assigned).nVars
  have resolved := analysisResolved_projection State.nVars s conflict
    (fun before start => by simpa only using congrArg State.nVars (markClause_frame before start).restore)
    (fun before => (resolveToUIP_frame before).nVars) rfl
  exact built.trans resolved

theorem analysisBeforeStore_fixed (s : State) (conflict : Nat) :
    (analysisBeforeStore s conflict).fixed = s.fixed := by
  simp only [analysisBeforeStore, backjump_fixed]
  have built := congrArg State.fixed (buildLearned_frame (analysisResolved s conflict)
    (analysisResolved s conflict).assigned).restore
  have resolved := analysisResolved_projection State.fixed s conflict
    (fun before start => by simpa only using congrArg State.fixed (markClause_frame before start).restore)
    (fun before => by simpa only using congrArg State.fixed (resolveToUIP_frame before).restore) rfl
  exact built.trans resolved

theorem analysisBeforeStore_nLemmas (s : State) (conflict : Nat) :
    (analysisBeforeStore s conflict).nLemmas = s.nLemmas := by
  have jump := congrArg State.nLemmas (backjump_frame
    { (analysisBuilt s conflict).1 with
      fast := (analysisBuilt s conflict).1.fast - ((analysisBuilt s conflict).1.fast >>> 5) +
        ((analysisBuilt s conflict).2.2 <<< 15)
      slow := (analysisBuilt s conflict).1.slow - ((analysisBuilt s conflict).1.slow >>> 15) +
        ((analysisBuilt s conflict).2.2 <<< 5) } (analysisResolved s conflict).assigned).restore
  have built := (buildLearned_frame (analysisResolved s conflict) (analysisResolved s conflict).assigned).nLemmas
  have resolved := analysisResolved_projection State.nLemmas s conflict
    (fun before start => by simpa only using congrArg State.nLemmas (markClause_frame before start).restore)
    (fun before => (resolveToUIP_frame before).nLemmas) rfl
  exact jump.trans (built.trans resolved)

/-- The real analyzer learns an entailed clause of declared literals. Its
entry assumptions describe the original state, entailed conflict, root tags,
and concrete ordered reason graph. No fact about an intermediate MARK clause
or a returned learned clause is an assumption. -/
theorem analyze_learned_sound {formula : Std.Sat.CNF Nat} (s : State) (conflict : Nat)
    {conflictLits : Array Lit} {rank : Lit → Nat}
    (graph : ReasonGraph formula s s.assigned rank) (arrays : ArrayBounds s)
    (active : ActiveTrail s) (positive : 0 < s.assigned)
    (packed : PackedClause s conflict conflictLits)
    (covered : ∀ lit ∈ conflictLits, TrailMember s s.assigned lit)
    (entailed : CNF.EntailsClause formula (clauseView conflictLits))
    (tags : ValidMarkTags s s.assigned s)
    (root : RootTagConsequences formula s s.assigned s)
    (rootPrefix : ∀ i, i < s.forced → i < s.assigned → s.mark s.trail[i]! = 6) :
    CNF.EntailsClause formula (clauseView (analysisLearned s conflict)) ∧
      (∀ lit ∈ analysisLearned s conflict, LiteralBound s.nVars lit) := by
  let marked := markClause (analysisStart s) conflict
  let resolved := resolveToUIP marked
  have startArrays : ArrayBounds (analysisStart s) :=
    ⟨arrays.firstSize, arrays.marksSize, arrays.reasonsSize, arrays.phasesSize,
      arrays.trailSize, arrays.previousSize, arrays.nextSize⟩
  have startPacked : PackedClause (analysisStart s) conflict conflictLits := packed.frame rfl rfl
  have markFrame := resolutionFrame_markClause (analysisStart s) conflict
  have markStorage : ReasonStorage s marked := markFrame.reasonStorage ⟨rfl, rfl⟩
  have markTrail : marked.trail = s.trail := markFrame.trail
  have markVars : marked.nVars = s.nVars := markFrame.nVars
  have markArrays : ArrayBounds marked := markFrame.arrayBounds startArrays
  have markAssigned : marked.assigned = s.assigned := markClause_assigned (analysisStart s) conflict
  have markForced : marked.forced = s.forced := markClause_forced (analysisStart s) conflict
  have markRoot : RootTagConsequences formula s s.assigned marked := by
    simpa only [Nat.add_zero] using markClause_rootTag startPacked startArrays root 0 (Nat.zero_le _)
  have markTags : ValidMarkTags s s.assigned marked := by
    simpa only [Nat.add_zero] using markClause_validTags (s := analysisStart s) tags
      startPacked startArrays 0 (Nat.zero_le _)
  have markEntailed : CNF.EntailsClause formula (markedClause s s.assigned marked) :=
    markClause_entails_of_clause startPacked startArrays root covered entailed
  have boundary : RootTagBoundary s s.assigned s.forced marked := by
    intro i rootIndex before
    apply Or.inl
    simpa only [Nat.add_zero] using markClause_mark_root startPacked startArrays 0 (Nat.zero_le _)
      (rootPrefix i rootIndex before)
  have resolvedSound := resolveToUIP_sound_of_count graph marked markStorage markTrail markVars
    markArrays markRoot markEntailed markAssigned
  have resolvedTags := resolveToUIP_tags graph marked markStorage markTrail markVars markArrays
    markTags boundary (Nat.le_of_eq markAssigned)
  have resolvedFrame := resolveToUIP_frame marked
  have storage : ReasonStorage s resolved := resolvedFrame.reasonStorage markStorage
  have trail : resolved.trail = s.trail := resolvedFrame.trail.trans markTrail
  have forced : resolved.forced = s.forced := by
    have frameForced : resolved.forced = marked.forced := by
      simpa only using congrArg State.forced resolvedFrame.restore
    exact frameForced.trans markForced
  have candidateBound : resolved.assigned < s.assigned := by
    have markPositive : 0 < marked.assigned := by simpa only [markAssigned] using positive
    simpa only [markAssigned] using resolveToUIP_assigned_lt marked markPositive
  let leaves := fun lit => TrailMember s s.assigned lit ∧ resolved.mark lit = 2
  have cache : ImpliedCache formula s s.assigned rank leaves resolved :=
    resolvedSound.2.1.impliedCache resolvedTags.1 (fun _ member marked => ⟨member, marked⟩)
  have leafMarks : ∀ lit, leaves lit → resolved.mark lit = 2 := fun _ leaf => leaf.2
  have leafRange : ∀ lit, leaves lit →
      TrailMember s s.assigned lit ∧ resolved.forced ≤ rank lit ∧ rank lit ≤ resolved.assigned := by
    rintro lit ⟨⟨i, before, equal⟩, marked⟩
    have position : rank lit = i := by rw [← equal]; exact graph.ranks i before
    have lower : s.forced ≤ i := by
      by_cases rootIndex : i < s.forced
      · have notMarked := resolvedTags.2.not_mark_two rootIndex before
        exact False.elim (notMarked (by simpa only [equal] using marked))
      · omega
    refine ⟨⟨i, before, equal⟩, ?_, ?_⟩
    · simpa only [forced, position] using lower
    · rw [position]
      exact resolvedSound.2.2.1 i before (by simpa only [equal] using marked)
  have originalLeaves : ∀ lit, leaves lit ↔ lit ∈ markedLiterals s s.assigned resolved :=
    fun _ => markedLiterals_mem.symm
  have minimized := buildLearned_entails graph resolved resolved.assigned candidateBound storage trail cache
    leafMarks leafRange originalLeaves resolvedSound.1
  have certificate := buildLearned_certificate graph resolved resolved.assigned candidateBound storage trail cache
    leafMarks leafRange
  refine ⟨minimized, ?_⟩
  intro lit member
  have leaf := certificate.2.2.2.2 lit member
  obtain ⟨i, before, equal⟩ := leaf.1
  simpa only [equal] using (active i before).1

/-- Concrete incoming invariants for a conflict-analysis call. The semantic
premises concern the original input, original roots, and stored conflict and
reason clauses. The analyzer's returned clause is not mentioned here. -/
structure AnalysisEntry (formula : Std.Sat.CNF Nat) (s : State) (conflict : Nat)
    (conflictLits : Array Lit) (rank : Lit → Nat) : Prop where
  graph : ReasonGraph formula s s.assigned rank
  arrays : ArrayBounds s
  active : ActiveTrail s
  positive : 0 < s.assigned
  packed : PackedClause s conflict conflictLits
  covered : ∀ lit ∈ conflictLits, TrailMember s s.assigned lit
  entailed : CNF.EntailsClause formula (clauseView conflictLits)
  tags : ValidMarkTags s s.assigned s
  root : RootTagConsequences formula s s.assigned s
  rootPrefix : ∀ i, i < s.forced → i < s.assigned → s.mark s.trail[i]! = 6

theorem AnalysisEntry.learned_sound {formula : Std.Sat.CNF Nat} {s : State} {conflict : Nat}
    {conflictLits : Array Lit} {rank : Lit → Nat}
    (entry : AnalysisEntry formula s conflict conflictLits rank) :
    CNF.EntailsClause formula (clauseView (analysisLearned s conflict)) ∧
      (∀ lit ∈ analysisLearned s conflict, LiteralBound s.nVars lit) :=
  analyze_learned_sound s conflict entry.graph entry.arrays entry.active entry.positive entry.packed
    entry.covered entry.entailed entry.tags entry.root entry.rootPrefix

/-- The actual clause identifier returned by `analyze` addresses its entailed,
well-formed learned clause in the actual resulting arena. This composes the
real resolution, recursive minimization, backjump, and allocation operations. -/
theorem analyze_stored_clause {formula : Std.Sat.CNF Nat} {s : State} {conflict : Nat}
    {conflictLits : Array Lit} {rank : Lit → Nat}
    (entry : AnalysisEntry formula s conflict conflictLits rank) (reserved : 2 ≤ s.arena.size) :
    PackedClause (analyze s conflict).1 (analyze s conflict).2 (analysisLearned s conflict) ∧
      CNF.EntailsClause formula (clauseView (analysisLearned s conflict)) := by
  have semantic := entry.learned_sound
  rw [analyze_eq_addClause]
  refine ⟨addClause_packed ?_ ?_, semantic.1⟩
  · simpa only [analysisBeforeStore_arena] using reserved
  · simpa only [analysisBeforeStore_nVars] using semantic.2

/-- The actual packed database is extended by exactly the actual entailed
learned clause. Its ghost meaning therefore continues to describe precisely
the input models. The database layout and semantic extension are both checked. -/
theorem analyze_database_meaning {formula : Std.Sat.CNF Nat} {s : State} {conflict : Nat}
    {conflictLits : Array Lit} {rank : Lit → Nat} {original learned : List StoredClause}
    (entry : AnalysisEntry formula s conflict conflictLits rank)
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned) :
    let added : StoredClause := ⟨(analyze s conflict).2, analysisLearned s conflict⟩
    Database (analyze s conflict).1 original (learned ++ [added]) ∧
      DatabaseMeaning formula original (learned ++ [added]) := by
  have semantic := entry.learned_sound
  have beforeDatabase : Database (analysisBeforeStore s conflict) original learned :=
    database.frame (analysisBeforeStore_arena s conflict) (analysisBeforeStore_nVars s conflict)
      (analysisBeforeStore_fixed s conflict) (analysisBeforeStore_nLemmas s conflict)
  have reserved : 2 ≤ s.arena.size := by
    have total := database.layout.size
    omega
  have beforeReserved : 2 ≤ (analysisBeforeStore s conflict).arena.size := by
    simpa only [analysisBeforeStore_arena] using reserved
  have bounded : ∀ lit ∈ analysisLearned s conflict,
      LiteralBound (analysisBeforeStore s conflict).nVars lit := by
    simpa only [analysisBeforeStore_nVars] using semantic.2
  rw [analyze_eq_addClause]
  exact ⟨beforeDatabase.addLearned beforeReserved bounded, meaning.addLearned _ semantic.1⟩

end MicrosatLean.Verification.Implementation.Native.Analysis
