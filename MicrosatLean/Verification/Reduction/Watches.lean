import MicrosatLean.Verification.Reduction.FilterWatches
import MicrosatLean.Verification.Propagation.WatchAllocation
import MicrosatLean.Verification.Propagation.DatabaseIdentity

namespace MicrosatLean.Verification.Reduction

open CDCL Representation Propagation Analysis Std.Sat

theorem compactionInitial_arrayBounds {s : State} (arrays : ArrayBounds s) :
    ArrayBounds (compactionInitial s).1 := by
  have detached := (removeLearnedWatches_frame s).arrayBounds arrays
  exact ⟨detached.firstSize, detached.marksSize, detached.reasonsSize, detached.phasesSize,
    detached.trailSize, detached.previousSize, detached.nextSize⟩

/-- Extracting the actual original prefix retains every filtered watch
header, including the zero next pointers at the ends of finite lists. -/
theorem compactionInitial_watchCertificate {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (arrays : ArrayBounds s) :
    WatchCertificate (compactionInitial s).1 original (originalWatchHeads s.fixed heads) := by
  have filtered := removeLearnedWatches_certificate database certificate arrays
  have afterDatabase := removeLearnedWatches_database database certificate
  have frame := removeLearnedWatches_frame s
  have fixed : s.removeLearnedWatches.fixed = s.fixed :=
    by simpa only using congrArg State.fixed frame.restore
  constructor
  · intro lit
    apply (filtered.links lit).frame (after := (compactionInitial s).1) rfl
    intro ref member
    obtain ⟨entry, stored, id, wide⟩ := filtered.references lit ref member
    have lower := (database.layout.packed (List.mem_append_left learned stored)).startLower
    have beforeFixed : watchLinkPos ref < s.fixed := by
      have bound := original_id_lt_fixed database stored
      simp only [watchClause] at id
      unfold watchLinkPos
      omega
    have beforeArena := storedWatchRef_link_bound afterDatabase
      ⟨entry, List.mem_append_left learned stored, id, wide⟩
    change (s.removeLearnedWatches.arena.extract 0 s.removeLearnedWatches.fixed)[watchLinkPos ref]! = _
    have within : watchLinkPos ref < min s.removeLearnedWatches.fixed s.removeLearnedWatches.arena.size := by
      rw [fixed]
      omega
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_extract,
      Nat.sub_zero, within, ite_true, Nat.zero_add, State.db]
  · exact filtered.references
  · exact filtered.covered
  · exact filtered.unique

private theorem learned_layout {s : State} {start : Nat} {original learned : List StoredClause}
    (layout : DatabaseFrom s start (original ++ learned)) :
    DatabaseFrom s (start + (original.map fun e => e.lits.size + 3).sum) learned := by
  induction original generalizing start with
  | nil => simpa only [List.nil_append, List.map_nil, List.sum_nil, Nat.add_zero] using layout
  | cons entry rest ih =>
    have tail := ih layout.2.2
    have id := layout.1
    have boundary : start + (entry.lits.size + 3 + (rest.map fun e => e.lits.size + 3).sum) =
        entry.id + entry.lits.size + 1 + (rest.map fun e => e.lits.size + 3).sum := by omega
    simpa only [List.map_cons, List.sum_cons, boundary] using tail

/-- Every keep branch is the actual allocator. Every skip branch changes
neither lists nor stored clauses. The ghost database is obtained by this
induction, independently of the semantic compaction theorem. -/
private theorem compaction_watchLoop (old : State) (locked : Array Bool) (k : Nat)
    (remaining : List StoredClause) (start index : Nat) (s : State) (remap : Array Nat)
    (layout : DatabaseFrom old start remaining) (original accumulated : List StoredClause)
    (database : Database s original accumulated) (arrays : ArrayBounds s)
    (heads : Nat → List Nat) (certificate : WatchCertificate s (original ++ accumulated) heads)
    (vars : s.nVars = old.nVars)
    (distinct : ∀ entry ∈ remaining, 1 < entry.lits.size → entry.lits[0]! ≠ entry.lits[1]!) :
    let result := forIn (m := Id) (List.range' index remaining.length)
      (s, remap, start) (compactionBody old.arena locked k)
    ∃ kept newHeads, Database result.1 original (accumulated ++ kept) ∧
      ArrayBounds result.1 ∧ WatchCertificate result.1 (original ++ (accumulated ++ kept)) newHeads := by
  induction remaining generalizing start index s remap accumulated heads with
  | nil =>
    change ∃ kept newHeads, Database s original (accumulated ++ kept) ∧
      ArrayBounds s ∧ WatchCertificate s (original ++ (accumulated ++ kept)) newHeads
    exact ⟨[], heads, by simpa only [List.append_nil] using database,
      arrays, by simpa only [List.append_nil] using certificate⟩
  | cons entry rest ih =>
    obtain ⟨id, packed, tailLayout⟩ := layout
    have wellFormed : ∀ lit ∈ entry.lits, LiteralBound s.nVars lit := by
      simpa only [vars] using packed.wellFormed
    have reserved : 2 ≤ s.arena.size := by have := database.layout.size; omega
    have tailDistinct : ∀ other ∈ rest, 1 < other.lits.size → other.lits[0]! ≠ other.lits[1]! :=
      fun other member => distinct other (List.mem_cons_of_mem entry member)
    have clause : PackedClause old (start + 2) entry.lits := by simpa only [id] using packed
    by_cases keep : (decide (phaseTrueCount s.phases entry.lits < k) || locked[start + 2]!) = true
    · let added := s.addClause entry.lits false
      let nextHeads := allocatedHeads s heads entry.lits
      have nextDatabase := database.addLearned reserved wellFormed
      have nextCertificate : WatchCertificate added.1
          (original ++ (accumulated ++ [⟨added.2, entry.lits⟩])) nextHeads := by
        simpa only [List.append_assoc, added, nextHeads] using certificate.addClause database
          entry.lits false arrays reserved wellFormed (distinct entry (by simp))
      obtain ⟨kept, resultHeads, stored, resultArrays, watched⟩ :=
        ih (entry.id + entry.lits.size + 1) (index + 1) added.1 (remap.set! entry.id added.2)
          tailLayout (accumulated ++ [⟨added.2, entry.lits⟩]) nextDatabase arrays.addClause
          nextHeads nextCertificate (by simpa only [added, addClause_nVars] using vars) tailDistinct
      refine ⟨⟨added.2, entry.lits⟩ :: kept, resultHeads, ?_⟩
      rw [List.length_cons, List.range'_succ, List.forIn_cons, compactionBody_packed clause]
      rw [← id] at keep
      simp only [← id, keep, ite_true, bind]
      exact ⟨by simpa only [List.append_assoc, List.singleton_append] using stored,
        resultArrays, by simpa only [List.append_assoc, List.singleton_append] using watched⟩
    · have skip : (decide (phaseTrueCount s.phases entry.lits < k) || locked[start + 2]!) = false := by
        cases value : (decide (phaseTrueCount s.phases entry.lits < k) || locked[start + 2]!) <;> simp_all
      obtain ⟨kept, resultHeads, stored, resultArrays, watched⟩ :=
        ih (entry.id + entry.lits.size + 1) (index + 1) s remap tailLayout accumulated
          database arrays heads certificate vars tailDistinct
      refine ⟨kept, resultHeads, ?_⟩
      rw [List.length_cons, List.range'_succ, List.forIn_cons, compactionBody_packed clause]
      rw [← id] at skip
      simp only [← id, skip, Bool.false_eq_true, ↓reduceIte, bind]
      exact ⟨stored, resultArrays, watched⟩

theorem compactionResult_watches {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (arrays : ArrayBounds s) (k : Nat) :
    ∃ kept newHeads, Database (compactionResult s k).1 original kept ∧
      ArrayBounds (compactionResult s k).1 ∧
      WatchCertificate (compactionResult s k).1 (original ++ kept) newHeads := by
  have initial := compactionInitial_database database (originalReads_of_watchCertificate database certificate)
  have initialWatches : WatchCertificate (compactionInitial s).1 (original ++ [])
      (originalWatchHeads s.fixed heads) := by
    simpa only [List.append_nil] using compactionInitial_watchCertificate database certificate arrays
  have layout : DatabaseFrom s (compactionInitial s).2.2 learned := by
    rw [compactionInitial_start, database.fixed]
    exact learned_layout database.layout
  obtain ⟨kept, newHeads, stored, resultArrays, watched⟩ :=
    compaction_watchLoop s (lockedReasons s) k learned (compactionInitial s).2.2 0
      (compactionInitial s).1 (compactionInitial s).2.1 layout original [] initial
      (compactionInitial_arrayBounds arrays) (originalWatchHeads s.fixed heads) initialWatches
      (compactionInitial_vars s) (by
        intro entry member wide
        exact (certificate.covered entry (List.mem_append_right original member) (by omega)).1)
  have execute : compactionResult s k = forIn (m := Id) (List.range' 0 learned.length)
      ((compactionInitial s).1, (compactionInitial s).2.1, (compactionInitial s).2.2)
      (compactionBody s.arena (lockedReasons s) k) := by
    simp only [compactionResult, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, database.learnedCount]
  rw [execute]
  exact ⟨kept, newHeads, by simpa only [List.nil_append] using stored, resultArrays,
    by simpa only [List.nil_append] using watched⟩

private theorem watchCertificate_reasonStats {s : State} {entries : List StoredClause}
    {heads : Nat → List Nat} (certificate : WatchCertificate s entries heads)
    (reasons : Array Nat) (stats : Stats) :
    WatchCertificate { s with reasons := reasons, stats := stats } entries heads := by
  refine ⟨?_, certificate.references, certificate.covered, certificate.unique⟩
  intro lit
  exact (certificate.links lit).frame (after := { s with reasons := reasons, stats := stats }) rfl (fun _ _ => rfl)

/-- The final reason relocation and statistics update leave the rebuilt
watch arrays unchanged. The kept witness is genuine actual packed storage. -/
theorem reduceDB_watches {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (arrays : ArrayBounds s) (k : Nat) :
    ∃ kept newHeads, Database (s.reduceDB k) original kept ∧ ArrayBounds (s.reduceDB k) ∧
      WatchCertificate (s.reduceDB k) (original ++ kept) newHeads := by
  obtain ⟨kept, newHeads, stored, resultArrays, watched⟩ := compactionResult_watches database certificate arrays k
  rw [reduceDB_eq_compaction]
  refine ⟨kept, newHeads, stored.frame rfl rfl rfl rfl, ?_, watchCertificate_reasonStats watched _ _⟩
  exact ⟨resultArrays.firstSize, resultArrays.marksSize,
    (relocatedReasons_size _ _).trans resultArrays.reasonsSize, resultArrays.phasesSize,
    resultArrays.trailSize, resultArrays.previousSize, resultArrays.nextSize⟩

/-- Packed database uniqueness aligns the rebuilt lists with any concrete
kept witness already supplied by the semantic/reason preservation theorem. -/
theorem reduceDB_watchCertificate {s : State} {original learned kept : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (arrays : ArrayBounds s) (k : Nat)
    (stored : Database (s.reduceDB k) original kept) :
    ∃ newHeads, ArrayBounds (s.reduceDB k) ∧ WatchCertificate (s.reduceDB k) (original ++ kept) newHeads := by
  obtain ⟨other, newHeads, otherDatabase, resultArrays, watched⟩ := reduceDB_watches database certificate arrays k
  have same := (otherDatabase.unique stored).2
  subst other
  exact ⟨newHeads, resultArrays, watched⟩

/-- One shared kept database witnesses actual reduction semantics, reason
relocation, reason DAG validity, array bounds and the complete watch layout. -/
theorem reduceDB_reasons_and_watches {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    (proper : ReasonDatabase s (original ++ learned)) (arrays : ArrayBounds s)
    (active : ActiveTrail s) (graph : ReasonGraph formula s s.assigned rank)
    (root : s.assigned = s.forced) (k : Nat) :
    ∃ kept newHeads, Database (s.reduceDB k) original kept ∧ DatabaseMeaning formula original kept ∧
      RelocationMatches (compactionResult s k).2.1
        (retainedEntries s (lockedReasons s) k learned) kept ∧
      ReasonRelocations s (s.reduceDB k) (original ++ learned) (original ++ kept) ∧
      ReasonDatabase (s.reduceDB k) (original ++ kept) ∧
      ReasonGraph formula (s.reduceDB k) (s.reduceDB k).assigned rank ∧
      ArrayBounds (s.reduceDB k) ∧ WatchCertificate (s.reduceDB k) (original ++ kept) newHeads := by
  obtain ⟨kept, stored, semantic, matching, relocations, resultReasons, resultGraph⟩ :=
    reduceDB_reasons database meaning certificate proper arrays active graph root k
  obtain ⟨newHeads, resultArrays, watched⟩ := reduceDB_watchCertificate database certificate arrays k stored
  exact ⟨kept, newHeads, stored, semantic, matching, relocations, resultReasons, resultGraph, resultArrays, watched⟩

end MicrosatLean.Verification.Reduction
