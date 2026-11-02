import MicrosatLean.Verification.Implementation.Native.Reduction.ClauseScan
import MicrosatLean.Verification.Implementation.Native.Reduction.Frame
import MicrosatLean.Verification.Implementation.Native.Representation.DatabaseUpdates
import MicrosatLean.Verification.Implementation.Native.Representation.Meaning

namespace MicrosatLean.Verification.Implementation.Native.Reduction

open CDCL Representation Std.Sat

def keepEntry (phases : Array Bool) (locked : Array Bool) (k : Nat) (entry : StoredClause) : Bool :=
  decide (phaseTrueCount phases entry.lits < k) || locked[entry.id]!

def retainedEntries (old : State) (locked : Array Bool) (k : Nat)
    (entries : List StoredClause) : List StoredClause := entries.filter (keepEntry old.phases locked k)

/-- Ordered literal preservation and the exact final old-ID relocation table. -/
inductive RelocationMatches (remap : Array Nat) : List StoredClause → List StoredClause → Prop where
  | nil : RelocationMatches remap [] []
  | cons {before after : StoredClause} {old kept : List StoredClause}
      (head : before.lits = after.lits ∧ remap[before.id]! = after.id)
      (tail : RelocationMatches remap old kept) :
      RelocationMatches remap (before :: old) (after :: kept)

private structure CompactionSummary (old : State) (locked : Array Bool) (k : Nat)
    (original accumulated remaining : List StoredClause) (initialRemap : Array Nat)
    (result : CompactionAcc) (kept : List StoredClause) : Prop where
  database : Database result.1 original (accumulated ++ kept)
  cursor : result.2.2 = old.arena.size
  vars : result.1.nVars = old.nVars
  phases : result.1.phases = old.phases
  relocations : RelocationMatches result.2.1 (retainedEntries old locked k remaining) kept
  outside : ∀ id, id ∉ (retainedEntries old locked k remaining).map StoredClause.id →
    result.2.1[id]! = initialRemap[id]!
  remapSize : result.2.1.size = initialRemap.size

private theorem retainedEntries_mem {old : State} {locked : Array Bool} {k : Nat}
    {entries : List StoredClause} {entry : StoredClause}
    (member : entry ∈ retainedEntries old locked k entries) : entry ∈ entries :=
  (List.mem_filter.mp member).1

private theorem compaction_loop (old : State) (locked : Array Bool) (k : Nat)
    (remaining : List StoredClause) (start index : Nat) (s : State) (remap : Array Nat)
    (layout : DatabaseFrom old start remaining) (original accumulated : List StoredClause)
    (database : Database s original accumulated) (vars : s.nVars = old.nVars)
    (phases : s.phases = old.phases) (coverage : old.arena.size ≤ remap.size) :
    ∃ kept, CompactionSummary old locked k original accumulated remaining remap
      (forIn (m := Id) (List.range' index remaining.length) (s, remap, start)
        (compactionBody old.arena locked k)) kept := by
  induction remaining generalizing start index s remap accumulated with
  | nil =>
    change ∃ kept, CompactionSummary old locked k original accumulated [] remap (s, remap, start) kept
    refine ⟨[], ?_⟩
    exact ⟨by simpa using database, layout, vars, phases, .nil, fun _ _ => rfl, rfl⟩
  | cons entry rest ih =>
    obtain ⟨id, packed, restLayout⟩ := layout
    have distinct : entry.id ∉ rest.map StoredClause.id := by
      have all := (show DatabaseFrom old start (entry :: rest) from ⟨id, packed, restLayout⟩).nodup_ids
      exact (List.nodup_cons.mp all).1
    have outsideRest : entry.id ∉ (retainedEntries old locked k rest).map StoredClause.id := by
      intro member
      obtain ⟨other, member, same⟩ := List.mem_map.mp member
      exact distinct (List.mem_map.mpr ⟨other, retainedEntries_mem member, same⟩)
    have bounded : ∀ lit ∈ entry.lits, LiteralBound s.nVars lit := by
      simpa only [vars] using packed.wellFormed
    have reserved : 2 ≤ s.arena.size := by have := database.layout.size; omega
    by_cases keep : keepEntry old.phases locked k entry = true
    · let added := s.addClause entry.lits false
      let nextRemap := remap.set! entry.id added.2
      have step : compactionBody old.arena locked k index (s, remap, start) =
          .yield (added.1, nextRemap, entry.id + entry.lits.size + 1) := by
        have clause : PackedClause old (start + 2) entry.lits := by simpa only [id] using packed
        rw [compactionBody_packed clause]
        have condition : (decide (phaseTrueCount s.phases entry.lits < k) || locked[start + 2]!) = true := by
          simpa only [phases, ← id, keepEntry] using keep
        simp only [condition, ite_true]
        simp only [← id, added, nextRemap]
      have nextDatabase := database.addLearned reserved bounded
      obtain ⟨kept, result⟩ := ih (entry.id + entry.lits.size + 1) (index + 1) added.1 nextRemap
        restLayout (accumulated ++ [⟨added.2, entry.lits⟩]) nextDatabase
        (by simpa only [added, addClause_nVars] using vars)
        (by simpa only [added, addClause_phases] using phases)
        (by simpa only [nextRemap, Array.size_set!] using coverage)
      refine ⟨⟨added.2, entry.lits⟩ :: kept, ?_⟩
      rw [List.length_cons, List.range'_succ, List.forIn_cons, step]
      simp only [bind]
      have filter : retainedEntries old locked k (entry :: rest) =
          entry :: retainedEntries old locked k rest := by simp only [retainedEntries, List.filter_cons, keep, ite_true]
      constructor
      · simpa only [List.append_assoc, List.singleton_append] using result.database
      · exact result.cursor
      · exact result.vars
      · exact result.phases
      · rw [filter]
        apply RelocationMatches.cons
        · constructor
          · rfl
          · rw [result.outside entry.id outsideRest]
            exact Array.getElem!_set!_self remap entry.id added.2
              (Nat.lt_of_lt_of_le packed.start_index coverage)
        · exact result.relocations
      · intro query outside
        have tailOutside : query ∉ (retainedEntries old locked k rest).map StoredClause.id := by
          intro member
          exact outside (by rw [filter]; exact List.mem_cons_of_mem _ member)
        rw [result.outside query tailOutside]
        exact Array.getElem!_set!_ne remap entry.id query added.2 (by
          intro same
          exact outside (by rw [filter]; simp only [List.map_cons, List.mem_cons]; exact Or.inl same.symm))
      · simpa only [nextRemap, Array.size_set!] using result.remapSize
    · have skip : keepEntry old.phases locked k entry = false := by
        cases equal : keepEntry old.phases locked k entry <;> simp_all
      have step : compactionBody old.arena locked k index (s, remap, start) =
          .yield (s, remap, entry.id + entry.lits.size + 1) := by
        have clause : PackedClause old (start + 2) entry.lits := by simpa only [id] using packed
        rw [compactionBody_packed clause]
        have condition : (decide (phaseTrueCount s.phases entry.lits < k) || locked[start + 2]!) = false := by
          simpa only [phases, ← id, keepEntry] using skip
        simp only [condition, Bool.false_eq_true, ↓reduceIte]
        simp only [← id]
      obtain ⟨kept, result⟩ := ih (entry.id + entry.lits.size + 1) (index + 1) s remap restLayout
        accumulated database vars phases coverage
      refine ⟨kept, ?_⟩
      rw [List.length_cons, List.range'_succ, List.forIn_cons, step]
      simp only [bind]
      have filter : retainedEntries old locked k (entry :: rest) = retainedEntries old locked k rest := by
        simp only [retainedEntries, List.filter_cons, skip, Bool.false_eq_true, ↓reduceIte]
      exact ⟨result.database, result.cursor, result.vars, result.phases,
        by simpa only [filter] using result.relocations,
        by simpa only [filter] using result.outside, result.remapSize⟩

theorem RelocationMatches.literals {remap : Array Nat} {old kept : List StoredClause}
    (matching : RelocationMatches remap old kept) :
    old.map StoredClause.lits = kept.map StoredClause.lits := by
  induction matching with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, head.1, ih]

theorem RelocationMatches.views {remap : Array Nat} {old kept : List StoredClause}
    (matching : RelocationMatches remap old kept) :
    old.map StoredClause.view = kept.map StoredClause.view := by
  induction matching with
  | nil => rfl
  | cons head tail ih => simp only [List.map_cons, StoredClause.view, head.1, ih]

theorem RelocationMatches.association {remap : Array Nat} {old kept : List StoredClause}
    (matching : RelocationMatches remap old kept) {entry : StoredClause} (member : entry ∈ old) :
    ∃ relocated ∈ kept, entry.lits = relocated.lits ∧ remap[entry.id]! = relocated.id := by
  induction matching with
  | nil => simp at member
  | cons head tail ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨_, by simp, head⟩
    · obtain ⟨relocated, stored, relation⟩ := ih member
      exact ⟨relocated, List.mem_cons_of_mem _ stored, relation⟩

private theorem database_suffix {s : State} {start : Nat} {original learned : List StoredClause}
    (layout : DatabaseFrom s start (original ++ learned)) :
    DatabaseFrom s (start + (original.map fun entry => entry.lits.size + 3).sum) learned := by
  induction original generalizing start with
  | nil => simpa only [List.nil_append, List.map_nil, List.sum_nil, Nat.add_zero] using layout
  | cons entry rest ih =>
    have result := ih layout.2.2
    have id := layout.1
    have boundary : start + (entry.lits.size + 3 + (rest.map fun e => e.lits.size + 3).sum) =
        entry.id + entry.lits.size + 1 + (rest.map fun e => e.lits.size + 3).sum := by omega
    simpa only [List.map_cons, List.sum_cons, boundary] using result

theorem compactionInitial_vars (s : State) : (compactionInitial s).1.nVars = s.nVars := by
  simpa only [compactionInitial] using congrArg State.nVars (removeLearnedWatches_frame s).restore

theorem compactionInitial_phases (s : State) : (compactionInitial s).1.phases = s.phases := by
  simpa only [compactionInitial] using congrArg State.phases (removeLearnedWatches_frame s).restore

theorem compactionInitial_start (s : State) : (compactionInitial s).2.2 = s.fixed := by
  simpa only [compactionInitial] using congrArg State.fixed (removeLearnedWatches_frame s).restore

/-- Actual compaction relocates exactly the filtered old learned entries.
The natural entry premise concerns only the concrete initial original prefix;
no final retained inclusion, relocation or database correctness is assumed. -/
theorem compactionResult_database {s : State} {original learned : List StoredClause}
    (database : Database s original learned)
    (initial : Database (compactionInitial s).1 original []) (k : Nat) :
    ∃ kept, Database (compactionResult s k).1 original kept ∧
      RelocationMatches (compactionResult s k).2.1
        (retainedEntries s (lockedReasons s) k learned) kept ∧
      (compactionResult s k).2.2 = s.arena.size ∧
      (∀ id, id ∉ (retainedEntries s (lockedReasons s) k learned).map StoredClause.id →
        (compactionResult s k).2.1[id]! = 0) ∧
      (compactionResult s k).2.1.size = s.arena.size := by
  have suffix : DatabaseFrom s s.fixed learned := by
    rw [database.fixed]
    exact database_suffix database.layout
  have layout : DatabaseFrom s (compactionInitial s).2.2 learned := by
    rw [compactionInitial_start]
    exact suffix
  obtain ⟨kept, result⟩ := compaction_loop s (lockedReasons s) k learned (compactionInitial s).2.2
    0 (compactionInitial s).1 (compactionInitial s).2.1 layout original [] initial
    (compactionInitial_vars s) (compactionInitial_phases s) (by simp [compactionInitial])
  have execute : compactionResult s k = forIn (m := Id) (List.range' 0 learned.length)
      ((compactionInitial s).1, (compactionInitial s).2.1, (compactionInitial s).2.2)
      (compactionBody s.arena (lockedReasons s) k) := by
    simp only [compactionResult, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
      Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one, database.learnedCount]
  rw [execute]
  refine ⟨kept, by simpa only [List.nil_append] using result.database, result.relocations,
    result.cursor, ?_, ?_⟩
  · intro id outside
    rw [result.outside id outside]
    simp [compactionInitial, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  · simpa only [compactionInitial, Array.size_replicate] using result.remapSize

theorem compactionResult_meaning {formula : CNF Nat} {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (initial : Database (compactionInitial s).1 original []) (k : Nat) :
    ∃ kept, Database (compactionResult s k).1 original kept ∧ DatabaseMeaning formula original kept ∧
      RelocationMatches (compactionResult s k).2.1 (retainedEntries s (lockedReasons s) k learned) kept := by
  obtain ⟨kept, stored, matching, _, _, _⟩ := compactionResult_database database initial k
  refine ⟨kept, stored, meaning.forgetLearned ?_, matching⟩
  rw [← matching.views]
  intro view member
  obtain ⟨entry, retained, equal⟩ := List.mem_map.mp member
  exact List.mem_map.mpr ⟨entry, retainedEntries_mem retained, equal⟩

theorem reduceDB_database_meaning {formula : CNF Nat} {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (initial : Database (compactionInitial s).1 original []) (k : Nat) :
    ∃ kept, Database (s.reduceDB k) original kept ∧ DatabaseMeaning formula original kept ∧
      RelocationMatches (compactionResult s k).2.1 (retainedEntries s (lockedReasons s) k learned) kept := by
  obtain ⟨kept, stored, semantic, matching⟩ := compactionResult_meaning database meaning initial k
  rw [reduceDB_eq_compaction]
  exact ⟨kept, stored.frame rfl rfl rfl rfl, semantic, matching⟩

/-- The remaining watch-filter obligation concerns only genuine original
literal slices and terminators, never arbitrary arena cells or watch links.
A valid watch certificate must show that header writes miss these reads. -/
def OriginalReads (s : State) (original : List StoredClause) : Prop :=
  ∀ entry ∈ original, ∀ i, i ≤ entry.lits.size →
    s.removeLearnedWatches.db (entry.id + i) = s.db (entry.id + i)

private theorem prefix_entry_end {s : State} {start : Nat} {original learned : List StoredClause}
    (layout : DatabaseFrom s start (original ++ learned)) {entry : StoredClause}
    (member : entry ∈ original) :
    entry.id + entry.lits.size + 1 ≤ start + (original.map fun e => e.lits.size + 3).sum := by
  induction original generalizing start with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · have id := layout.1
      simp only [List.map_cons, List.sum_cons]
      omega
    · have bound := ih layout.2.2 member
      have id := layout.1
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem prefix_layout {old current : State} {start : Nat} {original learned : List StoredClause}
    (layout : DatabaseFrom old start (original ++ learned))
    (size : current.arena.size = start + (original.map fun e => e.lits.size + 3).sum)
    (preserved : ∀ entry ∈ original, PackedClause current entry.id entry.lits) :
    DatabaseFrom current start original := by
  induction original generalizing start with
  | nil => simpa only [DatabaseFrom, List.map_nil, List.sum_nil, Nat.add_zero] using size.symm
  | cons entry rest ih =>
    refine ⟨layout.1, preserved entry (by simp), ih layout.2.2 ?_ ?_⟩
    · have id := layout.1
      simp only [List.map_cons, List.sum_cons] at size
      omega
    · intro other member
      exact preserved other (List.mem_cons_of_mem _ member)

private theorem database_fixed_bound {s : State} {original learned : List StoredClause}
    (database : Database s original learned) : s.fixed ≤ s.arena.size := by
  have size := database.layout.size
  rw [List.map_append, List.sum_append] at size
  rw [database.fixed]
  omega

theorem compactionInitial_database {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (reads : OriginalReads s original) :
    Database (compactionInitial s).1 original [] := by
  let detached := s.removeLearnedWatches
  have frame := removeLearnedWatches_frame s
  have fixed : detached.fixed = s.fixed := by simpa only using congrArg State.fixed frame.restore
  have initialSize : (compactionInitial s).1.arena.size = s.fixed := by
    change (detached.arena.extract 0 detached.fixed).size = s.fixed
    rw [Array.size_extract, fixed, frame.arenaSize, Nat.min_eq_left (database_fixed_bound database), Nat.sub_zero]
  have initialRead (i : Nat) (before : i < s.fixed) :
      (compactionInitial s).1.db i = detached.db i := by
    change (detached.arena.extract 0 detached.fixed)[i]! = detached.arena[i]!
    have within : i < min detached.fixed detached.arena.size := by
      rw [fixed, frame.arenaSize, Nat.min_eq_left (database_fixed_bound database)]
      exact before
    simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?, Array.getElem?_extract,
      Nat.sub_zero, within, ite_true, Nat.zero_add]
  have preserved : ∀ entry ∈ original, PackedClause (compactionInitial s).1 entry.id entry.lits := by
    intro entry member
    have packed := database.layout.packed (List.mem_append_left _ member)
    have last : entry.id + entry.lits.size < s.fixed := by
      have bound := prefix_entry_end database.layout member
      rw [← database.fixed] at bound
      omega
    constructor
    · exact packed.startLower
    · rw [initialSize]
      exact last
    · intro i within
      rw [initialRead _ (by omega), reads entry member i (by omega)]
      exact packed.literals i within
    · rw [initialRead _ last, reads entry member entry.lits.size (Nat.le_refl _)]
      exact packed.terminator
    · simpa only [compactionInitial_vars] using packed.wellFormed
  constructor
  · simp only [List.append_nil]
    apply prefix_layout database.layout
    · rw [initialSize, database.fixed]
    · exact preserved
  · have same : (compactionInitial s).1.fixed = s.fixed := fixed
    exact same.trans database.fixed
  · rfl

/-- Actual database compaction and model preservation reduce to the isolated
watch-header disjointness obligation `OriginalReads`; the scan, filter,
allocator, counters and relocation association are already proved concretely. -/
theorem reduceDB_database_meaning_of_originalReads {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} (database : Database s original learned)
    (meaning : DatabaseMeaning formula original learned) (reads : OriginalReads s original) (k : Nat) :
    ∃ kept, Database (s.reduceDB k) original kept ∧ DatabaseMeaning formula original kept ∧
      RelocationMatches (compactionResult s k).2.1 (retainedEntries s (lockedReasons s) k learned) kept :=
  reduceDB_database_meaning database meaning (compactionInitial_database database reads) k

end MicrosatLean.Verification.Implementation.Native.Reduction
