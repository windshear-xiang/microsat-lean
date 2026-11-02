import MicrosatLean.Verification.Implementation.Native.Representation.Arena
import MicrosatLean.Verification.Implementation.Native.Logic.ClauseSpace
import MicrosatLean.Verification.Implementation.Native.Specification

namespace MicrosatLean.Verification.Implementation.Native.Representation

open CDCL



/-- Original clauses precede learned clauses. The fixed boundary and learned
counter agree with this ghost layout of the actual packed arena. -/
structure Database (s : State) (original learned : List StoredClause) : Prop where
  layout : DatabaseFrom s 2 (original ++ learned)
  fixed : s.fixed = 2 + (original.map fun entry => entry.lits.size + 3).sum
  learnedCount : s.nLemmas = learned.length


def databaseView (entries : List StoredClause) : Std.Sat.CNF Nat :=
  ⟨(entries.map StoredClause.view).toArray⟩

theorem DatabaseFrom.size {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) :
    s.arena.size = start + (entries.map fun entry => entry.lits.size + 3).sum := by
  induction entries generalizing start with
  | nil => exact layout.symm
  | cons entry rest ih =>
    obtain ⟨id, _, tail⟩ := layout
    have total := ih tail
    simp only [List.map_cons, List.sum_cons]
    omega

theorem DatabaseFrom.packed {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) {entry : StoredClause} (member : entry ∈ entries) :
    PackedClause s entry.id entry.lits := by
  induction entries generalizing start with
  | nil => simp at member
  | cons head rest ih =>
    rcases List.mem_cons.mp member with rfl | member
    · exact layout.2.1
    · exact ih layout.2.2 member

theorem DatabaseFrom.id_lower {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) {entry : StoredClause} (member : entry ∈ entries) :
    start + 2 ≤ entry.id := by
  induction entries generalizing start with
  | nil => simp at member
  | cons head rest ih =>
    obtain ⟨id, _, tail⟩ := layout
    rcases List.mem_cons.mp member with rfl | member
    · omega
    · have lower := ih tail member
      omega

/-- Header cells of a later clause lie strictly beyond every earlier literal
and terminator. This spacing is stronger than mere clause-ID uniqueness. -/
theorem DatabaseFrom.spacing {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) :
    entries.Pairwise (fun left right => left.id + left.lits.size + 3 ≤ right.id) := by
  induction entries generalizing start with
  | nil => exact List.Pairwise.nil
  | cons head rest ih =>
    apply List.pairwise_cons.mpr
    refine ⟨?_, ih layout.2.2⟩
    intro entry member
    have lower := layout.2.2.id_lower member
    omega

theorem DatabaseFrom.nodup_ids {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) : (entries.map StoredClause.id).Nodup := by
  induction entries generalizing start with
  | nil => simp
  | cons head rest ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_, ih layout.2.2⟩
    intro member
    obtain ⟨entry, member, same⟩ := List.mem_map.mp member
    have lower := layout.2.2.id_lower member
    omega

theorem DatabaseFrom.append_addClause {s : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) {lits : Array Lit} {original : Bool}
    (reserved : 2 ≤ s.arena.size) (bounded : ∀ lit ∈ lits, LiteralBound s.nVars lit) :
    DatabaseFrom (s.addClause lits original).1 start
      (entries ++ [⟨(s.addClause lits original).2, lits⟩]) := by
  induction entries generalizing start with
  | nil =>
    simp only [List.nil_append, DatabaseFrom]
    refine ⟨?_, addClause_packed reserved bounded, ?_⟩
    · rw [addClause_id, layout]
    · rw [addClause_id, addClause_arena_size]
      omega
  | cons entry rest ih =>
    obtain ⟨id, packed, tail⟩ := layout
    exact ⟨id, packed.addClause lits, ih tail⟩

@[simp] theorem addClause_learnedCount {s : State} {lits : Array Lit} {original : Bool} :
    (s.addClause lits original).1.nLemmas = s.nLemmas + if original then 0 else 1 := by
  by_cases watches : 1 < lits.size <;> cases original <;>
    simp [State.addClause, State.addWatch, watches]

theorem Database.addLearned {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {lits : Array Lit}
    (reserved : 2 ≤ s.arena.size) (bounded : ∀ lit ∈ lits, LiteralBound s.nVars lit) :
    Database (s.addClause lits false).1 original
      (learned ++ [⟨(s.addClause lits false).2, lits⟩]) := by
  constructor
  · simpa only [List.append_assoc] using database.layout.append_addClause reserved bounded
  · simpa only [addClause_fixed, Bool.false_eq_true, ↓reduceIte] using database.fixed
  · simp [database.learnedCount]

theorem Database.addOriginal {s : State} {original : List StoredClause}
    (database : Database s original []) {lits : Array Lit}
    (reserved : 2 ≤ s.arena.size) (bounded : ∀ lit ∈ lits, LiteralBound s.nVars lit) :
    Database (s.addClause lits true).1
      (original ++ [⟨(s.addClause lits true).2, lits⟩]) [] := by
  constructor
  · simpa using database.layout.append_addClause reserved bounded
  · have size := database.layout.size
    simp only [List.append_nil] at size
    rw [addClause_fixed]
    simp only [↓reduceIte, addClause_arena_size, List.map_append, List.map_cons,
      List.map_nil, List.sum_append, List.sum_cons, List.sum_nil, Nat.add_zero]
    omega
  · simp [database.learnedCount]

/-- Once no duplicate canonical learned clauses are retained, the actual
runtime counter is bounded by the finite standard-literal clause space. -/
theorem Database.learnedCount_le {s : State} {original learned : List StoredClause}
    (database : Database s original learned)
    (distinct : (learned.map fun entry => Logic.ClauseSpace.canonicalize s.nVars
      (entry.lits.toList.map literalView)).Nodup) : s.nLemmas ≤ 3 ^ s.nVars := by
  rw [database.learnedCount]
  have bound := Logic.ClauseSpace.distinct_canonicalized_length_le s.nVars
    (learned.map fun entry => entry.lits.toList.map literalView)
    (by simpa only [List.map_map, Function.comp_def] using distinct)
  simpa only [List.length_map] using bound

end MicrosatLean.Verification.Implementation.Native.Representation
