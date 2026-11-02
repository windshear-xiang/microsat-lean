import MicrosatLean.Verification.Invariant
import MicrosatLean.Verification.Implementation.Native.Search.MachineInvariant

namespace MicrosatLean.Verification.Implementation.Bridge

/-! Shared representation identities for the two invariant presentations. -/

def toNativeEntry (entry : StoredClause) : Native.Representation.StoredClause :=
  ⟨entry.id, entry.lits⟩

def fromNativeEntry (entry : Native.Representation.StoredClause) : StoredClause :=
  ⟨entry.id, entry.lits⟩

@[simp] theorem from_to_entry (entry : StoredClause) :
    fromNativeEntry (toNativeEntry entry) = entry := rfl

@[simp] theorem to_from_entry (entry : Native.Representation.StoredClause) :
    toNativeEntry (fromNativeEntry entry) = entry := rfl

theorem toNativeEntry_injective : Function.Injective toNativeEntry := by
  intro left right same
  have equal := congrArg fromNativeEntry same
  simpa only [from_to_entry] using equal

theorem nodup_of_map {α β : Type} (f : α → β) {items : List α}
    (distinct : (items.map f).Nodup) : items.Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head rest ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp distinct
    exact List.nodup_cons.mpr ⟨fun member => absent (List.mem_map.mpr ⟨head, member, rfl⟩), ih tail⟩

theorem view_injective : Function.Injective literalView := Native.literalView_injective

@[simp] theorem native_view_eq : Native.literalView = literalView := rfl

@[simp] theorem native_clauseView_eq : Native.clauseView = clauseView := rfl

@[simp] theorem native_formulaView_eq : Native.formulaView = formulaView := rfl

@[simp] theorem native_entry_view (entry : StoredClause) :
    (toNativeEntry entry).view = entry.view := rfl

theorem prefix_mem_iff {a : LogicalState} {count : Nat} (bound : count ≤ a.trail.length)
    (lit : Literal) : lit ∈ prefixLiterals a count ↔
      ∃ i, i < count ∧ a.trail[i]!.literal = lit := by
  simp only [prefixLiterals, List.mem_map]
  constructor
  · rintro ⟨entry, member, equal⟩
    obtain ⟨i, hi, value⟩ := List.mem_iff_getElem.mp member
    have before : i < count := by simpa only [List.length_take, Nat.min_eq_left bound] using hi
    have active : i < a.trail.length := Nat.lt_of_lt_of_le before bound
    refine ⟨i, before, ?_⟩
    rw [← value] at equal
    simpa only [List.getElem_take, getElem!_pos a.trail i active] using equal
  · rintro ⟨i, before, equal⟩
    have active : i < a.trail.length := Nat.lt_of_lt_of_le before bound
    refine ⟨a.trail[i], ?_, ?_⟩
    · exact List.mem_iff_getElem.mpr ⟨i, by simp [List.length_take, bound, before], by simp⟩
    · simpa only [getElem!_pos a.trail i active] using equal

theorem falseBefore_iff {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {count : Nat} (bound : count ≤ m.solver.assigned) (lit : Lit) :
    FalseBefore a count lit ↔ Native.Analysis.FalseBefore m.solver count lit := by
  change (literalView lit).negate ∈ prefixLiterals a count ↔
    ∃ i, i < count ∧ m.solver.trail[i]! = lit
  rw [prefix_mem_iff (by simpa only [represented.trailLength] using bound)]
  constructor
  · rintro ⟨i, before, equal⟩
    have active := Nat.lt_of_lt_of_le before bound
    rw [represented.trail i active] at equal
    have views : literalView m.solver.trail[i]! = literalView lit := by
      simpa only [literalView, Std.Sat.Literal.negate, Bool.not_not] using
        congrArg (fun l : Literal => l.negate) equal
    exact ⟨i, before, view_injective views⟩
  · rintro ⟨i, before, equal⟩
    exact ⟨i, before, (represented.trail i (Nat.lt_of_lt_of_le before bound)).trans (by rw [equal])⟩

theorem trueBefore_iff {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {count : Nat} (bound : count ≤ m.solver.assigned) (lit : Lit) :
    TrueBefore a count lit ↔ Native.Analysis.TrueBefore m.solver count lit := by
  change literalView lit ∈ prefixLiterals a count ↔
    Native.Analysis.FalseBefore m.solver count lit.negate
  have opposite := falseBefore_iff represented bound lit.negate
  simpa only [FalseBefore, FalseIn, literalView_negate, Std.Sat.Literal.negate,
    Bool.not_not] using opposite

theorem trail_var {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {i : Nat} (before : i < m.solver.assigned) :
    a.trail[i]!.literal.1 = m.solver.trail[i]!.var := by
  exact congrArg Prod.fst (represented.trail i before)

theorem packed_toNative {s : CDCL.State} {entry : StoredClause} (packed : PackedClause s entry) :
    Native.Representation.PackedClause s entry.id entry.lits :=
  ⟨packed.header, packed.bound, packed.literals, packed.terminator, packed.declared⟩

theorem databaseFrom_toNative {s : CDCL.State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom s start entries) :
    Native.Representation.DatabaseFrom s start (entries.map toNativeEntry) := by
  induction entries generalizing start with
  | nil => exact layout
  | cons entry rest ih => exact ⟨layout.1, packed_toNative layout.2.1, ih layout.2.2⟩

theorem mapped_databaseView (entries : List StoredClause) :
    Native.Representation.databaseView (entries.map toNativeEntry) =
      databaseView (entries.map StoredClause.view) := by
  simp only [Native.Representation.databaseView, databaseView, List.map_map]
  rfl

theorem database_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) : Native.Representation.Database m.solver
      (w.original.map toNativeEntry) (w.learned.map toNativeEntry) := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [RepresentationWitness.entries, List.map_append] using
      databaseFrom_toNative represented.layout
  · simpa only [List.map_map, Function.comp_def, toNativeEntry] using represented.fixed
  · simpa only [List.length_map] using represented.count

theorem arrays_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) : Native.Representation.ArrayBounds m.solver :=
  ⟨represented.arrays.first, represented.arrays.marks, represented.arrays.reasons,
    represented.arrays.phases, represented.arrays.trail, represented.arrays.previous,
    represented.arrays.next⟩

theorem order_toNative {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) : Native.Representation.MTFOrder m.solver w.order :=
  represented.order

theorem stored_view_mem {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {entry : StoredClause} (member : entry ∈ w.entries) :
    entry.view ∈ a.database := by
  simp only [RepresentationWitness.entries, List.mem_append] at member
  rcases member with original | learned
  · exact List.mem_append_left _ (represented.original ▸ List.mem_map.mpr ⟨entry, original, rfl⟩)
  · exact List.mem_append_right _ (represented.learned ▸ List.mem_map.mpr ⟨entry, learned, rfl⟩)

end MicrosatLean.Verification.Implementation.Bridge
