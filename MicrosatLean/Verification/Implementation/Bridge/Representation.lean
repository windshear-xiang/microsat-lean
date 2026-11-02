import MicrosatLean.Verification.Invariant
import MicrosatLean.Verification.Implementation.Search.Concrete.MachineInvariant

namespace MicrosatLean.Verification.Implementation.Bridge

/-! Shared representation identities for the two invariant presentations. -/

theorem nodup_of_map {α β : Type} (f : α → β) {items : List α}
    (distinct : (items.map f).Nodup) : items.Nodup := by
  induction items with
  | nil => exact List.nodup_nil
  | cons head rest ih =>
    obtain ⟨absent, tail⟩ := List.nodup_cons.mp distinct
    exact List.nodup_cons.mpr ⟨fun member => absent (List.mem_map.mpr ⟨head, member, rfl⟩), ih tail⟩

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
    FalseBefore a count lit ↔ Analysis.FalseBefore m.solver count lit := by
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
    exact ⟨i, before, literalView_injective views⟩
  · rintro ⟨i, before, equal⟩
    exact ⟨i, before, (represented.trail i (Nat.lt_of_lt_of_le before bound)).trans (by rw [equal])⟩

theorem trueBefore_iff {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {count : Nat} (bound : count ≤ m.solver.assigned) (lit : Lit) :
    TrueBefore a count lit ↔ Analysis.TrueBefore m.solver count lit := by
  change literalView lit ∈ prefixLiterals a count ↔
    Analysis.FalseBefore m.solver count lit.negate
  have opposite := falseBefore_iff represented bound lit.negate
  simpa only [FalseBefore, FalseIn, literalView_negate, Std.Sat.Literal.negate,
    Bool.not_not] using opposite

theorem trail_var {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {i : Nat} (before : i < m.solver.assigned) :
    a.trail[i]!.literal.1 = m.solver.trail[i]!.var := by
  exact congrArg Prod.fst (represented.trail i before)

theorem mapped_databaseView (entries : List StoredClause) :
    Representation.databaseView (entries) =
      databaseView (entries.map Representation.StoredClause.view) := rfl

theorem database_concrete {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) : Representation.Database m.solver
      w.original w.learned :=
  ⟨represented.layout, represented.fixed, represented.count⟩

theorem stored_view_mem {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) {entry : StoredClause} (member : entry ∈ w.entries) :
    entry.view ∈ a.database := by
  simp only [RepresentationWitness.entries, List.mem_append] at member
  rcases member with original | learned
  · exact List.mem_append_left _ (represented.original ▸ List.mem_map.mpr ⟨entry, original, rfl⟩)
  · exact List.mem_append_right _ (represented.learned ▸ List.mem_map.mpr ⟨entry, learned, rfl⟩)

end MicrosatLean.Verification.Implementation.Bridge
