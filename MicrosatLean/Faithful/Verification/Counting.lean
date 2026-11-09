/-!
# Counting distinct values

Pigeonhole facts used to bound the trail (at most `n` distinct variables) and,
later, the number of distinct lemmas.
-/

namespace MicrosatLean.Faithful.Verification

/-- `m` distinct values from `[1, N]` that all differ from some `v` in `[1, N]` are
fewer than `N`. Used when a new variable is assigned: the trail stays within `n`. -/
theorem card_lt_of_distinct {N m : Nat} (f : Nat → Nat)
    (hrange : ∀ i < m, 1 ≤ f i ∧ f i ≤ N) (hdist : ∀ i < m, ∀ j < m, f i = f j → i = j)
    {v : Nat} (hv : 1 ≤ v ∧ v ≤ N) (hmiss : ∀ i < m, f i ≠ v) : m < N := by
  have hnodup : ((List.range m).map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab heq =>
      hab (hdist a (List.mem_range.mp ha) b (List.mem_range.mp hb) heq)) List.nodup_range
  have hsub : (List.range m).map f ⊆ (List.range' 1 N).erase v := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    have hi := List.mem_range.mp hi
    exact (List.mem_erase_of_ne (hmiss i hi)).mpr (List.mem_range'_1.mpr (by have := hrange i hi; omega))
  have := hnodup.length_le_of_subset hsub
  rw [List.length_map, List.length_range, List.length_erase_of_mem (List.mem_range'_1.mpr (by omega)),
    List.length_range'] at this
  omega

/-- `m` distinct values from `[1, N]` are at most `N`. -/
theorem card_le_of_distinct {N m : Nat} (f : Nat → Nat)
    (hrange : ∀ i < m, 1 ≤ f i ∧ f i ≤ N) (hdist : ∀ i < m, ∀ j < m, f i = f j → i = j) : m ≤ N := by
  have hnodup : ((List.range m).map f).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb hab heq =>
      hab (hdist a (List.mem_range.mp ha) b (List.mem_range.mp hb) heq)) List.nodup_range
  have hsub : (List.range m).map f ⊆ List.range' 1 N := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hx
    exact List.mem_range'_1.mpr (by have := hrange i (List.mem_range.mp hi); omega)
  have := hnodup.length_le_of_subset hsub
  simpa using this

end MicrosatLean.Faithful.Verification
