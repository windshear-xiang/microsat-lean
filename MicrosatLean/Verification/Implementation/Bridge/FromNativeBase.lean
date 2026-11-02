import MicrosatLean.Verification.Implementation.Bridge.ToNativeBase
import MicrosatLean.Verification.Implementation.Native.Search.MachineInvariant
import MicrosatLean.Verification.Implementation.Native.Propagation.Database

namespace MicrosatLean.Verification.Implementation.Bridge

private abbrev NativeEntry := Native.Representation.StoredClause

def nativeWitness (original learned : List NativeEntry) (heads : Lit → List Nat)
    (order : List Nat) : RepresentationWitness :=
  ⟨original.map fromNativeEntry, learned.map fromNativeEntry, heads, order⟩

def nativeReason (s : CDCL.State) (entries : List NativeEntry) (i : Nat) : Option Clause :=
  if s.reason s.trail[i]! = 0 then none
  else (entries.find? (fun entry => entry.id == s.reason s.trail[i]!)).map Native.Representation.StoredClause.view

def nativeTrail (s : CDCL.State) (entries : List NativeEntry) : List TrailEntry :=
  (List.range s.assigned).map fun i => ⟨(literalView s.trail[i]!).negate, nativeReason s entries i⟩

def nativeState (s : CDCL.State) (original learned : List NativeEntry) : LogicalState :=
  ⟨s.nVars, original.map Native.Representation.StoredClause.view,
    learned.map Native.Representation.StoredClause.view,
    nativeTrail s (original ++ learned), s.forced⟩

@[simp] theorem nativeTrail_length (s : CDCL.State) (entries : List NativeEntry) :
    (nativeTrail s entries).length = s.assigned := by simp [nativeTrail]

theorem nativeTrail_get (s : CDCL.State) (entries : List NativeEntry) {i : Nat}
    (before : i < s.assigned) :
    (nativeTrail s entries)[i]! =
      ⟨(literalView s.trail[i]!).negate, nativeReason s entries i⟩ := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by simpa using before)]
  simp [nativeTrail]

theorem nativeReason_some {s : CDCL.State} {entries : List NativeEntry}
    (proper : Native.Representation.ReasonDatabase s entries) {i : Nat}
    (before : i < s.assigned) (nonzero : s.reason s.trail[i]! ≠ 0) :
    ∃ entry ∈ entries, s.reason s.trail[i]! = entry.id ∧
      nativeReason s entries i = some entry.view := by
  obtain ⟨old, member, id⟩ := proper i before nonzero
  cases found : entries.find? (fun entry => entry.id == s.reason s.trail[i]!) with
  | none =>
    have absent := (List.find?_eq_none.mp found) old member
    exact False.elim (absent (by simp only [id, beq_self_eq_true]))
  | some entry =>
    have selected : entry.id = s.reason s.trail[i]! := by
      simpa only [beq_iff_eq] using List.find?_some found
    exact ⟨entry, List.mem_of_find?_eq_some found, selected.symm,
      by simp only [nativeReason, nonzero, ↓reduceIte, found, Option.map_some]⟩

theorem nativeReason_none_iff {s : CDCL.State} {entries : List NativeEntry}
    (proper : Native.Representation.ReasonDatabase s entries) {i : Nat}
    (before : i < s.assigned) :
    nativeReason s entries i = none ↔ s.reason s.trail[i]! = 0 := by
  constructor
  · intro absent
    by_cases zero : s.reason s.trail[i]! = 0
    · exact zero
    · obtain ⟨entry, _, _, selected⟩ := nativeReason_some proper before zero
      rw [absent] at selected
      cases selected
  · intro zero
    simp only [nativeReason, zero, ↓reduceIte]

theorem native_layout {s : CDCL.State} {start : Nat} {entries : List NativeEntry}
    (layout : Native.Representation.DatabaseFrom s start entries) :
    DatabaseFrom s start (entries.map fromNativeEntry) := by
  induction entries generalizing start with
  | nil => exact layout
  | cons entry rest ih =>
    obtain ⟨id, packed, tail⟩ := layout
    exact ⟨id, ⟨packed.startLower, packed.endBound, packed.literals, packed.terminator,
      fun lit member => ⟨by have := (packed.wellFormed lit member).1; omega,
        (packed.wellFormed lit member).2⟩⟩, ih tail⟩

private theorem getD_mem {α : Type} [Inhabited α] (items : List α) (i : Nat)
    (before : i < items.length) : items.getD i default ∈ items := by
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem before, Option.getD_some]
    using List.getElem_mem before

theorem native_rep {input : CNF} {m : CDCL.Machine}
    {original learned : List NativeEntry} {heads : Lit → List Nat} {rank : Lit → Nat}
    (base : Native.Search.StateCertificate input m.solver original learned heads rank)
    {order : List Nat} (ordered : Native.Representation.MTFOrder m.solver order) :
    Rep m (nativeState m.solver original learned) (nativeWitness original learned heads order) := by
  let s := m.solver
  let entries := original ++ learned
  have members : (nativeWitness original learned heads order).entries = entries.map fromNativeEntry := by
    simp [nativeWitness, RepresentationWitness.entries, entries]
  have size := base.database.layout.size
  refine ⟨rfl, ⟨base.arrays.firstSize, base.arrays.marksSize, base.arrays.reasonsSize,
    base.arrays.phasesSize, base.arrays.trailSize, base.arrays.previousSize, base.arrays.nextSize⟩,
    by omega, ?_, ?_, by simpa [nativeWitness] using base.database.learnedCount,
    by simp only [nativeState, nativeWitness, List.map_map]; rfl,
    by simp only [nativeState, nativeWitness, List.map_map]; rfl,
    nativeTrail_length _ _, rfl,
    ⟨base.bounds.forcedProcessed, base.bounds.processedAssigned, base.bounds.assignedVars⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [members]
    exact native_layout base.database.layout
  · simpa only [nativeWitness, List.map_map, fromNativeEntry, Function.comp_def]
      using base.database.fixed
  · intro i before
    exact congrArg TrailEntry.literal (nativeTrail_get _ _ before)
  · intro i before
    exact (base.active i before).2
  · intro lit
    constructor
    · exact base.marked lit
    · rintro ⟨i, before, rfl⟩
      exact (base.active i before).2.1
  · intro i before
    have bounded : i < s.assigned := by simpa only [nativeState, nativeTrail_length] using before
    change s.phases[(nativeTrail s entries)[i]!.literal.1]! = (nativeTrail s entries)[i]!.literal.2
    rw [nativeTrail_get _ _ bounded]
    have phase := base.phases i bounded
    change s.phases[s.trail[i]!.var]! = (s.trail[i]! % 2 == 1) at phase
    rcases Nat.mod_two_eq_zero_or_one s.trail[i]! with even | odd
    · simpa [literalView, Std.Sat.Literal.negate, even] using phase
    · simpa [literalView, Std.Sat.Literal.negate, odd] using phase
  · intro i before
    change match (nativeTrail s entries)[i]!.reason with
      | none => s.reason s.trail[i]! = 0
      | some clause => ∃ entry ∈ (nativeWitness original learned heads order).entries,
          entry.id = s.reason s.trail[i]! ∧ entry.view = clause
    rw [nativeTrail_get _ _ before]
    by_cases zero : s.reason s.trail[i]! = 0
    · have absent : nativeReason s entries i = none := by simp only [nativeReason, zero, ↓reduceIte]
      change match nativeReason s entries i with
        | none => s.reason s.trail[i]! = 0
        | some clause => ∃ entry ∈ (nativeWitness original learned heads order).entries,
            entry.id = s.reason s.trail[i]! ∧ entry.view = clause
      rw [absent]
      exact zero
    · obtain ⟨entry, member, id, selected⟩ := nativeReason_some base.reasons before zero
      rw [selected]
      exact ⟨fromNativeEntry entry, by rw [members]; exact List.mem_map.mpr ⟨entry, member, rfl⟩,
        id.symm, rfl⟩
  · constructor
    · intro lit
      have links := base.watches.links lit
      refine ⟨links.1, links.2.1, ?_⟩
      intro i before
      let ref := (heads lit).getD i 0
      have member : ref ∈ heads lit := getD_mem (heads lit) i before
      have proper := base.watches.references lit ref member
      obtain ⟨entry, stored, id, _⟩ := proper
      have lower := (base.database.layout.packed stored).startLower
      refine ⟨?_, Native.Propagation.storedWatchRef_link_bound base.database
        (base.watches.references lit ref member), links.2.2 i before⟩
      intro zero
      change ref = 0 at zero
      change CDCL.watchClause ref = entry.id at id
      rw [zero] at id
      simp only [CDCL.watchClause, Nat.zero_div] at id
      omega
    · intro lit ref member
      obtain ⟨entry, stored, id, width⟩ := base.watches.references lit ref member
      exact ⟨fromNativeEntry entry, by rw [members]; exact List.mem_map.mpr ⟨entry, stored, rfl⟩,
        id, width⟩
    · intro entry stored width
      rw [members] at stored
      obtain ⟨old, member, rfl⟩ := List.mem_map.mp stored
      exact base.watches.covered old member width
    · exact base.watches.unique
  · refine ⟨ordered.1, ?_, ordered.2.2.1, ordered.2.2.2⟩
    intro var
    simpa only [nativeWitness, Nat.lt_iff_add_one_le, Nat.zero_add] using ordered.2.1 var

end MicrosatLean.Verification.Implementation.Bridge
