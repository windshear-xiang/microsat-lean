import MicrosatLean.Verification.Implementation.Native.Representation.Database

namespace MicrosatLean.Verification.Implementation.Native.Representation

open Std.Sat

theorem databaseView_sat_iff (entries : List StoredClause) (a : Nat → Bool) :
    CNF.Sat a (databaseView entries) ↔
      ∀ entry ∈ entries, CNF.Clause.Sat a entry.view := by
  constructor
  · intro satisfied entry member
    apply CNF.sat_of_mem satisfied
    change entry.view ∈ (entries.map StoredClause.view).toArray
    exact List.mem_toArray.mpr (List.mem_map.mpr ⟨entry, member, rfl⟩)
  · intro satisfied
    apply CNF.sat_of_all_mem_sat
    intro clause member
    change clause ∈ (entries.map StoredClause.view).toArray at member
    obtain ⟨entry, entryMember, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp member)
    exact satisfied entry entryMember

@[simp] theorem databaseView_nil : databaseView [] = CNF.empty := rfl

@[simp] theorem databaseView_append (left right : List StoredClause) :
    databaseView (left ++ right) = databaseView left ++ databaseView right := by
  rw [CNF.Internal.ext_iff, CNF.Internal.clauses_append]
  simp [databaseView]

@[simp] theorem databaseView_append_singleton (entries : List StoredClause) (entry : StoredClause) :
    databaseView (entries ++ [entry]) = (databaseView entries).add entry.view := by
  simp [databaseView, CNF.add]

/-- The original database represents the input exactly; every retained learned
clause follows from the input. Forgetting such clauses does not change models. -/
structure DatabaseMeaning (formula : CNF Nat) (original learned : List StoredClause) : Prop where
  original : CNF.BiEntails formula (databaseView original)
  learned : CNF.Entails formula (databaseView learned)

theorem DatabaseMeaning.combined {formula : CNF Nat} {original learned : List StoredClause}
    (meaning : DatabaseMeaning formula original learned) :
    CNF.BiEntails formula (databaseView (original ++ learned)) := by
  rw [databaseView_append]
  exact ⟨CNF.entails_append_of_entails meaning.original.1 meaning.learned,
    CNF.entails_trans CNF.append_entails_left meaning.original.2⟩

theorem DatabaseMeaning.entails_entry {formula : CNF Nat} {original learned : List StoredClause}
    (meaning : DatabaseMeaning formula original learned) {entry : StoredClause}
    (member : entry ∈ original ++ learned) : CNF.EntailsClause formula entry.view := by
  intro a model
  exact (databaseView_sat_iff _ a).mp (meaning.combined.1 a model) entry member

theorem DatabaseMeaning.addLearned {formula : CNF Nat} {original learned : List StoredClause}
    (meaning : DatabaseMeaning formula original learned) (entry : StoredClause)
    (entailed : CNF.EntailsClause formula entry.view) :
    DatabaseMeaning formula original (learned ++ [entry]) := by
  refine ⟨meaning.original, ?_⟩
  rw [databaseView_append_singleton]
  exact CNF.entails_add_iff.mpr ⟨meaning.learned, entailed⟩

/-- Clause identifiers may be relocated during compaction. Only their literal
views matter to model preservation; the runtime compactor must prove this
retained-view inclusion independently. -/
theorem DatabaseMeaning.forgetLearned {formula : CNF Nat}
    {original oldLearned newLearned : List StoredClause}
    (meaning : DatabaseMeaning formula original oldLearned)
    (retained : newLearned.map StoredClause.view ⊆ oldLearned.map StoredClause.view) :
    DatabaseMeaning formula original newLearned := by
  refine ⟨meaning.original, ?_⟩
  intro a model
  apply (databaseView_sat_iff _ a).mpr
  intro entry member
  have oldView := retained (List.mem_map.mpr ⟨entry, member, rfl⟩)
  obtain ⟨old, oldMember, same⟩ := List.mem_map.mp oldView
  have satisfied := (databaseView_sat_iff _ a).mp (meaning.learned a model) old oldMember
  simpa only [same] using satisfied

end MicrosatLean.Verification.Implementation.Native.Representation
