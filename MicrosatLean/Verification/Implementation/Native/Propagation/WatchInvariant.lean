import MicrosatLean.Verification.Implementation.Native.Propagation.WatchLiteralLinks

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation

/-- A simultaneous ghost description of finite watch chains, genuine refs,
both slots of every long stored clause, and unique ownership by literal head.
Literal order is read from the current ghost database, after any permutation. -/
structure WatchCertificate (s : State) (entries : List StoredClause) (heads : Nat → List Nat) : Prop where
  links : ∀ lit, WatchLinks s lit (heads lit)
  references : ∀ lit ref, ref ∈ heads lit → StoredWatchRef entries ref
  covered : ∀ entry ∈ entries, 2 ≤ entry.lits.size →
    ClauseWatches heads entry.id entry.lits[0]! entry.lits[1]!
  unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other

theorem WatchCertificate.frameArrays {before after : State} {entries : List StoredClause}
    {heads : Nat → List Nat} (certificate : WatchCertificate before entries heads)
    (arena : after.arena = before.arena) (first : after.first = before.first) :
    WatchCertificate after entries heads :=
  ⟨fun lit => (certificate.links lit).frame (by rw [first]) (by intro ref _; simp only [State.db, arena]),
    certificate.references, certificate.covered, certificate.unique⟩

theorem WatchCertificate.entry {s : State} {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (certificate : WatchCertificate s (original ++ learned) heads)
    {lit : Lit} {ref : Nat} (member : ref ∈ heads lit) : WatchEntry s lit ref := by
  obtain ⟨entry, entryMember, id, wide⟩ := certificate.references lit ref member
  have packed := database.layout.packed entryMember
  have covered := certificate.covered entry entryMember wide
  have encoding : ref = 2 * entry.id ∨ ref = 2 * entry.id + 1 := by
    simp only [watchClause] at id
    omega
  have headMembership : ref ∈ heads entry.lits[0]! ∨ ref ∈ heads entry.lits[1]! := by
    rcases encoding with first | second
    · subst ref
      rcases covered.2 with forward | backward
      · exact Or.inl forward.1
      · exact Or.inr backward.1
    · subst ref
      rcases covered.2 with forward | backward
      · exact Or.inr forward.2
      · exact Or.inl backward.2
  unfold WatchEntry
  rw [id]
  refine ⟨packed.startLower, ?_, storedWatchRef_link_bound database ⟨entry, entryMember, id, wide⟩, ?_⟩
  · have upper := packed.endBound
    omega
  · rcases headMembership with first | second
    · left
      have read : s.db entry.id = entry.lits[0]! := by simpa using packed.literals 0 (by omega)
      exact read.trans (certificate.unique lit _ ref member first).symm
    · right
      exact (packed.literals 1 (by omega)).trans (certificate.unique lit _ ref member second).symm

/-- Proper slot coverage and unique head ownership reconstruct the stronger
WatchEntry component of every list after its pointer splice has been proved. -/
theorem WatchCertificate.watchLists {s : State} {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (certificate : WatchCertificate s (original ++ learned) heads) :
    ∀ lit, WatchList s lit (heads lit) := by
  intro lit
  have links := certificate.links lit
  refine ⟨links.1, links.2.1, ?_⟩
  intro i before
  have member : (heads lit).getD i 0 ∈ heads lit := by
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem before, Option.getD_some] using
      List.getElem_mem before
  exact ⟨certificate.entry database member, links.2.2 i before⟩

end MicrosatLean.Verification.Implementation.Native.Propagation
