import MicrosatLean.Verification.Implementation.Native.Propagation.WatchCursor

namespace MicrosatLean.Verification.Implementation.Native.Propagation

open CDCL Representation

/-- Compose the actual pointer splices at every head. The arena may currently
have its literal cells reoriented; only genuine refs and pointer chains matter
until the completed clause coverage is reattached to the certificate. -/
theorem rewireWatch_all_links {s : State} {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (links : ∀ lit, WatchLinks s lit (heads lit))
    (proper : ∀ lit ref, ref ∈ heads lit → StoredWatchRef (original ++ learned) ref)
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    {lit newLit : Lit} {previous ref : Nat} {rest : List Nat}
    (cursor : WatchCursor heads lit previous (ref :: rest)) (different : lit ≠ newLit)
    (headBound : lit < s.first.size) (targetBound : newLit < s.first.size) :
    let arrays := rewireWatch s.arena s.first lit newLit ref previous
    let after := restoreWatchArrays s arrays.1 arrays.2
    ∀ other, WatchLinks after other (moveHeads heads newLit ref other) := by
  dsimp only
  have current := cursor.member
  have currentProper := proper lit ref current
  have fresh : ref ∉ heads newLit := fun member => different (unique lit newLit ref current member)
  cases cursor with
  | head _ source =>
    have currentLinks : WatchLinks s lit (ref :: rest) := by simpa only [source] using links lit
    have moved := rewireWatch_head_links_proper database currentLinks (links newLit) (by
      intro old member
      rcases List.mem_cons.mp member with same | remaining
      · subst old
        exact currentProper
      · rcases List.mem_append.mp remaining with before | target
        · exact proper lit old (by simp [source, before])
        · exact proper newLit old target) different fresh headBound targetBound
    intro other
    by_cases atSource : other = lit
    · subst other
      simpa only [moveHeads, different, ite_false, source, List.erase_cons_head] using moved.1
    · by_cases atTarget : other = newLit
      · subst other
        simpa only [moveHeads, ite_true] using moved.2
      · rw [moveHeads_other unique lit newLit other ref current atSource atTarget]
        apply rewireWatch_head_other_links (links other) (Ne.symm atSource) (Ne.symm atTarget)
        intro old member equal
        have same := storedWatchRef_link_injective database currentProper (proper other old member) equal
        subst old
        exact atSource (unique lit other ref current member).symm
  | after previous initial _ nonzero source =>
    have previousMember : previous ∈ heads lit := by simp [source]
    have previousProper := proper lit previous previousMember
    have previousFresh : previous ∉ heads newLit :=
      fun member => different (unique lit newLit previous previousMember member)
    have currentLinks : WatchLinks s lit (initial ++ previous :: ref :: rest) := by
      simpa only [source] using links lit
    have moved := rewireWatch_nonhead_links_proper database currentLinks (links newLit) (by
      intro old member
      rcases List.mem_append.mp member with before | target
      · exact proper lit old (by simpa only [source] using before)
      · exact proper newLit old target) different fresh previousFresh targetBound
    have parts := List.nodup_append.mp currentLinks.1
    have absent : ref ∉ initial := fun member => parts.2.2 ref member ref (by simp) rfl
    have ne : previous ≠ ref := fun same => (List.nodup_cons.mp parts.2.1).1 (by simp [same])
    have sourceMoved : moveHeads heads newLit ref lit = initial ++ previous :: rest := by
      simp only [moveHeads, different, ite_false, source]
      rw [List.erase_append_right _ absent, List.erase_cons_tail (by simpa using ne), List.erase_cons_head]
    intro other
    by_cases atSource : other = lit
    · subst other
      simpa only [sourceMoved] using moved.1
    · by_cases atTarget : other = newLit
      · subst other
        simpa only [moveHeads, ite_true] using moved.2
      · rw [moveHeads_other unique lit newLit other ref current atSource atTarget]
        apply rewireWatch_nonhead_other_links (links other) nonzero (Ne.symm atTarget)
        intro old member
        constructor
        · intro equal
          have same := storedWatchRef_link_injective database previousProper (proper other old member) equal
          subst old
          exact atSource (unique lit other previous previousMember member).symm
        · intro equal
          have same := storedWatchRef_link_injective database currentProper (proper other old member) equal
          subst old
          exact atSource (unique lit other ref current member).symm

end MicrosatLean.Verification.Implementation.Native.Propagation
