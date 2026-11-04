import MicrosatLean.Verification.Implementation.Reduction.Database
import MicrosatLean.Verification.Implementation.Propagation.WatchBounds

namespace MicrosatLean.Verification.Implementation.Reduction

open CDCL Representation Propagation Std.Sat

/-- The predecessor cell comes from an already visited genuine reference.
It is outside the unvisited suffix, so bypassing a learned reference cannot
change the next-pointer reads still needed by the executable loop. -/
private def PreviousReference (source remaining : List Nat) : Option Nat → Prop
  | none => True
  | some pos => ∃ ref ∈ source, ref ∉ remaining ∧ pos = watchLinkPos ref

theorem database_setWatchLink {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {ref : Nat}
    (proper : StoredWatchRef (original ++ learned) ref) (value : Nat) :
    Database { s with arena := s.arena.set! (watchLinkPos ref) value } original learned := by
  obtain ⟨entry, member, id, _⟩ := proper
  have position : watchLinkPos ref = entry.id - 2 + ref % 2 := by
    simp only [watchLinkPos, watchClause] at *
    rw [id]
  rw [position]
  exact database.setHeader member (ref % 2) value (by omega)

theorem watchLink_ne {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {left right : Nat}
    (leftProper : StoredWatchRef (original ++ learned) left)
    (rightProper : StoredWatchRef (original ++ learned) right) (different : left ≠ right) :
    watchLinkPos left ≠ watchLinkPos right :=
  fun same => different (storedWatchRef_link_injective database leftProper rightProper same)

/-- This invariant follows the exact mutable cursor, rather than assuming
that its next reference remains genuine after a pointer write. The suffix
chain and predecessor provenance establish that fact at every iteration.
No fuel-sufficiency premise is needed for read preservation. -/
private theorem watchFilter_loop_database {original learned : List StoredClause}
    (heads : Nat → List Nat) (lit : Lit) (source : List Nat) (protect : Nat → Prop)
    (sourceProper : ∀ ref ∈ source, StoredWatchRef (original ++ learned) ref)
    (protectedProper : ∀ other, protect other → ∀ ref ∈ heads other,
      StoredWatchRef (original ++ learned) ref)
    (separateHeads : ∀ other, protect other → lit ≠ other)
    (separateRefs : ∀ other, protect other → ∀ ref ∈ source, ref ∉ heads other)
    (indices : List Nat) (s : State) (remaining : List Nat) (previous : Option Nat)
    (database : Database s original learned) (chain : WatchChain s remaining)
    (nodup : remaining.Nodup) (included : remaining ⊆ source)
    (predecessor : PreviousReference source remaining previous)
    (protectedLinks : ∀ other, protect other → WatchLinks s other (heads other)) :
    let result := forIn (m := Id) indices (s, remaining.headD 0, previous) (watchFilterBody lit)
    Database result.1 original learned ∧
      ∀ other, protect other → WatchLinks result.1 other (heads other) := by
  induction indices generalizing s remaining previous with
  | nil => exact ⟨database, protectedLinks⟩
  | cons index indices ih =>
    rw [List.forIn_cons]
    simp only [bind, pure]
    cases remaining with
    | nil =>
      simpa only [List.headD_nil, watchFilterBody, beq_self_eq_true, ↓reduceIte, Id.run, pure]
        using And.intro database protectedLinks
    | cons ref rest =>
      have refMember : ref ∈ source := included (by simp)
      have proper := sourceProper ref refMember
      have nonzero := storedWatchRef_nonzero database proper
      have restIncluded : rest ⊆ source := fun _ member => included (List.mem_cons_of_mem ref member)
      have restNodup := (List.nodup_cons.mp nodup).2
      have next : s.db (watchLinkPos ref) = rest.headD 0 := chain.1
      by_cases retained : watchClause ref < s.fixed
      · have previousNext : PreviousReference source rest (some (watchLinkPos ref)) :=
          ⟨ref, refMember, (List.nodup_cons.mp nodup).1, rfl⟩
        simpa only [watchFilterBody, List.headD_cons, nonzero, beq_iff_eq, ↓reduceIte,
          retained, next, Id.run, pure] using
          ih s rest (some (watchLinkPos ref)) database chain.2 restNodup restIncluded
            previousNext protectedLinks
      · cases previous with
        | none =>
          let after := { s with first := s.first.set! lit (rest.headD 0) }
          have afterDatabase : Database after original learned := database.frame rfl rfl rfl rfl
          have afterChain : WatchChain after rest := chain.2.frame (fun _ _ => rfl)
          have afterLinks : ∀ other, protect other → WatchLinks after other (heads other) := by
            intro other isProtected
            apply (protectedLinks other isProtected).frame
            · exact Array.getElem!_set!_ne _ _ _ _ (separateHeads other isProtected)
            · intro old member
              rfl
          simpa only [watchFilterBody, List.headD_cons, nonzero, beq_iff_eq, ↓reduceIte,
            retained, next, Id.run, pure, after] using
            ih after rest none afterDatabase afterChain restNodup restIncluded trivial afterLinks
        | some pos =>
          obtain ⟨old, oldMember, oldAbsent, position⟩ := predecessor
          subst pos
          let after := { s with arena := s.arena.set! (watchLinkPos old) (rest.headD 0) }
          have oldProper := sourceProper old oldMember
          have afterDatabase : Database after original learned := database_setWatchLink database oldProper _
          have afterChain : WatchChain after rest := by
            apply chain.2.frame
            intro other member
            exact Array.getElem!_set!_ne _ _ _ _ (watchLink_ne database oldProper
              (sourceProper other (restIncluded member)) (fun equal =>
                oldAbsent (by simpa only [equal] using List.mem_cons_of_mem ref member)))
          have afterLinks : ∀ other, protect other → WatchLinks after other (heads other) := by
            intro other isProtected
            apply (protectedLinks other isProtected).frame (after := after) rfl
            intro watched member
            exact Array.getElem!_set!_ne _ _ _ _ (watchLink_ne database oldProper
              (protectedProper other isProtected watched member) (fun equal =>
                separateRefs other isProtected old oldMember (equal ▸ member)))
          have previousNext : PreviousReference source rest (some (watchLinkPos old)) :=
            ⟨old, oldMember, fun member => oldAbsent (List.mem_cons_of_mem ref member), rfl⟩
          simpa only [watchFilterBody, List.headD_cons, nonzero, beq_iff_eq, ↓reduceIte,
            retained, next, Id.run, pure, after] using
            ih after rest (some (watchLinkPos old)) afterDatabase afterChain restNodup
              restIncluded previousNext afterLinks

private theorem watchFilterList_database {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (heads : Nat → List Nat) (lit : Lit)
    (protect : Nat → Prop) (links : WatchLinks s lit (heads lit))
    (sourceProper : ∀ ref ∈ heads lit, StoredWatchRef (original ++ learned) ref)
    (protectedProper : ∀ other, protect other → ∀ ref ∈ heads other,
      StoredWatchRef (original ++ learned) ref)
    (separateHeads : ∀ other, protect other → lit ≠ other)
    (unique : ∀ other, protect other → ∀ ref ∈ heads lit, ref ∉ heads other)
    (protectedLinks : ∀ other, protect other → WatchLinks s other (heads other)) :
    Database (watchFilterList lit s).value original learned ∧
      ∀ other, protect other → WatchLinks (watchFilterList lit s).value other (heads other) := by
  unfold watchFilterList
  simp only [ForInStep.value_yield]
  rw [links.2.1, Std.Legacy.Range.forIn_eq_forIn_range']
  exact watchFilter_loop_database heads lit (heads lit) protect sourceProper protectedProper
    separateHeads unique _ s (heads lit) none database links.chain links.1
    (fun _ member => member) trivial protectedLinks

private theorem watchFilter_outer_database {original learned : List StoredClause}
    (heads : Nat → List Nat)
    (proper : ∀ lit ref, ref ∈ heads lit → StoredWatchRef (original ++ learned) ref)
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    (indices : List Nat) (distinct : indices.Nodup) (s : State)
    (database : Database s original learned)
    (links : ∀ lit ∈ indices, WatchLinks s lit (heads lit)) :
    Database (forIn (m := Id) indices s watchFilterList) original learned := by
  induction indices generalizing s with
  | nil => exact database
  | cons lit rest ih =>
    have separate (other : Nat) (member : other ∈ rest) : lit ≠ other := by
      intro equal
      exact (List.nodup_cons.mp distinct).1 (equal ▸ member)
    have filtered := watchFilterList_database database heads lit (fun other => other ∈ rest)
      (links lit (by simp)) (proper lit) (fun other _ => proper other) separate
      (by
        intro other member ref sourceMember targetMember
        exact separate other member (unique lit other ref sourceMember targetMember))
      (fun other member => links other (List.mem_cons_of_mem lit member))
    rw [List.forIn_cons]
    simp only [watchFilterList, bind]
    apply ih (List.nodup_cons.mp distinct).2 _ filtered.1 filtered.2

/-- Genuine finite watch lists and unique head ownership imply that the
actual filter writes only genuine headers. Consequently it preserves the
entire original and learned packed database, before any compaction begins. -/
theorem removeLearnedWatches_database {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) :
    Database s.removeLearnedWatches original learned := by
  rw [removeLearnedWatches_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
  exact watchFilter_outer_database heads certificate.references certificate.unique _
    (List.nodup_range' 1 (by decide)) s database (fun lit _ => certificate.links lit)

/-- The original-read obligation now follows from the actual watch
certificate and database, including each zero terminator. -/
theorem originalReads_of_watchCertificate {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) : OriginalReads s original := by
  have after := removeLearnedWatches_database database certificate
  intro entry member i within
  have beforePacked := database.layout.packed (List.mem_append_left learned member)
  have afterPacked := after.layout.packed (List.mem_append_left learned member)
  by_cases literal : i < entry.lits.size
  · exact (afterPacked.literals i literal).trans (beforePacked.literals i literal).symm
  · have endIndex : i = entry.lits.size := by omega
    subst i
    exact afterPacked.terminator.trans beforePacked.terminator.symm

/-- Semantic database preservation for the actual reducer, with the former
read-frame premise discharged by the concrete watch representation. -/
theorem reduceDB_database_meaning_of_watchCertificate {formula : Std.Sat.CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat}
    (database : Database s original learned) (meaning : DatabaseMeaning formula original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (k : Nat) :
    ∃ kept, Database (s.reduceDB k) original kept ∧ DatabaseMeaning formula original kept ∧
      RelocationMatches (compactionResult s k).2.1
        (retainedEntries s (lockedReasons s) k learned) kept :=
  reduceDB_database_meaning_of_originalReads database meaning
    (originalReads_of_watchCertificate database certificate) k

end MicrosatLean.Verification.Implementation.Reduction
