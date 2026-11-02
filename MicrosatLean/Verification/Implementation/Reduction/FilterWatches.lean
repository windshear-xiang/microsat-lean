import MicrosatLean.Verification.Implementation.Reduction.Reasons

namespace MicrosatLean.Verification.Implementation.Reduction

open CDCL Representation Propagation

def originalWatchHeads (fixed : Nat) (heads : Nat → List Nat) (lit : Lit) : List Nat :=
  (heads lit).filter (fun ref => decide (watchClause ref < fixed))

private def FilterPredecessor (accumulated : List Nat) (previous : Option Nat) : Prop :=
  (accumulated = [] ∧ previous = none) ∨
    ∃ initial ref, accumulated = initial ++ [ref] ∧ previous = some (watchLinkPos ref)

private theorem removeWatch_head {s : State} {lit ref : Nat} {rest : List Nat}
    (links : WatchLinks s lit (ref :: rest)) (bound : lit < s.first.size) :
    WatchLinks { s with first := s.first.set! lit (rest.headD 0) } lit rest := by
  refine ⟨(List.nodup_cons.mp links.1).2, Array.getElem!_set!_self _ _ _ bound, ?_⟩
  exact (watchChain_iff rest).mp (links.chain.2.frame (fun _ _ => rfl))

private theorem removeWatch_nonhead {s : State} {original learned : List StoredClause}
    (database : Database s original learned) {lit previous ref : Nat} {initial rest : List Nat}
    (links : WatchLinks s lit (initial ++ previous :: ref :: rest))
    (proper : ∀ old ∈ initial ++ previous :: ref :: rest, StoredWatchRef (original ++ learned) old) :
    WatchLinks { s with arena := s.arena.set! (watchLinkPos previous) (rest.headD 0) }
      lit (initial ++ previous :: rest) := by
  have previousProper := proper previous (by simp)
  have parts := List.nodup_append.mp links.1
  have previousAbsent : previous ∉ initial ++ rest := by
    intro member
    rcases List.mem_append.mp member with before | after
    · exact parts.2.2 previous before previous (by simp) rfl
    · exact (List.nodup_cons.mp parts.2.1).1 (List.mem_cons_of_mem ref after)
  let after := { s with arena := s.arena.set! (watchLinkPos previous) (rest.headD 0) }
  have chain : WatchChain after (initial ++ previous :: rest) := by
    apply links.chain.splice initial previous ref rest
    · exact Array.getElem!_set!_self _ _ _ (storedWatchRef_link_bound database previousProper)
    · intro old member
      apply Array.getElem!_set!_ne
      apply watchLink_ne database previousProper (proper old (by
        rcases List.mem_append.mp member with before | after
        · exact List.mem_append_left _ before
        · exact List.mem_append_right _ (by simp [after])))
      intro equal
      exact previousAbsent (equal ▸ member)
  have sublist : (initial ++ previous :: rest).Sublist (initial ++ previous :: ref :: rest) :=
    (List.Sublist.cons_cons previous (List.Sublist.cons ref (List.Sublist.refl rest))).append_left initial
  refine ⟨sublist.nodup links.1, ?_, (watchChain_iff _).mp chain⟩
  exact links.2.1.trans (by cases initial <;> rfl)

/-- The real inner loop traverses its initial suffix exactly once. A finite
genuine list supplies enough arena-sized fuel, and each bypass preserves the
processed prefix and every other protected head. -/
private theorem filterLoop_exact {original learned : List StoredClause}
    (heads : Nat → List Nat) (lit fixed : Nat) (source : List Nat) (protect : Nat → Prop)
    (sourceProper : ∀ ref ∈ source, StoredWatchRef (original ++ learned) ref)
    (protectedProper : ∀ other, protect other → ∀ ref ∈ heads other,
      StoredWatchRef (original ++ learned) ref)
    (separateHeads : ∀ other, protect other → lit ≠ other)
    (separateRefs : ∀ other, protect other → ∀ ref ∈ source, ref ∉ heads other)
    (remaining : List Nat) (accumulated : List Nat) (s : State) (previous : Option Nat)
    (fuel index : Nat) (budget : remaining.length < fuel)
    (database : Database s original learned) (fixedEq : s.fixed = fixed)
    (links : WatchLinks s lit (accumulated ++ remaining))
    (included : accumulated ++ remaining ⊆ source)
    (predecessor : FilterPredecessor accumulated previous) (headBound : lit < s.first.size)
    (protectedLinks : ∀ other, protect other → WatchLinks s other (heads other)) :
    let result := forIn (m := Id) (List.range' index fuel)
      (s, remaining.headD 0, previous) (watchFilterBody lit)
    Database result.1 original learned ∧
      WatchLinks result.1 lit (accumulated ++ remaining.filter (fun ref => decide (watchClause ref < fixed))) ∧
      (∀ other, protect other → WatchLinks result.1 other (heads other)) ∧
      result.2.1 = 0 ∧ result.1.first.size = s.first.size := by
  induction remaining generalizing accumulated s previous fuel index with
  | nil =>
    cases fuel with
    | zero => simp at budget
    | succ fuel =>
      rw [List.range'_succ, List.forIn_cons]
      simp only [watchFilterBody, List.headD_nil, beq_self_eq_true, ↓reduceIte, Id.run,
        pure, bind, List.filter_nil, List.append_nil]
      exact ⟨database, by simpa only [List.append_nil] using links, protectedLinks, by simp⟩
  | cons ref rest ih =>
    cases fuel with
    | zero => simp at budget
    | succ fuel =>
      have member : ref ∈ source := included (List.mem_append_right _ (by simp))
      have proper := sourceProper ref member
      have nonzero := storedWatchRef_nonzero database proper
      have suffix := links.chain.suffix accumulated (ref :: rest)
      have next : s.db (watchLinkPos ref) = rest.headD 0 := suffix.1
      have restBudget : rest.length < fuel := by simp only [List.length_cons] at budget; omega
      rw [List.range'_succ, List.forIn_cons]
      simp only [bind, pure]
      by_cases retained : watchClause ref < fixed
      · have nextLinks : WatchLinks s lit ((accumulated ++ [ref]) ++ rest) := by
          simpa only [List.append_assoc, List.singleton_append] using links
        have nextIncluded : (accumulated ++ [ref]) ++ rest ⊆ source := by
          simpa only [List.append_assoc, List.singleton_append] using included
        have result := ih (accumulated ++ [ref]) s (some (watchLinkPos ref)) fuel (index + 1)
          restBudget database fixedEq nextLinks nextIncluded (Or.inr ⟨accumulated, ref, rfl, rfl⟩)
          headBound protectedLinks
        have actualRetained : watchClause ref < s.fixed := by simpa only [fixedEq] using retained
        simpa only [watchFilterBody, List.headD_cons, nonzero, beq_iff_eq, ↓reduceIte,
          actualRetained, next, Id.run, pure, List.filter_cons, retained, decide_true,
          List.append_assoc, List.singleton_append] using result
      · have currentProper : ∀ old ∈ accumulated ++ ref :: rest,
            StoredWatchRef (original ++ learned) old := fun old oldMember => sourceProper old (included oldMember)
        have actualRemoved : ¬watchClause ref < s.fixed := by simpa only [fixedEq] using retained
        rcases predecessor with ⟨rfl, rfl⟩ | ⟨initial, old, rfl, rfl⟩
        · let after := { s with first := s.first.set! lit (rest.headD 0) }
          have afterDatabase : Database after original learned := database.frame rfl rfl rfl rfl
          have afterLinks : WatchLinks after lit ([] ++ rest) := by
            exact removeWatch_head links headBound
          have others : ∀ other, protect other → WatchLinks after other (heads other) := by
            intro other isProtected
            apply (protectedLinks other isProtected).frame
            · exact Array.getElem!_set!_ne _ _ _ _ (separateHeads other isProtected)
            · intro watched watchedMember
              rfl
          have result := ih [] after none fuel (index + 1) restBudget afterDatabase fixedEq
            afterLinks (fun _ restMember => included (List.mem_cons_of_mem ref restMember))
            (Or.inl ⟨rfl, rfl⟩) (by simpa only [after, Array.size_set!] using headBound) others
          simpa only [watchFilterBody, List.headD_cons, nonzero, beq_iff_eq, ↓reduceIte,
            actualRemoved, next, Id.run, pure, List.filter_cons, retained, decide_false,
            Bool.false_eq_true, List.nil_append, after, Array.size_set!] using result
        · let after := { s with arena := s.arena.set! (watchLinkPos old) (rest.headD 0) }
          have oldMember : old ∈ source := included (by simp)
          have oldProper := sourceProper old oldMember
          have afterDatabase : Database after original learned := database_setWatchLink database oldProper _
          have afterLinks : WatchLinks after lit ((initial ++ [old]) ++ rest) := by
            have beforeLinks : WatchLinks s lit (initial ++ old :: ref :: rest) := by
              simpa only [List.append_assoc, List.singleton_append] using links
            have properAll : ∀ watched ∈ initial ++ old :: ref :: rest,
                StoredWatchRef (original ++ learned) watched := by
              simpa only [List.append_assoc, List.singleton_append] using currentProper
            simpa only [List.append_assoc, List.singleton_append] using
              removeWatch_nonhead database beforeLinks properAll
          have others : ∀ other, protect other → WatchLinks after other (heads other) := by
            intro other isProtected
            apply (protectedLinks other isProtected).frame (after := after) rfl
            intro watched watchedMember
            exact Array.getElem!_set!_ne _ _ _ _ (watchLink_ne database oldProper
              (protectedProper other isProtected watched watchedMember) (fun equal =>
                separateRefs other isProtected old oldMember (equal ▸ watchedMember)))
          have nextIncluded : (initial ++ [old]) ++ rest ⊆ source := by
            intro watched watchedMember
            apply included
            simp only [List.mem_append, List.mem_cons] at watchedMember ⊢
            rcases watchedMember with (before | same) | tail
            · exact Or.inl (Or.inl before)
            · exact Or.inl (Or.inr same)
            · exact Or.inr (Or.inr tail)
          have result := ih (initial ++ [old]) after (some (watchLinkPos old)) fuel (index + 1)
            restBudget afterDatabase fixedEq afterLinks nextIncluded (Or.inr ⟨initial, old, rfl, rfl⟩)
            headBound others
          simpa only [watchFilterBody, List.headD_cons, nonzero, beq_iff_eq, ↓reduceIte,
            actualRemoved, next, Id.run, pure, List.filter_cons, retained, decide_false,
            Bool.false_eq_true, after] using result

private def filteredHeads (fixed : Nat) (indices : List Nat) (heads : Nat → List Nat) (lit : Lit) : List Nat :=
  if lit ∈ indices then originalWatchHeads fixed heads lit else heads lit

private def filterHead (fixed : Nat) (heads : Nat → List Nat) (selected lit : Lit) : List Nat :=
  if lit = selected then originalWatchHeads fixed heads lit else heads lit

private theorem filterHead_subset (fixed : Nat) (heads : Nat → List Nat) (selected lit : Lit) :
    filterHead fixed heads selected lit ⊆ heads lit := by
  unfold filterHead originalWatchHeads
  split
  · exact fun _ member => (List.mem_filter.mp member).1
  · exact fun _ member => member

private theorem filterList_exact {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (heads : Nat → List Nat)
    (links : ∀ lit, WatchLinks s lit (heads lit))
    (proper : ∀ lit ref, ref ∈ heads lit → StoredWatchRef (original ++ learned) ref)
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    (lit : Lit) (headBound : lit < s.first.size) :
    Database (watchFilterList lit s).value original learned ∧
      (∀ other, WatchLinks (watchFilterList lit s).value other (filterHead s.fixed heads lit other)) ∧
      (watchFilterList lit s).value.first.size = s.first.size := by
  have result := filterLoop_exact heads lit s.fixed (heads lit) (fun other => lit ≠ other)
    (proper lit) (fun other _ => proper other) (fun _ different => different)
    (fun other different ref source target => different (unique lit other ref source target))
    (heads lit) [] s none s.arena.size 0
    (watchLinks_length_lt_arena database (links lit) (proper lit)) database rfl (links lit)
    (fun _ member => member) (Or.inl ⟨rfl, rfl⟩) headBound (fun other _ => links other)
  have execute : (watchFilterList lit s).value =
      (forIn (m := Id) (List.range' 0 s.arena.size)
        (s, (heads lit).headD 0, none) (watchFilterBody lit)).1 := by
    simp only [watchFilterList, ForInStep.value_yield, (links lit).2.1,
      Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one]
  rw [execute]
  refine ⟨result.1, ?_, result.2.2.2.2⟩
  intro other
  by_cases same : other = lit
  · subst other
    simpa only [filterHead, ite_true, originalWatchHeads, List.nil_append] using result.2.1
  · simpa only [filterHead, same, ite_false] using result.2.2.1 other (Ne.symm same)

private theorem filteredHeads_update (fixed : Nat) (heads : Nat → List Nat) (lit : Lit)
    (rest : List Nat) (absent : lit ∉ rest) :
    filteredHeads fixed rest (filterHead fixed heads lit) = filteredHeads fixed (lit :: rest) heads := by
  funext other
  by_cases same : other = lit
  · subst other
    simp only [filteredHeads, filterHead, absent, ↓reduceIte, List.mem_cons_self]
  · by_cases member : other ∈ rest <;>
      simp only [filteredHeads, filterHead, originalWatchHeads, same, member, List.mem_cons,
        or_false, false_or, ↓reduceIte]

private theorem filterOuter_exact {original learned : List StoredClause}
    (indices : List Nat) (distinct : indices.Nodup) (s : State) (heads : Nat → List Nat)
    (database : Database s original learned) (links : ∀ lit, WatchLinks s lit (heads lit))
    (proper : ∀ lit ref, ref ∈ heads lit → StoredWatchRef (original ++ learned) ref)
    (unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other)
    (bounded : ∀ lit ∈ indices, lit < s.first.size) :
    let after := forIn (m := Id) indices s watchFilterList
    Database after original learned ∧
      (∀ lit, WatchLinks after lit (filteredHeads s.fixed indices heads lit)) ∧
      after.first.size = s.first.size := by
  induction indices generalizing s heads with
  | nil => exact ⟨database, links, rfl⟩
  | cons lit rest ih =>
    let after := (watchFilterList lit s).value
    let updated := filterHead s.fixed heads lit
    have step := filterList_exact database heads links proper unique lit (bounded lit (by simp))
    have nextProper : ∀ other ref, ref ∈ updated other → StoredWatchRef (original ++ learned) ref := by
      intro other ref member
      exact proper other ref (filterHead_subset _ _ _ _ member)
    have nextUnique : ∀ left right ref, ref ∈ updated left → ref ∈ updated right → left = right := by
      intro left right ref leftMember rightMember
      exact unique left right ref (filterHead_subset _ _ _ _ leftMember) (filterHead_subset _ _ _ _ rightMember)
    have fixed : after.fixed = s.fixed := step.1.fixed.trans database.fixed.symm
    have tail := ih (List.nodup_cons.mp distinct).2 after updated step.1 step.2.1 nextProper nextUnique (by
      intro other member
      rw [step.2.2]
      exact bounded other (List.mem_cons_of_mem lit member))
    rw [List.forIn_cons]
    simp only [watchFilterList, bind]
    refine ⟨tail.1, ?_, tail.2.2.trans step.2.2⟩
    intro other
    have same := congrFun (filteredHeads_update s.fixed heads lit rest (List.nodup_cons.mp distinct).1) other
    have list := tail.2.1 other
    rw [fixed] at list
    change WatchLinks _ other (filteredHeads s.fixed rest (filterHead s.fixed heads lit) other) at list
    rw [same] at list
    exact list

private theorem watchHead_bound {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (arrays : ArrayBounds s)
    {lit ref : Nat} (member : ref ∈ heads lit) : 2 ≤ lit ∧ lit < s.first.size := by
  obtain ⟨entry, stored, id, wide⟩ := certificate.references lit ref member
  have packed := database.layout.packed stored
  have watched := (certificate.entry database member).2.2.2
  rw [id] at watched
  have literal : LiteralBound s.nVars lit := by
    rcases watched with first | second
    · have value : entry.lits[0]! = lit := (packed.literals 0 (by omega)).symm.trans (by simpa using first)
      have member : entry.lits[0]! ∈ entry.lits := by
        rw [getElem!_pos entry.lits 0 (by omega)]
        exact Array.getElem_mem (by omega)
      simpa only [value] using packed.wellFormed _ member
    · have value : entry.lits[1]! = lit := (packed.literals 1 (by omega)).symm.trans second
      have member : entry.lits[1]! ∈ entry.lits := by
        rw [getElem!_pos entry.lits 1 (by omega)]
        exact Array.getElem_mem (by omega)
      simpa only [value] using packed.wellFormed _ member
  constructor
  · have lower := literal.1
    unfold Lit.var at lower
    omega
  · exact (arrays.literal_index literal).2

/-- The actual arena-sized inner budgets reach zero and the actual outer
loop gives the stable original-ID subsequence at every literal head. -/
theorem removeLearnedWatches_links {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (arrays : ArrayBounds s) :
    ∀ lit, WatchLinks s.removeLearnedWatches lit (originalWatchHeads s.fixed heads lit) := by
  let indices := List.range' 2 (s.first.size - 2)
  have bounded : ∀ lit ∈ indices, lit < s.first.size := by
    intro lit member
    obtain ⟨offset, before, equal⟩ := List.mem_range'.mp member
    omega
  have result := filterOuter_exact indices (List.nodup_range' 1 (by decide)) s heads database
    certificate.links certificate.references certificate.unique bounded
  have execute : s.removeLearnedWatches = forIn (m := Id) indices s watchFilterList := by
    rw [removeLearnedWatches_eq_loop, Std.Legacy.Range.forIn_eq_forIn_range']
    simp only [indices, Std.Legacy.Range.size, Nat.add_sub_cancel, Nat.div_one]
  intro lit
  rw [execute]
  have list := result.2.1 lit
  by_cases member : lit ∈ indices
  · simpa only [filteredHeads, member, ite_true] using list
  · have empty : heads lit = [] := by
      cases equation : heads lit with
      | nil => rfl
      | cons ref rest =>
        have refMember : ref ∈ heads lit := by simp only [equation, List.mem_cons_self]
        have bound := watchHead_bound database certificate arrays refMember
        apply False.elim (member ?_)
        exact List.mem_range'.mpr ⟨lit - 2, by omega, by omega⟩
    simpa only [filteredHeads, member, ite_false, originalWatchHeads, empty, List.filter_nil] using list

/-- Filtering removes all learned refs and preserves exactly both genuine
slots of every original long clause; short clauses never gain a watch. -/
theorem removeLearnedWatches_certificate {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads) (arrays : ArrayBounds s) :
    WatchCertificate s.removeLearnedWatches original (originalWatchHeads s.fixed heads) := by
  constructor
  · exact removeLearnedWatches_links database certificate arrays
  · intro lit ref member
    obtain ⟨oldMember, retained⟩ := List.mem_filter.mp member
    obtain ⟨entry, stored, id, wide⟩ := certificate.references lit ref oldMember
    rcases List.mem_append.mp stored with originalMember | learnedMember
    · exact ⟨entry, originalMember, id, wide⟩
    · have ge := learned_id_ge_fixed database learnedMember
      have lt : watchClause ref < s.fixed := of_decide_eq_true retained
      rw [id] at lt
      omega
  · intro entry member wide
    have old := certificate.covered entry (List.mem_append_left learned member) wide
    have lower := original_id_lt_fixed database member
    have first : watchClause (2 * entry.id) < s.fixed := by unfold watchClause; omega
    have second : watchClause (2 * entry.id + 1) < s.fixed := by unfold watchClause; omega
    have keep (lit ref : Nat) (member : ref ∈ heads lit) (bound : watchClause ref < s.fixed) :
        ref ∈ originalWatchHeads s.fixed heads lit := List.mem_filter.mpr ⟨member, decide_eq_true bound⟩
    refine ⟨old.1, ?_⟩
    rcases old.2 with forward | backward
    · exact Or.inl ⟨keep _ _ forward.1 first, keep _ _ forward.2 second⟩
    · exact Or.inr ⟨keep _ _ backward.1 first, keep _ _ backward.2 second⟩
  · intro lit other ref left right
    exact certificate.unique lit other ref (List.mem_filter.mp left).1 (List.mem_filter.mp right).1

end MicrosatLean.Verification.Implementation.Reduction
