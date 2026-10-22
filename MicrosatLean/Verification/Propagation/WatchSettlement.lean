import MicrosatLean.Verification.Propagation.WatchSettled
import MicrosatLean.Verification.Propagation.WatchRetention

namespace MicrosatLean.Verification.Propagation

open CDCL Representation Analysis

/-- Completed literals may use truth witnesses anywhere on the active trail,
including pending assignments appended while processing an earlier literal. -/
def SettledPrefix (s : State) (entries : List StoredClause)
    (heads : Nat → List Nat) (count : Nat) : Prop :=
  ∀ lit, FalseBefore s count lit → ∀ ref ∈ heads lit,
    SettledWatch s entries s.assigned lit ref

/-- Only the visited part of the current list must already be settled. -/
def SettledCursor (s : State) (entries : List StoredClause)
    (heads : Nat → List Nat) (lit : Lit) (remaining : List Nat) : Prop :=
  ∀ ref ∈ heads lit, ref ∉ remaining → SettledWatch s entries s.assigned lit ref

theorem SettledPrefix.complete {s : State} {entries : List StoredClause}
    {heads : Nat → List Nat} (settled : SettledPrefix s entries heads s.assigned) :
    SettledWatches s entries heads s.assigned := settled

theorem settledCursor_head (s : State) (entries : List StoredClause)
    (heads : Nat → List Nat) (lit : Lit) : SettledCursor s entries heads lit (heads lit) := by
  intro ref member absent
  exact False.elim (absent member)

theorem SettledCursor.advance {s : State} {entries : List StoredClause}
    {heads : Nat → List Nat} {lit : Lit} {ref : Nat} {rest : List Nat}
    (visited : SettledCursor s entries heads lit (ref :: rest))
    (current : SettledWatch s entries s.assigned lit ref) :
    SettledCursor s entries heads lit rest := by
  intro other member absent
  by_cases same : other = ref
  · exact same ▸ current
  · exact visited other member (by simp only [List.mem_cons, same, false_or]; exact absent)

theorem SettledCursor.finish {s : State} {entries : List StoredClause}
    {heads : Nat → List Nat} {lit : Lit}
    (visited : SettledCursor s entries heads lit []) :
    ∀ ref ∈ heads lit, SettledWatch s entries s.assigned lit ref := by
  intro ref member
  exact visited ref member (by simp)

theorem trueBefore_of_marked {s : State} (marked : MarkedOnTrail s)
    {lit : Lit} (truth : s.mark lit.negate ≠ 0) : TrueBefore s s.assigned lit :=
  marked lit.negate truth

theorem falseBefore_assign_prefix {s : State} {count id : Nat} {root : Bool} {lit : Lit}
    (bound : count ≤ s.assigned) (falseLit : FalseBefore (s.assign id root) count lit) :
    FalseBefore s count lit := by
  obtain ⟨i, before, value⟩ := falseLit
  exact ⟨i, before, (assign_trail_prefix (by omega)).symm.trans value⟩

theorem trueBefore_assign {s : State} {id : Nat} {root : Bool} {lit : Lit}
    (truth : TrueBefore s s.assigned lit) :
    TrueBefore (s.assign id root) (s.assign id root).assigned lit := by
  obtain ⟨i, before, value⟩ := truth
  exact ⟨i, by simpa [State.assign] using Nat.lt_succ_of_lt before,
    (assign_trail_prefix before).trans value⟩

theorem SettledWatch.assign {s : State} {entries : List StoredClause} {lit : Lit} {ref id : Nat}
    {root : Bool} (settled : SettledWatch s entries s.assigned lit ref) :
    SettledWatch (s.assign id root) entries (s.assign id root).assigned lit ref := by
  intro entry member same
  exact trueBefore_assign (settled entry member same)

theorem SettledPrefix.assign {s : State} {entries : List StoredClause} {heads : Nat → List Nat}
    {count id : Nat} {root : Bool} (settled : SettledPrefix s entries heads count)
    (bound : count ≤ s.assigned) : SettledPrefix (s.assign id root) entries heads count := by
  intro lit falseLit ref member
  exact (settled lit (falseBefore_assign_prefix bound falseLit) ref member).assign

theorem SettledCursor.assign {s : State} {entries : List StoredClause} {heads : Nat → List Nat}
    {lit : Lit} {remaining : List Nat} {id : Nat} {root : Bool}
    (settled : SettledCursor s entries heads lit remaining) :
    SettledCursor (s.assign id root) entries heads lit remaining := by
  intro ref member absent
  exact (settled ref member absent).assign

/-- Swapping the two watched positions preserves the opposite watch for a
literal genuinely attached to either position. -/
theorem otherWatch_retainWatchEntry (entry : StoredClause) (first : Bool)
    (wide : 2 ≤ entry.lits.size) (distinct : entry.lits[0]! ≠ entry.lits[1]!)
    {lit : Lit} (watched : lit = entry.lits[0]! ∨ lit = entry.lits[1]!) :
    otherWatch (retainWatchEntry entry.id first entry).lits lit = otherWatch entry.lits lit := by
  have pair := retainWatchEntry_heads entry first wide
  unfold otherWatch
  rw [pair.1, pair.2]
  cases first <;> rcases watched with rfl | rfl <;> simp [distinct, Ne.symm distinct]

theorem watch_ref_literals {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    {entry : StoredClause} (member : entry ∈ original ++ learned)
    {lit : Lit} {ref : Nat} (current : ref ∈ heads lit) (id : watchClause ref = entry.id)
    (wide : 2 ≤ entry.lits.size) : lit = entry.lits[0]! ∨ lit = entry.lits[1]! := by
  have packed := database.layout.packed member
  have watched := (certificate.entry database current).2.2.2
  rw [id] at watched
  have first : s.db entry.id = entry.lits[0]! := by simpa using packed.literals 0 (by omega)
  have second := packed.literals 1 (by omega : 1 < entry.lits.size)
  rcases watched with head | tail
  · exact Or.inl (head.symm.trans first)
  · exact Or.inr (tail.symm.trans second)

/-- Completing a failed replacement's orientation preserves every existing
settled witness. Only a swap of the two genuine watched positions occurs. -/
theorem SettledWatch.retain {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    {target : StoredClause} (targetMember : target ∈ original ++ learned)
    {query : Lit} {ref : Nat} (current : ref ∈ heads query)
    (settled : SettledWatch s (original ++ learned) s.assigned query ref)
    (first : Bool) (arena : Array Nat) :
    SettledWatch { s with arena := arena }
      ((original ++ learned).map (retainWatchEntry target.id first)) s.assigned query ref := by
  intro changed changedMember id
  obtain ⟨old, member, rfl⟩ := List.mem_map.mp changedMember
  have oldId : watchClause ref = old.id := by simpa only [retainWatchEntry_id] using id
  have truth := settled old member oldId
  by_cases same : old.id = target.id
  · have equal := database.layout.entry_eq_of_id member targetMember same
    subst old
    obtain ⟨proper, properMember, properId, wide⟩ := certificate.references query ref current
    have equal := database.layout.entry_eq_of_id properMember targetMember (properId.symm.trans oldId)
    subst proper
    rw [otherWatch_retainWatchEntry target first wide (certificate.covered target targetMember wide).1
      (watch_ref_literals database certificate targetMember current oldId wide)]
    exact truth
  · rw [retainWatchEntry_of_ne _ _ _ same]
    exact truth

theorem SettledPrefix.retain {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    {target : StoredClause} (targetMember : target ∈ original ++ learned)
    {count : Nat} (settled : SettledPrefix s (original ++ learned) heads count)
    (first : Bool) (arena : Array Nat) :
    SettledPrefix { s with arena := arena }
      ((original ++ learned).map (retainWatchEntry target.id first)) heads count := by
  intro lit falseLit ref member
  exact (settled lit falseLit ref member).retain database certificate targetMember member first arena

theorem SettledCursor.retain {s : State} {original learned : List StoredClause}
    {heads : Nat → List Nat} (database : Database s original learned)
    (certificate : WatchCertificate s (original ++ learned) heads)
    {target : StoredClause} (targetMember : target ∈ original ++ learned)
    {lit : Lit} {remaining : List Nat}
    (settled : SettledCursor s (original ++ learned) heads lit remaining)
    (first : Bool) (arena : Array Nat) :
    SettledCursor { s with arena := arena }
      ((original ++ learned).map (retainWatchEntry target.id first)) heads lit remaining := by
  intro ref member absent
  exact (settled ref member absent).retain database certificate targetMember member first arena

end MicrosatLean.Verification.Propagation
