import MicrosatLean.Verification.Implementation.Native.Search.Assignment
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchBounds
import MicrosatLean.Verification.Implementation.Native.Analysis.DecisionHistory

namespace MicrosatLean.Verification.Implementation.Native.Search

open CDCL Representation Propagation Analysis Std.Sat

theorem canonicalKey_perm (n : Nat) {left right : Array Lit} (perm : left.Perm right) :
    canonicalKey n left = canonicalKey n right :=
  Logic.ClauseSpace.canonicalize_eq_of_mem_iff n
    (fun _ => ((Array.perm_iff_toList_perm.mp perm).map literalView).mem_iff)

theorem noClash_perm {left right : Array Lit} (perm : left.Perm right)
    (noClash : Logic.ClauseSpace.NoClash (viewedLiterals right)) :
    Logic.ClauseSpace.NoClash (viewedLiterals left) := by
  have same (lit : Literal Nat) : lit ∈ viewedLiterals left ↔ lit ∈ viewedLiterals right :=
    ((Array.perm_iff_toList_perm.mp perm).map literalView).mem_iff
  intro var positive negative
  exact noClash var ((same _).mp positive) ((same _).mp negative)

/-- Watch-array writes leave assignment data intact. Concrete operation
lemmas supply the new packed database, linked watches, and exact reason slices;
literal permutations preserve the normalization and learned-key invariants. -/
theorem StateCertificate.watchArrays {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    (certificate : StateCertificate formula s original learned heads rank)
    (arena first : Array Nat) (firstSize : first.size = s.first.size)
    (f : StoredClause → StoredClause) (ids : ∀ entry, (f entry).id = entry.id)
    (sizes : ∀ entry, (f entry).lits.size = entry.lits.size)
    (perms : ∀ entry, (f entry).lits.Perm entry.lits) (nextHeads : Nat → List Nat)
    (database : Database (restoreWatchArrays s arena first) (original.map f) (learned.map f))
    (meaning : DatabaseMeaning formula (original.map f) (learned.map f))
    (watches : WatchCertificate (restoreWatchArrays s arena first)
      (original.map f ++ learned.map f) nextHeads)
    (graph : ReasonGraph formula (restoreWatchArrays s arena first) s.assigned rank) :
    StateCertificate formula (restoreWatchArrays s arena first)
      (original.map f) (learned.map f) nextHeads rank := by
  refine ⟨arrayBounds_restoreWatchArrays certificate.arrays arena first firstSize,
    ⟨certificate.bounds.forcedProcessed, certificate.bounds.processedAssigned, certificate.bounds.assignedVars⟩,
    certificate.active, certificate.distinct, certificate.phases, certificate.marked,
    certificate.order, database, meaning, ?_, graph, watches, ?_, ?_, ?_, ?_,
    certificate.tags, certificate.roots, certificate.rootPrefix⟩
  · have proper : ReasonDatabase (restoreWatchArrays s arena first) ((original ++ learned).map f) s.assigned :=
      (certificate.reasons.mapEntries f ids).frame rfl rfl
    simpa only [List.map_append, restoreWatchArrays] using proper
  · intro changed member
    rw [← List.map_append] at member
    obtain ⟨entry, oldMember, rfl⟩ := List.mem_map.mp member
    rw [sizes]
    exact certificate.nonempty entry oldMember
  · intro changed member
    rw [← List.map_append] at member
    obtain ⟨entry, oldMember, rfl⟩ := List.mem_map.mp member
    exact (Array.perm_iff_toList_perm.mp (perms entry)).symm.nodup (certificate.nodup entry oldMember)
  · intro changed member
    rw [← List.map_append] at member
    obtain ⟨entry, oldMember, rfl⟩ := List.mem_map.mp member
    exact noClash_perm (perms entry) (certificate.noClash entry oldMember)
  · have keys : (learned.map f).map (fun entry => canonicalKey s.nVars entry.lits) =
        learned.map (fun entry => canonicalKey s.nVars entry.lits) := by
      simp only [List.map_map, Function.comp_def]
      exact List.map_congr_left (fun entry _ => canonicalKey_perm s.nVars (perms entry))
    simpa only [restoreWatchArrays, keys] using certificate.learnedDistinct

theorem decisionHistory_watchArrays_map {s : State} {entries : List StoredClause}
    (history : DecisionHistory s entries) (arena first : Array Nat)
    (f : StoredClause → StoredClause) (perms : ∀ entry, (f entry).lits.Perm entry.lits) :
    DecisionHistory (restoreWatchArrays s arena first) (entries.map f) := by
  apply (history.frame rfl rfl rfl rfl).restrict
  intro changed member
  obtain ⟨entry, oldMember, rfl⟩ := List.mem_map.mp member
  exact ⟨entry, oldMember, fun _ => (perms entry).mem_iff⟩

end MicrosatLean.Verification.Implementation.Native.Search
