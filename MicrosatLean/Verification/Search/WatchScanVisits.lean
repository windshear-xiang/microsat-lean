import MicrosatLean.Verification.Search.WatchScan

namespace MicrosatLean.Verification.Search

open CDCL Representation Propagation Analysis Std.Sat

theorem WatchScanFacts.skip {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {count : Nat} {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (facts : WatchScanFacts formula s original learned heads rank count lit previous (ref :: rest))
    (falseLit : s.mark lit ≠ 0)
    (truth : s.mark (Lit.negate ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!)) ≠ 0) :
    let after := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    ∃ nextOriginal nextLearned,
      WatchScanFacts formula after nextOriginal nextLearned heads rank count lit ref rest := by
  dsimp only
  obtain ⟨nextOriginal, nextLearned, oriented⟩ := facts.orient falseLit
  obtain ⟨settledOriginal, settledLearned, database, _, _, _, cursor, _, visited⟩ :=
    skip_branch_settlement facts.base.database facts.base.meaning facts.base.watches facts.base.nodup facts.base.marked
      facts.cursor facts.prefixSettled facts.visited truth
  obtain ⟨sameOriginal, sameLearned⟩ := database.unique oriented.base.database
  subst settledOriginal settledLearned
  exact ⟨nextOriginal, nextLearned, oriented.base, oriented.history, oriented.saved, oriented.units,
    oriented.bound, oriented.prefixSettled, visited, cursor⟩

theorem WatchScanFacts.unit {formula : CNF Nat} {s : State}
    {original learned : List StoredClause} {heads : Nat → List Nat} {rank : Lit → Nat}
    {count : Nat} {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (facts : WatchScanFacts formula s original learned heads rank count lit previous (ref :: rest))
    (falseLit : s.mark lit ≠ 0) (root : Bool) (rootTrail : RootWatchTrail s root)
    (missing : replacement (orientWatch s.arena (watchClause ref) lit) s.marks (watchClause ref) = none)
    (head : s.mark ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!) = 0)
    (opposite : s.mark (Lit.negate ((Propagation.retainWatch s.arena (watchClause ref) lit)[watchClause ref]!)) = 0) :
    let retained := { s with arena := Propagation.retainWatch s.arena (watchClause ref) lit }
    let after := retained.assign (watchClause ref) root
    ∃ nextOriginal nextLearned nextRank,
      WatchScanFacts formula after nextOriginal nextLearned heads nextRank count lit ref rest := by
  dsimp only
  obtain ⟨nextOriginal, nextLearned, nextRank, nextBase, nextHistory⟩ :=
    facts.base.watchUnit facts.cursor.member falseLit root rootTrail missing head opposite
  obtain ⟨savedOriginal, savedLearned, _, savedBase, nextSaved⟩ :=
    facts.base.watchUnit_saved facts.cursor.member falseLit root rootTrail missing head opposite
  obtain ⟨sameOriginal, sameLearned⟩ := savedBase.database.unique nextBase.database
  subst savedOriginal savedLearned
  have space : s.assigned < s.trail.size := by
    rw [facts.base.arrays.trailSize]
    have assigned := facts.base.bounds.assignedVars
    omega
  obtain ⟨settledOriginal, settledLearned, settledDatabase, _, _, _, cursor, prefixSettled, visited⟩ :=
    unit_branch_settlement facts.base.database facts.base.meaning facts.base.watches facts.base.nodup facts.bound
      facts.cursor facts.prefixSettled facts.visited root space
  obtain ⟨sameOriginal, sameLearned⟩ := settledDatabase.unique nextBase.database
  subst settledOriginal settledLearned
  obtain ⟨retainedOriginal, retainedLearned, oriented⟩ := facts.orient falseLit
  have units := units_assign oriented.units (watchClause ref) root
  obtain ⟨sameOriginal, sameLearned⟩ := (oriented.base.database.assign (watchClause ref) root).unique nextBase.database
  subst retainedOriginal retainedLearned
  refine ⟨nextOriginal, nextLearned, nextRank, nextBase, nextHistory facts.history, nextSaved facts.saved,
    units, ?_, prefixSettled, visited, cursor⟩
  change count ≤ s.assigned + 1
  have := facts.bound
  omega

end MicrosatLean.Verification.Search
