import MicrosatLean.Verification.Implementation.Propagation.WatchHeads
import MicrosatLean.Verification.Implementation.Propagation.WatchSplice

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL Representation

/-- The unvisited suffix of the concrete watch list. The predecessor is zero
at its head; otherwise a uniquely owned visited ref ends the processed prefix. -/
inductive WatchCursor (heads : Nat → List Nat) (lit : Lit) : Nat → List Nat → Prop where
  | head (remaining : List Nat) (same : heads lit = remaining) : WatchCursor heads lit 0 remaining
  | after (previous : Nat) (initial remaining : List Nat) (nonzero : previous ≠ 0)
      (same : heads lit = initial ++ previous :: remaining) : WatchCursor heads lit previous remaining

theorem WatchCursor.current {s : State} {heads : Nat → List Nat} {lit : Lit} {previous : Nat}
    {remaining : List Nat} (cursor : WatchCursor heads lit previous remaining)
    (links : WatchLinks s lit (heads lit)) : currentWatchRef s.arena s.first lit previous = remaining.headD 0 := by
  cases cursor with
  | head remaining same => simpa only [currentWatchRef, beq_self_eq_true, ite_true, same] using links.2.1
  | after previous initial remaining nonzero same =>
    have chain := links.chain
    rw [same] at chain
    exact (by simpa only [currentWatchRef, beq_iff_eq, nonzero, ite_false, State.db] using
      (chain.suffix initial (previous :: remaining)).1)

theorem WatchCursor.member {heads : Nat → List Nat} {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (cursor : WatchCursor heads lit previous (ref :: rest)) : ref ∈ heads lit := by
  cases cursor with
  | head _ same => simp only [same, List.mem_cons_self]
  | after _ _ _ _ same => simp [same]

theorem WatchCursor.previous_member {heads : Nat → List Nat} {lit : Lit} {previous : Nat} {remaining : List Nat}
    (cursor : WatchCursor heads lit previous remaining) (nonzero : previous ≠ 0) : previous ∈ heads lit := by
  cases cursor with
  | head _ _ => exact False.elim (nonzero rfl)
  | after _ _ _ _ same => simp [same]

theorem WatchCursor.length_le {heads : Nat → List Nat} {lit : Lit} {previous : Nat} {remaining : List Nat}
    (cursor : WatchCursor heads lit previous remaining) : remaining.length ≤ (heads lit).length := by
  cases cursor with
  | head _ same => simp [same]
  | after _ _ _ _ same => simp [same]; omega

theorem WatchCursor.advance {heads : Nat → List Nat} {lit : Lit} {previous ref : Nat} {rest : List Nat}
    (cursor : WatchCursor heads lit previous (ref :: rest)) (nonzero : ref ≠ 0) : WatchCursor heads lit ref rest := by
  cases cursor with
  | head _ same => exact .after ref [] rest nonzero same
  | after previous initial _ _ same =>
    exact .after ref (initial ++ [previous]) rest nonzero (by simpa only [List.append_assoc, List.singleton_append] using same)

theorem WatchCursor.move {heads : Nat → List Nat} {lit newLit : Lit} {previous ref : Nat} {rest : List Nat}
    (cursor : WatchCursor heads lit previous (ref :: rest)) (nodup : (heads lit).Nodup)
    (different : lit ≠ newLit) : WatchCursor (moveHeads heads newLit ref) lit previous rest := by
  cases cursor with
  | head _ same =>
    apply WatchCursor.head
    simp only [moveHeads, different, ite_false, same, List.erase_cons_head]
  | after previous initial _ nonzero same =>
    have parts : initial.Nodup ∧ (previous :: ref :: rest).Nodup ∧
        ∀ a ∈ initial, ∀ b ∈ previous :: ref :: rest, a ≠ b := by
      simpa only [same, List.nodup_append] using nodup
    have absent : ref ∉ initial := fun member => parts.2.2 ref member ref (by simp) rfl
    have ne : previous ≠ ref := fun equal => (List.nodup_cons.mp parts.2.1).1 (by simp [equal])
    apply WatchCursor.after previous initial rest nonzero
    simp only [moveHeads, different, ite_false, same]
    rw [List.erase_append_right _ absent, List.erase_cons_tail (by simpa using ne), List.erase_cons_head]

end MicrosatLean.Verification.Implementation.Propagation
