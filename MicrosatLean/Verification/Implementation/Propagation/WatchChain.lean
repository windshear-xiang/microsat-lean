import MicrosatLean.Verification.Implementation.Propagation.WatchLinks

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL

/-- Structural presentation of the same finite pointer chain as WatchLinks. -/
def WatchChain (s : State) : List Nat → Prop
  | [] => True
  | ref :: rest => s.db (watchLinkPos ref) = rest.headD 0 ∧ WatchChain s rest

theorem watchChain_iff {s : State} (refs : List Nat) : WatchChain s refs ↔
    ∀ i, i < refs.length → s.db (watchLinkPos (refs.getD i 0)) = refs.getD (i + 1) 0 := by
  induction refs with
  | nil => simp [WatchChain]
  | cons ref rest ih =>
    constructor
    · rintro ⟨head, tail⟩ i within
      cases i with
      | zero => simpa only [List.getD_cons_zero, List.getD_cons_succ, List.headD_eq_getD] using head
      | succ i =>
        have before : i < rest.length := by simpa using within
        simpa only [List.getD_cons_succ] using ih.mp tail i before
    · intro links
      constructor
      · simpa only [List.getD_cons_zero, List.getD_cons_succ, List.headD_eq_getD] using links 0 (by simp)
      · apply ih.mpr
        intro i before
        simpa only [List.getD_cons_succ] using links (i + 1) (by simp; omega)

theorem WatchLinks.chain {s : State} {lit : Lit} {refs : List Nat} (links : WatchLinks s lit refs) :
    WatchChain s refs := (watchChain_iff refs).mpr links.2.2

theorem WatchChain.frame {before after : State} {refs : List Nat} (chain : WatchChain before refs)
    (cells : ∀ ref ∈ refs, after.db (watchLinkPos ref) = before.db (watchLinkPos ref)) : WatchChain after refs := by
  induction refs with
  | nil => trivial
  | cons ref rest ih =>
    exact ⟨(cells ref (by simp)).trans chain.1, ih chain.2 (fun other member => cells other (by simp [member]))⟩

theorem WatchChain.suffix {s : State} (before rest : List Nat) (chain : WatchChain s (before ++ rest)) :
    WatchChain s rest := by
  induction before with
  | nil => exact chain
  | cons ref before ih => exact ih chain.2

/-- Removing the element after `previous` changes exactly that predecessor's
next pointer. Every earlier pointer and every retained suffix pointer stays. -/
theorem WatchChain.splice {before after : State} (initial : List Nat) (previous ref : Nat) (rest : List Nat)
    (chain : WatchChain before (initial ++ previous :: ref :: rest))
    (next : after.db (watchLinkPos previous) = rest.headD 0)
    (cells : ∀ old ∈ initial ++ rest,
      after.db (watchLinkPos old) = before.db (watchLinkPos old)) :
    WatchChain after (initial ++ previous :: rest) := by
  induction initial with
  | nil => exact ⟨next, chain.2.2.frame (by simpa using cells)⟩
  | cons head initial ih =>
    constructor
    · rw [cells head (by simp)]
      have sameHead : (initial ++ previous :: ref :: rest).headD 0 =
          (initial ++ previous :: rest).headD 0 := by cases initial <;> rfl
      exact chain.1.trans sameHead
    · apply ih chain.2
      intro old member
      exact cells old (by simp [member])

end MicrosatLean.Verification.Implementation.Propagation
