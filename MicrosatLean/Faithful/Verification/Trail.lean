import MicrosatLean.Faithful.Verification.Database

/-!
# The trail: `falseStack`, `false`, `reason` and `model`

`falseStack[0 .. assigned)` holds the literals made false, in order (C:45, C:178).
A decision is a literal whose `reason` is 0 (C:179); positions before the first
decision are the root level. Everything below `forced` is root level, but the root
can extend above `forced`: `parse` assigns unit clauses without moving `forced`
(C:239), and the first `propagate` catches up (C:157). Positions below `processed`
have had their watch lists visited. Positions are counted from `falseStack`.
-/

namespace MicrosatLean.Faithful.Verification

/-- Number of literals on the trail. -/
def trailLen (S : solver) : Nat := (S.assigned - S.falseStack).toNat

/-- Trail entry `i`, a false literal (`falseStack[i]`). -/
def trailAt (S : solver) (i : Nat) : CInt := S.ld (S.falseStack + i)

/-- Position of `forced` on the trail: everything below is root level. -/
def forcedPos (S : solver) : Nat := (S.forced - S.falseStack).toNat

/-- Position of `processed` on the trail: everything below has been propagated. -/
def processedPos (S : solver) : Nat := (S.processed - S.falseStack).toNat

/-- `false[lit]` (C:36, C:44): 0 if `lit` is not false, otherwise a tag. -/
def flag (S : solver) (lit : CInt) : CInt := S.ld (S.false + lit)

/-- `reason[abs lit]`: 0 for a decision, else `1 +` the reason clause pointer (C:46). -/
def reasonOf (S : solver) (lit : CInt) : CInt := S.ld (S.reason + abs lit)

/-- Trail position `i` is a decision: its literal has no reason (C:179). -/
def IsDecision (S : solver) (i : Nat) : Prop :=
  reasonOf S (trailAt S i) = 0

/-- Trail position `i` is at the root level: no decision at or below it. -/
def RootLevel (S : solver) (i : Nat) : Prop :=
  ∀ k ≤ i, ¬ IsDecision S k

/-- `lit` is false at trail position `i`. -/
def FalseAt (S : solver) (lit : CInt) (i : Nat) : Prop :=
  i < trailLen S ∧ trailAt S i = lit

/-- The trail is a stack of distinct variables, and `false` and `model` agree with
it. Between `step`s every `false` tag is 0, 1 or `IMPLIED`: no analysis marks
are left (C:121). Used by every proof that assigns or unassigns. -/
structure Trail (S : solver) : Prop where
  forced_le : S.falseStack ≤ S.forced
  processed_le : S.forced ≤ S.processed
  assigned_le : S.processed ≤ S.assigned
  len_le : trailLen S ≤ S.nVars.toNat
  lit : ∀ i < trailLen S, InRange S.nVars (trailAt S i)
  distinct : ∀ i < trailLen S, ∀ j < trailLen S, abs (trailAt S i) = abs (trailAt S j) → i = j
  /-- Root literals are tagged `IMPLIED` (C:44), the others 1. -/
  flag_root : ∀ i < trailLen S, RootLevel S i → flag S (trailAt S i) = IMPLIED
  flag_level : ∀ i < trailLen S, ¬ RootLevel S i → flag S (trailAt S i) = 1
  /-- Literals not on the trail are not false. -/
  flag_off : ∀ lit, InRange S.nVars lit → (∀ i < trailLen S, trailAt S i ≠ lit) → flag S lit = 0
  /-- `model` is nonzero exactly for the variables assigned true (C:47, C:176). -/
  model : ∀ i < trailLen S, (S.ld (S.model + abs (trailAt S i)) ≠ 0 ↔ trailAt S i < 0)
  /-- `false[0]` is never written; the decision scan stops on it (C:173). -/
  flag_zero : flag S 0 = 0
  /-- Everything below `forced` is root level. -/
  forced_root : ∀ i < forcedPos S, RootLevel S i

/-- Root literals are false in every model of the input. Stale reasons after
`reduceDB` (C:68–83) do not matter: only this semantic fact is kept for them. -/
def RootEntailed (input : Input) (S : solver) : Prop :=
  ∀ i < trailLen S, RootLevel S i → input.Entails [- trailAt S i]

/-- No decision in the trail positions `(p, q]`: `q` is in the same decision level
as `p`, or a lower one. -/
def SameOrLowerLevel (S : solver) (p q : Nat) : Prop :=
  ∀ k, p < k → k ≤ q → ¬ IsDecision S k

/-- Every literal at or above `forced` that is not a decision has its reason clause
in `DB`: the clause's first literal is the literal made true, and its other literals
are false earlier on the trail, one of them at the same level unless at the root.
This is the implication graph `analyze` and `implied` walk; the same-level literal
keeps `implied` from dropping the first UIP (C:93–100).
(Below `forced` reasons may be stale after `reduceDB`; `RootEntailed` covers them.) -/
def Reasons (S : solver) (db : Records) : Prop :=
  ∀ i < trailLen S, forcedPos S ≤ i → reasonOf S (trailAt S i) ≠ 0 →
    ∃ r ∈ db.all, reasonOf S (trailAt S i) = 1 + r.1 ∧ r.2[0]? = some (- trailAt S i) ∧
      (∀ lit ∈ r.2.drop 1, ∃ j < i, FalseAt S lit j) ∧
      (¬ RootLevel S i → ∃ lit ∈ r.2.drop 1, ∃ j < i, FalseAt S lit j ∧ SameOrLowerLevel S j i)

/-- The watched-literal invariant: if a watched literal of a clause is false and
already propagated, the other watched literal is true, at the same or a lower
level. Gives "no missed unit" for SAT answers and "every lemma is new" for termination. -/
def WatchedTrue (S : solver) (db : Records) : Prop :=
  ∀ r ∈ db.all, 2 ≤ r.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
    ∀ p < processedPos S, FalseAt S r.2[w]! p →
      ∃ q, FalseAt S (- r.2[o]!) q ∧ SameOrLowerLevel S p q

/-- Unit clauses are not watched (C:62); their literal is true at the root. -/
def UnitsTrue (S : solver) (db : Records) : Prop :=
  ∀ r ∈ db.all, r.2.length = 1 → ∃ i < trailLen S, RootLevel S i ∧ trailAt S i = - r.2[0]!

end MicrosatLean.Faithful.Verification
