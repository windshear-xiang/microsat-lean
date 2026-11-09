import MicrosatLean.Faithful.Verification.VisitFound
import MicrosatLean.Faithful.Verification.Bump
import MicrosatLean.Faithful.Verification.Implied

/-!
# `analyze` (C:102–130)

`analyze` marks the conflict clause, resolves backwards along the trail to the first
UIP, removes implied literals (`implied`, C:93–100), writes the learned clause into
`buffer`, backjumps, and stores the clause with `addClause`. `analyzeCore` is
everything before the final `addClause` (C:130); `Analyzed` is what it guarantees
(`analyzeCore_spec`, proved in `AnalyzeLoop.lean`).
-/

namespace MicrosatLean.Faithful.Verification

/-- C:103–129: `analyze` up to (not including) its final `addClause`; returns the state and
the size of the learned clause in `buffer`. -/
def analyzeCore (S : solver) (clause : Ptr) : solver × CInt := Id.run do
  let mut S := S
  let mut clause := clause
  S := { S with res := S.res + 1, nConflicts := S.nConflicts + 1 }
  while S.ld clause != 0 do
    S := bump S (S.ld clause)
    clause := clause + 1
  let mut gotoBuild := false
  repeat
    S := { S with assigned := S.assigned - 1 }
    if S.ld (S.reason + abs (S.ld S.assigned)) == 0 then break
    if S.ld (S.false + S.ld S.assigned) == MARK then
      let mut check : Ptr := S.assigned
      repeat
        check := check - 1
        if S.ld (S.false + S.ld check) == MARK then break
        if S.ld (S.reason + abs (S.ld check)) == 0 then
          gotoBuild := true
          break
      if gotoBuild then break
      clause := S.ld (S.reason + abs (S.ld S.assigned))
      while S.ld clause != 0 do
        S := bump S (S.ld clause)
        clause := clause + 1
    S := unassign S (S.ld S.assigned)
  let mut size : CInt := 0
  let mut lbd : CInt := 0
  let mut flag : CInt := 0
  S := { S with processed := S.assigned }
  let mut p : Ptr := S.processed
  while p ≥ S.forced do
    if S.ld (S.false + S.ld p) == MARK then
      let mut r : CInt := 0
      (S, r) := (implied S (S.ld p)).getD (default, 0)
      if r == 0 then
        S := S.st (S.buffer + size) (S.ld p)
        size := size + 1
        flag := 1
    if S.ld (S.reason + abs (S.ld p)) == 0 then
      lbd := lbd + flag
      flag := 0
      if size == 1 then S := { S with processed := p }
    S := S.st (S.false + S.ld p) 1
    p := p - 1
  S := { S with fast := S.fast - (S.fast >>> 5) }
  S := { S with fast := S.fast + (lbd <<< 15) }
  S := { S with slow := S.slow - (S.slow >>> 15) }
  S := { S with slow := S.slow + (lbd <<< 5) }
  while S.assigned > S.processed do
    S := unassign S (S.ld S.assigned)
    S := { S with assigned := S.assigned - 1 }
  S := unassign S (S.ld S.assigned)
  S := S.st (S.buffer + size) 0
  return (S, size)

set_option maxHeartbeats 1000000 in
/-- `analyze` is `analyzeCore` followed by `addClause` of the buffer (C:130). -/
theorem analyze_eq (S : solver) (c : Ptr) :
    analyze S c = addClause (analyzeCore S c).1 (analyzeCore S c).1.buffer (analyzeCore S c).2 0 := by
  unfold analyze analyzeCore
  simp only [Id.run, bind, pure]

/-- What `analyzeCore` leaves (C:102–129), from the conflict state `T`: the learned clause
`L` in `buffer`; the trail cut at the decision position `B`, below which nothing about the
trail changed and the flags are reset; the asserting literal `L[0]` above `B`; `L[1]` at
the highest level below `B`, with no decision between it and `B`; and a decision order. -/
structure Analyzed (input : Input) (T : solver) (db : Records) (S' : solver) (size : CInt)
    (L : List CInt) (vs' : List CInt) (B : Nat) : Prop where
  size_eq : size = L.length
  nonempty : L ≠ []
  buffer_eq : ∀ i (h : i < L.length), S'.ld (S'.buffer + i) = L[i]
  shape : (L.map Int.natAbs).Nodup ∧ ∀ l ∈ L, InRange T.nVars l
  entailed : input.Entails L
  new : ∀ s ∈ db.all, ¬ s.2.Perm L
  fields : ∃ (DB : Array CInt) (h r nc fa sl : CInt),
    S' = ({ T with
      DB := DB, assigned := T.falseStack + B, processed := T.falseStack + B,
      head := h, res := r, nConflicts := nc, fast := fa, slow := sl } : solver)
  cut : B < trailLen T ∧ forcedPos T ≤ B ∧ IsDecision T B
  trail_eq : ∀ i < B, trailAt S' i = trailAt T i
  reason_eq : ∀ i < B, reasonOf S' (trailAt T i) = reasonOf T (trailAt T i)
  model_eq : ∀ i < B, S'.ld (S'.model + abs (trailAt T i)) = T.ld (T.model + abs (trailAt T i))
  flag_root : ∀ i < B, RootLevel T i → flag S' (trailAt T i) = IMPLIED
  flag_level : ∀ i < B, ¬ RootLevel T i → flag S' (trailAt T i) = 1
  flags_off : ∀ l, InRange T.nVars l → (∀ i < B, trailAt T i ≠ l) → flag S' l = 0
  flag_zero : flag S' 0 = 0
  high : ∀ q, 8 * T.nVars + 6 ≤ q → S'.ld q = T.ld q
  order : OrderList S' vs'
  asserting : ∃ U, B ≤ U ∧ U < trailLen T ∧ trailAt T U = L[0]!
  rest_false : ∀ l ∈ L.tail, ∃ j < B, trailAt T j = l
  unit : L.length = 1 → ∀ i < B, RootLevel T i
  second : 2 ≤ L.length → (∃ j1 < B, trailAt T j1 = L[1]! ∧ ∀ k, j1 < k → k < B → ¬ IsDecision T k) ∧
    ∃ D, forcedPos T ≤ D ∧ D < B ∧ IsDecision T D

end MicrosatLean.Faithful.Verification
