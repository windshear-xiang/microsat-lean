import MicrosatLean.CDCL.State

namespace MicrosatLean.CDCL

/-!
Conflict analysis follows `analyze` and `implied` in `upstream/microsat.c`.
The trail stores falsified literals. Reason clauses start with the literal
made true, so resolution and minimization inspect each reason after its head.

The executable helpers use explicit bounds: reasons of assigned variables refer
only to earlier trail entries, and every arena clause has a zero terminator.
These are the intended invariants for subsequent refinement proofs. Exhausting
the minimization bound conservatively retains a literal in the learned clause.
-/

/-- Check whether a false literal follows from the currently marked literals.
The tags 5 and 6 cache failure and success, respectively, as in Microsat.
On a well-formed implication graph, `nVars + 1` bounds the recursive depth. -/
def implied : Nat → State → Lit → State × Bool
  | 0, s, _ => (s, false)
  | fuel + 1, s, lit => Id.run do
    let tag := s.mark lit
    if tag > 2 then
      return (s, tag &&& 2 != 0)
    let reason := s.reason lit
    if reason == 0 then
      return (s, false)
    let mut s := s
    for i in [reason + 1 : s.arena.size] do
      let antecedent := s.db i
      if antecedent == 0 then
        break
      if s.mark antecedent != 2 then
        let (next, follows) := implied fuel s antecedent
        s := next
        if !follows then
          return (s.setMark lit 5, false)
    return (s.setMark lit 6, true)

/-- Mark a clause suffix, also moving its variables to the heuristic front. -/
def markClause (s : State) (start : Nat) : State := Id.run do
  let mut s := s
  for i in [start : s.arena.size] do
    let lit := s.db i
    if lit == 0 then
      break
    s := s.bump lit
  return s

/-- The candidate is the first UIP precisely when no earlier marked literal
occurs before the decision that begins its decision level. -/
def firstUIP (s : State) (candidate : Nat) : Bool := Id.run do
  for offset in [:candidate] do
    let lit := s.trail[candidate - 1 - offset]!
    if s.mark lit == 2 then
      return false
    if s.reason lit == 0 then
      return true
  return true

/-- Construct the minimized learned clause in reverse trail order, recording
its backjump cursor and LBD. Earlier MARK tags remain available to `implied`. -/
def buildLearned (s : State) (candidate : Nat) : State × Array Lit × Nat := Id.run do
  let mut s := { s with processed := candidate }
  let mut learned : Array Lit := #[]
  let mut lbd := 0
  let mut levelUsed := false
  for offset in [:candidate + 1 - s.forced] do
    let p := candidate - offset
    let lit := s.trail[p]!
    if s.mark lit == 2 then
      let (next, follows) := implied (s.nVars + 1) s lit
      s := next
      if !follows then
        learned := learned.push lit
        levelUsed := true
    if s.reason lit == 0 then
      if levelUsed then
        lbd := lbd + 1
      levelUsed := false
      if learned.size == 1 then
        s := { s with processed := p }
    s := s.setMark lit 1
  return (s, learned, lbd)

/-- Clear the analyzed candidate and every trail entry above the backjump
cursor. Popped entries remain in the fixed-capacity trail array. -/
def backjump (s : State) (candidate : Nat) : State := Id.run do
  let mut s := s
  for offset in [:candidate + 1 - s.processed] do
    s := s.unassign s.trail[candidate - offset]!
  return { s with assigned := s.processed }

/-- Pop the conflict's implication graph until its decision or first UIP.
During this phase `assigned` changes from a count to the candidate's index. -/
def resolveToUIP (s : State) : State := Id.run do
  let mut s := s
  for _ in [:s.assigned] do
    let candidate := s.assigned - 1
    s := { s with assigned := candidate }
    let lit := s.trail[candidate]!
    if s.reason lit == 0 then break
    if s.mark lit == 2 then
      if firstUIP s candidate then break
      s := markClause s (s.reason lit + 1)
    s := s.unassign lit
  return s

/-- Resolve a non-root conflict, minimize the first-UIP clause, and backjump.
`assigned` is normally a count; while analyzing it is the candidate's index,
exactly like the decremented assignment pointer in the source implementation.
The fixed-capacity trail preserves popped entries until clause construction
finishes. The result points to the learned clause's first literal. -/
def analyze (s : State) (conflictClauseId : Nat) : State × Nat := Id.run do
  let mut s := { s with
    res := s.res + 1
    stats := { s.stats with conflicts := s.stats.conflicts + 1 } }
  s := markClause s conflictClauseId
  s := resolveToUIP s
  let candidate := s.assigned
  let (next, learned, lbd) := buildLearned s candidate
  s := next
  s := { s with
    fast := s.fast - (s.fast >>> 5) + (lbd <<< 15)
    slow := s.slow - (s.slow >>> 15) + (lbd <<< 5) }
  s := backjump s candidate
  return s.addClause learned false

end MicrosatLean.CDCL
