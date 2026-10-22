import MicrosatLean.Formula

namespace MicrosatLean.CDCL

structure Config where
  initialLemmaLimit : Nat := 2000
  reductionK : Nat := 6
  deriving Repr, Inhabited

structure Stats where
  conflicts : Nat := 0
  decisions : Nat := 0
  propagations : Nat := 0
  restarts : Nat := 0
  reductions : Nat := 0
  removedLearned : Nat := 0
  deriving Repr, Inhabited

/-- Explicit solver state corresponding to the mutable fields in `microsat.c`.

The arena begins with two zero cells. Each clause occupies two watch-link cells,
its literals, and a zero terminator; its identifier is the first literal index.
A watch reference is `2 * clauseId + slot`, where slot is zero or one. The two
watch references stay attached to their link cells when watched literals swap.
Zero is the end of a watch list and is never a clause identifier.

For valid states, indexed arrays cover all declared variables/literals, arena
clause identifiers are in bounds, and `forced ≤ processed ≤ assigned ≤ nVars`.
The active trail stores false literals, with precisely one per assigned variable.
Marks are 0 (unset), 1 (false), 2 (analysis mark), 5 (not implied), or 6 (implied).
Reasons contain a clause identifier, or zero for a decision. Phases persist after
unassignment. The MTF list is traversed from `head` through `previous` to zero.

The accessors are total; their in-bounds preconditions are explicit invariants
to establish when the implementation is formally verified. -/
structure State where
  nVars : Nat
  arena : Array Nat
  first : Array Nat
  marks : Array Nat
  reasons : Array Nat
  phases : Array Bool
  trail : Array Lit
  assigned : Nat := 0
  processed : Nat := 0
  forced : Nat := 0
  previous : Array Nat
  next : Array Nat
  head : Nat
  fixed : Nat := 2
  nLemmas : Nat := 0
  maxLemmas : Nat := 2000
  res : Nat := 0
  fast : Nat := 16777216
  slow : Nat := 16777216
  stats : Stats := {}
  config : Config := {}
  deriving Repr, Inhabited

@[inline] def watchClause (ref : Nat) : Nat := ref / 2

@[inline] def watchLinkPos (ref : Nat) : Nat := ref / 2 - 2 + ref % 2

namespace State

@[inline] def mark (s : State) (lit : Lit) : Nat := s.marks[lit]!

@[inline] def reason (s : State) (lit : Lit) : Nat := s.reasons[lit.var]!

@[inline] def db (s : State) (idx : Nat) : Nat := s.arena[idx]!

@[inline] def setMark (s : State) (lit : Lit) (value : Nat) : State :=
  { s with marks := s.marks.set! lit value }

@[inline] def unassign (s : State) (lit : Lit) : State := s.setMark lit 0

/-- Assign the first clause literal true. The clause must be unit under the
current assignment, and its first variable must currently be unassigned. -/
@[inline] def assign (s : State) (clauseId : Nat) (root : Bool) : State := Id.run do
  let lit : Lit := s.db clauseId
  let falseLit := lit.negate
  return { s with
    marks := s.marks.set! falseLit (if root then 6 else 1)
    trail := s.trail.set! s.assigned falseLit
    assigned := s.assigned + 1
    reasons := s.reasons.set! lit.var clauseId
    phases := s.phases.set! lit.var (lit % 2 == 0)
    stats := { s.stats with propagations := s.stats.propagations + 1 } }

/-- Decide an unassigned variable using its last saved phase. -/
@[inline] def decide (s : State) (var : Nat) : State :=
  let lit : Lit := 2 * var + if s.phases[var]! then 0 else 1
  { s with
    marks := s.marks.set! lit.negate 1
    trail := s.trail.set! s.assigned lit.negate
    assigned := s.assigned + 1
    reasons := s.reasons.set! var 0
    stats := { s.stats with decisions := s.stats.decisions + 1 } }

@[inline] def addWatch (s : State) (lit : Lit) (ref : Nat) : State :=
  { s with
    arena := s.arena.set! (watchLinkPos ref) s.first[lit]!
    first := s.first.set! lit ref }

/-- Append a clause and return its literal-start identifier. Original clauses
must precede all learned clauses, so `fixed` remains an input-prefix boundary. -/
def addClause (s : State) (lits : Array Lit) (original : Bool) : State × Nat := Id.run do
  let clauseId := s.arena.size + 2
  let mut arena := s.arena.push 0 |>.push 0
  for lit in lits do
    arena := arena.push lit
  arena := arena.push 0
  let mut s := { s with arena }
  if lits.size > 1 then
    s := s.addWatch lits[0]! (2 * clauseId)
    s := s.addWatch lits[1]! (2 * clauseId + 1)
  if original then
    s := { s with fixed := s.arena.size }
  else
    s := { s with nLemmas := s.nLemmas + 1 }
  return (s, clauseId)

/-- Remove all non-root assignments while preserving saved phases. -/
def restart (s : State) : State := Id.run do
  let mut s := s
  for _ in [:s.assigned - s.forced] do
    let idx := s.assigned - 1
    s := { s.unassign s.trail[idx]! with assigned := idx }
  return { s with
    processed := s.forced
    stats := { s.stats with restarts := s.stats.restarts + 1 } }

/-- Mark a false literal and move its variable to the decision-list head.
Top-level implied literals are omitted exactly as in the reference solver. -/
def bump (s : State) (lit : Lit) : State := Id.run do
  if s.mark lit == 6 then return s
  let mut s := s.setMark lit 2
  let var := lit.var
  if var != s.head then
    let prev := s.previous[var]!
    let next := s.next[var]!
    s := { s with
      previous := s.previous.set! next prev
      next := s.next.set! prev next }
    s := { s with
      next := s.next.set! s.head var
      previous := s.previous.set! var s.head
      head := var }
  return s

/-- Remove learned watches while retaining original links and their order.
Each list is acyclic and has at most `arena.size` entries in a valid state. -/
private def removeLearnedWatches (s : State) : State := Id.run do
  let mut s := s
  for lit in [2:s.first.size] do
    let mut ref := s.first[lit]!
    let mut previousLink : Option Nat := none
    for _ in [:s.arena.size] do
      if ref == 0 then break
      let linkPos := watchLinkPos ref
      let nextRef := s.db linkPos
      if watchClause ref < s.fixed then
        previousLink := some linkPos
      else
        match previousLink with
        | none => s := { s with first := s.first.set! lit nextRef }
        | some pos => s := { s with arena := s.arena.set! pos nextRef }
      ref := nextRef
  return s

/-- Compact learned clauses at a root-level restart, retaining clauses satisfied
by fewer than `k` saved phases. Root reason clauses are also retained and their
identifiers remapped; under the usual root invariant and `k > 1` they already
meet the criterion. This avoids the reference C implementation's stale reasons.
All scans have explicit finite bounds for later termination proofs. -/
def reduceDB (s : State) (k : Nat) : State := Id.run do
  let oldArena := s.arena
  let oldLemmas := s.nLemmas
  let mut limit := s.maxLemmas
  if s.nLemmas > limit then
    limit := limit + 300 * ((s.nLemmas - limit + 299) / 300)
  let mut locked := Array.replicate oldArena.size false
  for idx in [:s.forced] do
    let clauseId := s.reason s.trail[idx]!
    if clauseId != 0 then locked := locked.set! clauseId true
  let mut s := removeLearnedWatches s
  s := { s with arena := s.arena.extract 0 s.fixed, nLemmas := 0, maxLemmas := limit }
  let mut remap := Array.replicate oldArena.size 0
  let mut start := s.fixed
  for _ in [:oldLemmas] do
    let clauseId := start + 2
    let mut lits : Array Lit := #[]
    let mut count := 0
    let mut cursor := clauseId
    for _ in [:oldArena.size - clauseId] do
      let lit : Lit := oldArena[cursor]!
      if lit == 0 then break
      lits := lits.push lit
      if lit.satisfiedBy s.phases then count := count + 1
      cursor := cursor + 1
    start := cursor + 1
    if count < k || locked[clauseId]! then
      let (next, newId) := s.addClause lits false
      s := next
      remap := remap.set! clauseId newId
  let mut reasons := s.reasons
  for var in [1:s.nVars + 1] do
    let oldId := reasons[var]!
    if oldId >= s.fixed then
      reasons := reasons.set! var remap[oldId]!
  return { s with
    reasons := reasons
    stats := { s.stats with
      reductions := s.stats.reductions + 1
      removedLearned := s.stats.removedLearned + oldLemmas - s.nLemmas } }

end State

/-- Validate and normalize input clauses, then construct the initial state.
Normalization removes repeated literals and discards tautologies in linear time
using per-clause stamps. `none` detects an empty clause or conflicting units;
other consequences are deliberately left to watched-literal propagation. -/
def initState (formula : Formula) (config : Config := {}) : Except String (Option State) := do
  let n := max 1 formula.numVars
  let mut previous := Array.replicate (n + 1) 0
  let mut next := Array.replicate (n + 1) 0
  for var in [1:n + 1] do
    previous := previous.set! var (var - 1)
    next := next.set! (var - 1) var
  let mut s : State := {
    nVars := n, arena := #[0, 0]
    first := Array.replicate (2 * (n + 1)) 0
    marks := Array.replicate (2 * (n + 1)) 0
    reasons := Array.replicate (n + 1) 0
    phases := Array.replicate (n + 1) false
    trail := Array.replicate (n + 1) 0
    previous, next, head := n, maxLemmas := config.initialLemmaLimit, config }
  let mut stamps := Array.replicate (2 * (n + 1)) 0
  for idx in [:formula.clauses.size] do
    let stamp := idx + 1
    let mut lits : Array Lit := #[]
    let mut tautology := false
    for lit in formula.clauses[idx]! do
      if lit.var == 0 || lit.var > formula.numVars then
        throw s!"literal {lit.toInt} is outside declared variable range 1..{formula.numVars}"
      if stamps[lit.negate]! == stamp then tautology := true
      if stamps[lit]! != stamp then
        stamps := stamps.set! lit stamp
        lits := lits.push lit
    if !tautology then
      if lits.isEmpty then return none
      let (nextState, clauseId) := s.addClause lits true
      s := nextState
      if lits.size == 1 then
        let lit := lits[0]!
        if s.mark lit != 0 then return none
        if s.mark lit.negate == 0 then s := s.assign clauseId true
  return some s

end MicrosatLean.CDCL
