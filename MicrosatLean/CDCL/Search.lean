import MicrosatLean.CDCL.Analysis

namespace MicrosatLean.CDCL

/-- A completed search, including the saved assignment for satisfiable inputs. -/
inductive SolveResult where
  | sat (model : Array Bool) (stats : Stats)
  | unsat (stats : Stats)
  deriving Repr, Inhabited

/-- The propagation cursor makes even an unbounded search a sequence of total
transitions. A watch step handles a bounded part of one literal's watch list;
analysis is bounded by the trail. -/
inductive Phase where
  | beginPropagation
  | nextLiteral
  | watch
  | choose
  deriving Repr, Inhabited

/-- `previousWatch = 0` means the current list's head; otherwise its next link.
`root` is preserved across a propagation invocation, including its conflicts,
and becomes true when analysis derives a unit clause. -/
structure Machine where
  solver : State
  decision : Nat
  phase : Phase := .beginPropagation
  oldLemmas : Nat := 0
  root : Bool := false
  currentLit : Lit := 0
  previousWatch : Nat := 0
  deriving Repr, Inhabited

/-- Construct the initial search machine with its decision cursor at the MTF
head and the remaining control fields at their defaults. -/
def Machine.initial (s : State) : Machine := { solver := s, decision := s.head }

inductive Progress where
  | running (machine : Machine)
  | finished (result : SolveResult)
  deriving Repr, Inhabited

/-- Find the first nonfalse, nonwatched literal in source order. Structural
recursion avoids allocating a range and early-return accumulator for every
visited clause. The caller supplies the remaining arena length as a bound. -/
def replacementScan : Nat → Array Nat → Array Nat → Nat → Option Nat
  | 0, _, _, _ => none
  | fuel + 1, arena, marks, pos =>
    let lit := arena[pos]!
    if lit == 0 then none
    else if marks[lit]! == 0 then some pos
    else replacementScan fuel arena marks (pos + 1)

def replacement (arena marks : Array Nat) (clauseId : Nat) : Option Nat :=
  replacementScan (arena.size - (clauseId + 2)) arena marks (clauseId + 2)

/-- Bounded traversal of the move-to-front list through assigned variables.
Zero denotes an exhausted list or exhausted traversal budget. -/
def nextDecisionScan : Nat → State → Nat → Nat
  | 0, _, _ => 0
  | fuel + 1, s, cursor =>
    if cursor == 0 then 0
    else if s.mark (2 * cursor) == 0 && s.mark (2 * cursor + 1) == 0 then cursor
    else nextDecisionScan fuel s s.previous[cursor]!

/-- The MTF list's acyclicity and coverage justify the `nVars + 1` bound. -/
def nextDecision (s : State) (cursor : Nat) : Nat :=
  nextDecisionScan (s.nVars + 1) s cursor

/-- Reattach the two arrays temporarily owned by the propagation loop. -/
@[inline] def restoreWatchArrays (s : State) (arena first : Array Nat) : State :=
  { s with arena := arena, first := first }

/-- Traverse one false literal's watch list in the reference solver's order.
The arena and watch heads are detached from `s`, avoiding reconstruction of all
state fields at every clause. The complete state is restored before assignment,
analysis, or any return. The other state fields remain unchanged during a scan.
The representation invariant concerns `restoreWatchArrays s arena first`, not
the temporarily detached state on its own.

The initial arena length bounds an acyclic watch list. A replacement cannot be
the current false literal, so moving a watch never adds to the list being scanned.
Fuel exhaustion still returns a resumable cursor without a SAT/UNSAT claim. -/
def propagateWatches : Nat → State → Array Nat → Array Nat → Nat → Nat → Bool → Lit → Nat → Progress
  | 0, s, arena, first, decision, oldLemmas, root, lit, previous =>
    .running ⟨restoreWatchArrays s arena first, decision, .watch, oldLemmas, root, lit, previous⟩
  | fuel + 1, s, arena, first, decision, oldLemmas, root, lit, previous => Id.run do
    let ref := if previous == 0 then first[lit]! else arena[watchLinkPos previous]!
    if ref == 0 then
      return .running ⟨restoreWatchArrays s arena first, decision, .nextLiteral, oldLemmas, root, 0, 0⟩
    let clauseId := watchClause ref
    -- Keep the other watch first, then preserve the exact source scan/swap order.
    let arena := if arena[clauseId]! == lit then
        arena.set! clauseId arena[clauseId + 1]!
      else arena
    match replacement arena s.marks clauseId with
    | some pos =>
      let newLit := arena[pos]!
      let arena := (arena.set! (clauseId + 1) newLit).set! pos lit
      let nextRef := arena[watchLinkPos ref]!
      let (arena, first) := if previous == 0 then
          (arena, first.set! lit nextRef)
        else
          (arena.set! (watchLinkPos previous) nextRef, first)
      let arena := arena.set! (watchLinkPos ref) first[newLit]!
      let first := first.set! newLit ref
      return propagateWatches fuel s arena first decision oldLemmas root lit previous
    | none =>
      let arena := arena.set! (clauseId + 1) lit
      let other : Lit := arena[clauseId]!
      if s.mark other.negate != 0 then
        return propagateWatches fuel s arena first decision oldLemmas root lit ref
      let s := restoreWatchArrays s arena first
      if s.mark other == 0 then
        let s := s.assign clauseId root
        return .running ⟨s, decision, .watch, oldLemmas, root, lit, ref⟩
      if root then return .finished (.unsat s.stats)
      let (s, learned) := analyze s clauseId
      let root := s.db (learned + 1) == 0
      let s := s.assign learned root
      return .running ⟨s, decision, .nextLiteral, oldLemmas, root, 0, 0⟩

/-- Perform one faithful CDCL transition, batching watch-list visits until a
unit, conflict, list end, or finite bound. All internal scans are bounded by
finite arrays. Only the outer execution driver is unbounded. -/
def step (machine : Machine) : Progress := Id.run do
  let ⟨s, decision, phase, oldLemmas, root, lit, previous⟩ := machine
  match phase with
  | .beginPropagation =>
    let root := s.processed < s.assigned && s.reason s.trail[s.processed]! != 0
    return .running ⟨s, decision, .nextLiteral, s.nLemmas, root, 0, 0⟩
  | .nextLiteral =>
    if s.processed < s.assigned then
      let lit := s.trail[s.processed]!
      let s := { s with processed := s.processed + 1 }
      return .running ⟨s, decision, .watch, oldLemmas, root, lit, 0⟩
    let s := if root then { s with forced := s.processed } else s
    return .running ⟨s, decision, .choose, oldLemmas, root, 0, 0⟩
  | .watch =>
    let arena := s.arena
    let first := s.first
    let s := { s with arena := #[], first := #[] }
    return propagateWatches arena.size s arena first decision oldLemmas root lit previous
  | .choose =>
    let mut s := s
    let mut decision := decision
    if s.nLemmas > oldLemmas then
      decision := s.head
      let threshold := (s.slow / 100) * 125
      if s.fast > threshold then
        s := ({ s with res := 0, fast := threshold }).restart
        if s.nLemmas > s.maxLemmas then
          s := s.reduceDB s.config.reductionK
    decision := nextDecision s decision
    if decision == 0 then
      return .finished (.sat s.phases s.stats)
    s := s.decide decision
    return .running ⟨s, decision, .beginPropagation, 0, false, 0, 0⟩

/-- Execute at most `fuel` transitions, returning a resumable machine when the
budget expires. This helper supports bounded and chunked regression tests;
fuel exhaustion is never classified as SAT or UNSAT. A watch transition may
visit several clauses, with its own arena-length bound. -/
def runFor : Nat → Machine → Progress
  | 0, machine => .running machine
  | fuel + 1, machine =>
    match step machine with
    | .finished result => .finished result
    | .running next => runFor fuel next

end MicrosatLean.CDCL
