import MicrosatLean.Verification.Specification

/-! Canonical storage predicates shared by the logical model and concrete
implementation proofs. No operation preservation or solver result is assumed. -/

namespace MicrosatLean.Verification.Implementation.Representation

open CDCL

/-- A runtime literal names a declared, nonzero variable. -/
def LiteralBound (n : Nat) (lit : Lit) : Prop :=
  1 ≤ lit.var ∧ lit.var ≤ n

/-- Exact dimensions of the fixed-size indexed arrays. Arena allocation and
trail cursor ordering are separate invariants. -/
structure ArrayBounds (s : State) : Prop where
  firstSize : s.first.size = 2 * (s.nVars + 1)
  marksSize : s.marks.size = 2 * (s.nVars + 1)
  reasonsSize : s.reasons.size = s.nVars + 1
  phasesSize : s.phases.size = s.nVars + 1
  trailSize : s.trail.size = s.nVars + 1
  previousSize : s.previous.size = s.nVars + 1
  nextSize : s.next.size = s.nVars + 1

structure ArenaBounds (s : State) : Prop where
  reserved : 2 ≤ s.arena.size
  fixedLower : 2 ≤ s.fixed
  fixedUpper : s.fixed ≤ s.arena.size

structure TrailBounds (s : State) : Prop where
  forcedProcessed : s.forced ≤ s.processed
  processedAssigned : s.processed ≤ s.assigned
  assignedVars : s.assigned ≤ s.nVars

/-- A clause occupies its exact literal slice followed by a zero terminator.
The two preceding watch-link cells are in bounds because `clauseId ≥ 4`. -/
structure PackedClause (s : State) (clauseId : Nat) (lits : Array Lit) : Prop where
  startLower : 4 ≤ clauseId
  endBound : clauseId + lits.size < s.arena.size
  literals : ∀ i, i < lits.size → s.db (clauseId + i) = lits[i]!
  terminator : s.db (clauseId + lits.size) = 0
  wellFormed : ∀ lit ∈ lits, LiteralBound s.nVars lit

/-- Marks may temporarily carry analysis tags, all of which still denote a
false literal. The complementary literal must remain unmarked. -/
def FalseAssignment (s : State) (lit : Lit) : Prop :=
  s.mark lit ≠ 0 ∧ s.mark lit.negate = 0

def ActiveTrail (s : State) : Prop :=
  ∀ i, i < s.assigned → LiteralBound s.nVars s.trail[i]! ∧
    FalseAssignment s s.trail[i]!

def DistinctTrailVariables (s : State) : Prop :=
  ∀ i j, i < s.assigned → j < s.assigned →
    s.trail[i]!.var = s.trail[j]!.var → i = j

def TrailPhases (s : State) : Prop :=
  ∀ i, i < s.assigned →
    s.phases[s.trail[i]!.var]! = (s.trail[i]! % 2 == 1)

/-- Reasons of assigned variables are decisions or valid clauses containing
the true literal. This does not require a reason to retain its watch order. -/
def ReasonClauses (s : State) : Prop :=
  ∀ i, i < s.assigned → s.reason s.trail[i]! = 0 ∨
    ∃ lits, PackedClause s (s.reason s.trail[i]!) lits ∧ s.trail[i]!.negate ∈ lits

/-- A concrete ordering of all variables. The head follows `previous` towards
zero; `next` is constrained only away from the head, whose unused slot can be
stale after a move-to-front update in the runtime implementation. -/
def MTFOrder (s : State) (order : List Nat) : Prop :=
  order.Nodup ∧ (∀ var, var ∈ order ↔ 1 ≤ var ∧ var ≤ s.nVars) ∧
  s.head = order.headD 0 ∧
  ∀ i, i < order.length →
    s.previous[order.getD i 0]! = order.getD (i + 1) 0 ∧
    (0 < i → s.next[order.getD i 0]! = order.getD (i - 1) 0)

def MTFCoverage (s : State) : Prop := ∃ order, MTFOrder s order

/-- A watch reference addresses one of the two link cells of a clause and
appears on a list for one of that clause's current watched literals. -/
def WatchEntry (s : State) (lit ref : Nat) : Prop :=
  4 ≤ watchClause ref ∧ watchClause ref + 1 < s.arena.size ∧
  watchLinkPos ref < s.arena.size ∧
  (s.db (watchClause ref) = lit ∨ s.db (watchClause ref + 1) = lit)

def WatchList (s : State) (lit : Lit) (refs : List Nat) : Prop :=
  refs.Nodup ∧ s.first[lit]! = refs.headD 0 ∧
  ∀ i, i < refs.length → WatchEntry s lit (refs.getD i 0) ∧
    s.db (watchLinkPos (refs.getD i 0)) = refs.getD (i + 1) 0

/-- The two fixed link cells occur at distinct watched heads. Their order may
swap, so this relation intentionally allows either permutation. -/
def ClauseWatches (heads : Nat → List Nat) (clauseId first second : Nat) : Prop :=
  first ≠ second ∧
    ((2 * clauseId ∈ heads first ∧ 2 * clauseId + 1 ∈ heads second) ∨
     (2 * clauseId ∈ heads second ∧ 2 * clauseId + 1 ∈ heads first))

/-- Ghost clause contents name genuine arena starts; arbitrary terminated
suffixes of a stored clause are not themselves database entries. -/
structure StoredClause where
  id : Nat
  lits : Array Lit

def StoredClause.view (entry : StoredClause) : Std.Sat.CNF.Clause Nat := clauseView entry.lits

/-- The exact consecutive layout, beginning at a watch-header boundary. -/
def DatabaseFrom (s : State) (start : Nat) : List StoredClause → Prop
  | [] => start = s.arena.size
  | entry :: rest => entry.id = start + 2 ∧ PackedClause s entry.id entry.lits ∧
      DatabaseFrom s (entry.id + entry.lits.size + 1) rest

end MicrosatLean.Verification.Implementation.Representation

namespace MicrosatLean.Verification.Implementation.Propagation

open CDCL Representation

/-- A proper watch reference belongs to a genuine long stored clause, rather
than to an arbitrary zero-terminated suffix in the arena. -/
def StoredWatchRef (entries : List StoredClause) (ref : Nat) : Prop :=
  ∃ entry ∈ entries, watchClause ref = entry.id ∧ 2 ≤ entry.lits.size

/-- The pointer component of WatchList, separated from clause membership
while literal cells are temporarily being reoriented by propagation. -/
def WatchLinks (s : State) (lit : Lit) (refs : List Nat) : Prop :=
  refs.Nodup ∧ s.first[lit]! = refs.headD 0 ∧
    ∀ i, i < refs.length → s.db (watchLinkPos (refs.getD i 0)) = refs.getD (i + 1) 0

/-- A simultaneous ghost description of finite watch chains, genuine refs,
both slots of every long stored clause, and unique ownership by literal head.
Literal order is read from the current ghost database, after any permutation. -/
structure WatchCertificate (s : State) (entries : List StoredClause) (heads : Nat → List Nat) : Prop where
  links : ∀ lit, WatchLinks s lit (heads lit)
  references : ∀ lit ref, ref ∈ heads lit → StoredWatchRef entries ref
  covered : ∀ entry ∈ entries, 2 ≤ entry.lits.size →
    ClauseWatches heads entry.id entry.lits[0]! entry.lits[1]!
  unique : ∀ lit other ref, ref ∈ heads lit → ref ∈ heads other → lit = other

end MicrosatLean.Verification.Implementation.Propagation
