import MicrosatLean.Verification.Implementation.Representation.Types

namespace MicrosatLean.Verification

/-!
The logical trail records TRUE literals; the executable trail records their
complements. Reasons are logical clauses here, not numeric arena addresses.
`RepresentationWitness` supplies one shared packed layout and watch/order
description. `Rep` relates present data only: it assumes no future behavior.
-/

structure TrailEntry where
  literal : Literal
  reason : Option Clause
  deriving Inhabited

structure LogicalState where
  numVars : Nat
  original : List Clause
  learned : List Clause
  trail : List TrailEntry
  rootSize : Nat

def LogicalState.database (a : LogicalState) : List Clause := a.original ++ a.learned

def LogicalState.trueTrail (a : LogicalState) : List Literal := a.trail.map TrailEntry.literal

def databaseView (clauses : List Clause) : CNF := ⟨clauses.toArray⟩

def TrueIn (trail : List Literal) (lit : Literal) : Prop := lit ∈ trail

def FalseIn (trail : List Literal) (lit : Literal) : Prop := lit.negate ∈ trail

def Compatible (a : Assignment) (trail : List Literal) : Prop :=
  ∀ lit ∈ trail, a lit.1 = lit.2

def Unassigned (trail : List Literal) (var : Nat) : Prop :=
  ∀ lit ∈ trail, lit.1 ≠ var

def LiteralBound (variables : Nat) (lit : Literal) : Prop := 0 < lit.1 ∧ lit.1 ≤ variables

def UnitClosed (trail : List Literal) (clause : Clause) : Prop :=
  ∀ head ∈ clause, (∀ tail ∈ clause, tail ≠ head → FalseIn trail tail) → TrueIn trail head

def Closed (a : LogicalState) : Prop := ∀ clause ∈ a.database, UnitClosed a.trueTrail clause

def Complete (a : LogicalState) : Prop :=
  ∀ var, 0 < var → var ≤ a.numVars → ∃ lit ∈ a.trueTrail, lit.1 = var

def Conflict (a : LogicalState) (clause : Clause) : Prop :=
  ∀ lit ∈ clause, FalseIn a.trueTrail lit

def prefixLiterals (a : LogicalState) (count : Nat) : List Literal :=
  (a.trail.take count).map TrailEntry.literal

abbrev StoredClause := Implementation.Representation.StoredClause

structure RepresentationWitness where
  original : List StoredClause
  learned : List StoredClause
  heads : Lit → List Nat
  order : List Nat

def RepresentationWitness.entries (w : RepresentationWitness) : List StoredClause :=
  w.original ++ w.learned

abbrev ArrayBounds := Implementation.Representation.ArrayBounds

abbrev PackedClause (s : CDCL.State) (entry : StoredClause) :=
  Implementation.Representation.PackedClause s entry.id entry.lits

abbrev DatabaseFrom := Implementation.Representation.DatabaseFrom

abbrev WatchRepresentation (s : CDCL.State) (w : RepresentationWitness) :=
  Implementation.Propagation.WatchCertificate s w.entries w.heads

abbrev OrderRepresentation := Implementation.Representation.MTFOrder

/-- Numeric storage and the logical state share this single witness. Array
contents outside the active trail may be stale; they are not assignments. -/
structure Rep (m : CDCL.Machine) (a : LogicalState) (w : RepresentationWitness) : Prop where
  variables : a.numVars = m.solver.nVars
  arrays : ArrayBounds m.solver
  reserved : 2 ≤ m.solver.arena.size
  layout : DatabaseFrom m.solver 2 w.entries
  fixed : m.solver.fixed = 2 + (w.original.map fun e => e.lits.size + 3).sum
  count : m.solver.nLemmas = w.learned.length
  original : a.original = w.original.map Implementation.Representation.StoredClause.view
  learned : a.learned = w.learned.map Implementation.Representation.StoredClause.view
  trailLength : a.trail.length = m.solver.assigned
  rootSize : a.rootSize = m.solver.forced
  cursors : m.solver.forced ≤ m.solver.processed ∧
    m.solver.processed ≤ m.solver.assigned ∧ m.solver.assigned ≤ m.solver.nVars
  trail : ∀ i, i < m.solver.assigned →
    a.trail[i]!.literal = (literalView m.solver.trail[i]!).negate
  active : ∀ i, i < m.solver.assigned →
    m.solver.mark m.solver.trail[i]! ≠ 0 ∧ m.solver.mark m.solver.trail[i]!.negate = 0
  marks : ∀ lit, m.solver.mark lit ≠ 0 ↔
    ∃ i, i < m.solver.assigned ∧ m.solver.trail[i]! = lit
  phases : ∀ i, i < a.trail.length →
    m.solver.phases[a.trail[i]!.literal.1]! = a.trail[i]!.literal.2
  reasons : ∀ i, i < m.solver.assigned →
    match a.trail[i]!.reason with
    | none => m.solver.reason m.solver.trail[i]! = 0
    | some clause => ∃ entry ∈ w.entries,
        entry.id = m.solver.reason m.solver.trail[i]! ∧ entry.view = clause
  watches : WatchRepresentation m.solver w
  order : OrderRepresentation m.solver w.order

theorem databaseView_sat_iff (clauses : List Clause) (a : Assignment) :
    Std.Sat.CNF.Sat a (databaseView clauses) ↔
      ∀ clause ∈ clauses, Std.Sat.CNF.Clause.Sat a clause := by
  simp [Std.Sat.CNF.sat_iff_all_mem_sat, databaseView, Std.Sat.CNF.Internal.mem_iff]

end MicrosatLean.Verification
