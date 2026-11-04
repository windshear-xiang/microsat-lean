import MicrosatLean.Verification.Model

namespace MicrosatLean.Verification

/-!
Review the predicates, not only their names. None asserts future preservation,
successful execution or termination. `Certificate` separates logical meaning,
present storage/control facts and progress facts. Histories are proof-only
facts about retained decision prefixes, not runtime copies of old machines.
-/

/-- Reason tails precede their head in the true-literal trail. Root entries
additionally follow from the input without any decision assumptions. -/
structure SemanticInv (input : CNF) (a : LogicalState) : Prop where
  original : Std.Sat.CNF.BiEntails input (databaseView a.original)
  learned : Std.Sat.CNF.Entails input (databaseView a.learned)
  rootBound : a.rootSize ≤ a.trail.length
  trailBound : a.trail.length ≤ a.numVars
  declaredTrail : ∀ lit ∈ a.trueTrail, LiteralBound a.numVars lit
  distinct : (a.trueTrail.map Prod.fst).Nodup
  declaredClauses : ∀ clause ∈ a.database, ∀ lit ∈ clause, LiteralBound a.numVars lit
  nonempty : ∀ clause ∈ a.database, clause.literals ≠ []
  reasons : ∀ i, i < a.trail.length → ∀ clause,
    a.trail[i]!.reason = some clause →
      Std.Sat.CNF.EntailsClause input clause ∧
      clause.literals.head? = some a.trail[i]!.literal ∧
      ∀ lit ∈ clause.literals.tail, FalseIn (prefixLiterals a i) lit
  roots : ∀ lit ∈ prefixLiterals a a.rootSize,
    ∀ valuation, Std.Sat.CNF.Sat valuation input → valuation lit.1 = lit.2

/-- Facts saved at each surviving nonroot decision boundary. Newly learned
clauses must also satisfy this property; their birth proof is an obligation. -/
def DecisionHistory (a : LogicalState) : Prop :=
  ∀ i, a.rootSize ≤ i → i < a.trail.length → a.trail[i]!.reason = none →
    ∀ clause ∈ a.database, UnitClosed (prefixLiterals a i) clause

def FalseBefore (a : LogicalState) (count : Nat) (lit : Lit) : Prop :=
  FalseIn (prefixLiterals a count) (literalView lit)

def TrueBefore (a : LogicalState) (count : Nat) (lit : Lit) : Prop :=
  TrueIn (prefixLiterals a count) (literalView lit)

def otherWatch (entry : StoredClause) (lit : Lit) : Lit :=
  if entry.lits[0]! == lit then entry.lits[1]! else entry.lits[0]!

def SettledWatch (a : LogicalState) (w : RepresentationWitness)
    (count : Nat) (lit : Lit) (ref : Nat) : Prop :=
  ∀ entry ∈ w.entries, CDCL.watchClause ref = entry.id →
    TrueBefore a count (otherWatch entry lit)

/-- Previously processed false literals have true opposite-watch witnesses.
Those witnesses may be pending assignments anywhere on the active trail. -/
def SettledPrefix (a : LogicalState) (w : RepresentationWitness) (count : Nat) : Prop :=
  ∀ lit, FalseBefore a count lit → ∀ ref ∈ w.heads lit,
    SettledWatch a w a.trail.length lit ref

def SettledCursor (a : LogicalState) (w : RepresentationWitness)
    (lit : Lit) (remaining : List Nat) : Prop :=
  ∀ ref ∈ w.heads lit, ref ∉ remaining → SettledWatch a w a.trail.length lit ref

def SavedWatches (a : LogicalState) (w : RepresentationWitness) : Prop :=
  ∀ i, a.rootSize ≤ i → i < a.trail.length → a.trail[i]!.reason = none →
    ∀ lit, FalseBefore a i lit → ∀ ref ∈ w.heads lit, SettledWatch a w i lit ref

/-- The cursor is after exactly the visited prefix, or at its head. -/
def WatchCursor (w : RepresentationWitness) (lit : Lit) (previous : Nat)
    (remaining : List Nat) : Prop :=
  (previous = 0 ∧ remaining = w.heads lit) ∨
    ∃ visited, w.heads lit = visited ++ previous :: remaining

def Assigned (a : LogicalState) (var : Nat) : Prop := ∃ lit ∈ a.trueTrail, lit.1 = var

def DecisionCursor (a : LogicalState) (w : RepresentationWitness) (cursor : Nat) : Prop :=
  ∃ position, position ≤ w.order.length ∧ cursor = w.order.getD position 0 ∧
    ∀ i, i < position → Assigned a (w.order.getD i 0)

def LevelCover (a : LogicalState) : Prop :=
  ∀ i, a.rootSize ≤ i → i < a.trail.length →
    ∃ decision, a.rootSize ≤ decision ∧ decision ≤ i ∧ a.trail[decision]!.reason = none

def SixBefore (s : CDCL.State) : Prop :=
  ∀ i, i < s.assigned → s.mark s.trail[i]! = 6 → i < s.forced

def NonrootMode (m : CDCL.Machine) (a : LogicalState) : Prop :=
  a.rootSize < a.trail.length ∧ LevelCover a ∧ SixBefore m.solver

def PropagationMode (m : CDCL.Machine) (a : LogicalState) : Prop :=
  (m.root = true → ∀ i, i < m.solver.assigned → m.solver.mark m.solver.trail[i]! = 6) ∧
  (m.root = false → NonrootMode m a)

/-- An idle next-literal phase may have a root-only trail with a false mode
flag. An active watch phase cannot: its conflict branch needs a real nonroot
decision when root is false. Keeping these cases separate excludes unreachable
states without restricting any input formula or configuration. -/
def NextMode (m : CDCL.Machine) (a : LogicalState) : Prop :=
  (m.root = true → ∀ i, i < m.solver.assigned → m.solver.mark m.solver.trail[i]! = 6) ∧
  (m.root = false → a.trail.length = a.rootSize ∨ NonrootMode m a)

def BeginEvidence (m : CDCL.Machine) (a : LogicalState) : Prop :=
  (m.solver.processed = 0 ∧ m.solver.forced = 0 ∧
    ∀ i, i < m.solver.assigned → m.solver.mark m.solver.trail[i]! = 6 ∧
      m.solver.reason m.solver.trail[i]! ≠ 0) ∨
  (NonrootMode m a ∧ m.solver.processed + 1 = m.solver.assigned ∧
    m.solver.reason m.solver.trail[m.solver.processed]! = 0)

def PhaseInv (m : CDCL.Machine) (a : LogicalState) (w : RepresentationWitness) : Prop :=
  match m.phase with
  | .beginPropagation => BeginEvidence m a ∧ DecisionCursor a w m.decision ∧
      m.oldLemmas = 0 ∧ m.root = false ∧ m.currentLit = 0 ∧ m.previousWatch = 0 ∧
      SettledPrefix a w m.solver.processed
  | .nextLiteral => NextMode m a ∧ m.currentLit = 0 ∧ m.previousWatch = 0 ∧
      SettledPrefix a w m.solver.processed
  | .watch => PropagationMode m a ∧ 0 < m.solver.processed ∧
      m.currentLit = m.solver.trail[m.solver.processed - 1]! ∧
      ∃ remaining, WatchCursor w m.currentLit m.previousWatch remaining ∧
        SettledCursor a w m.currentLit remaining ∧ SettledPrefix a w (m.solver.processed - 1)
  | .choose => m.solver.processed = m.solver.assigned ∧ m.currentLit = 0 ∧ m.previousWatch = 0 ∧
      LevelCover a ∧ SixBefore m.solver ∧ SettledPrefix a w m.solver.processed

structure ControlInv (input : CNF) (m : CDCL.Machine) (a : LogicalState)
    (w : RepresentationWitness) : Prop where
  history : DecisionHistory a
  saved : SavedWatches a w
  units : ∀ clause ∈ a.database, clause.literals.length = 1 →
    ∀ lit ∈ clause, TrueIn a.trueTrail lit
  cursor : m.solver.nLemmas ≤ m.oldLemmas → DecisionCursor a w m.decision
  oldCount : m.oldLemmas ≤ m.solver.nLemmas
  tags : ∀ i, i < m.solver.assigned →
    let tag := m.solver.mark m.solver.trail[i]!
    tag = 1 ∨ tag = 2 ∨ tag = 5 ∨ tag = 6
  rootTags : ∀ i, i < a.trail.length → m.solver.mark m.solver.trail[i]! = 6 →
    ∀ valuation, Std.Sat.CNF.Sat valuation input →
      valuation a.trail[i]!.literal.1 = a.trail[i]!.literal.2
  rootPrefix : ∀ i, i < m.solver.forced → m.solver.mark m.solver.trail[i]! = 6
  phase : PhaseInv m a w

/-- One polarity choice per declared variable, independent of clause order. -/
def canonicalKey (variables : Nat) (clause : Clause) : List (Option Bool) :=
  (List.range variables).map fun i =>
    if (i + 1, true) ∈ clause then some true
    else if (i + 1, false) ∈ clause then some false else none

structure ProgressInv (a : LogicalState) : Prop where
  normalized : ∀ clause ∈ a.database, clause.literals.Nodup ∧
    (clause.literals.map Prod.fst).Nodup
  distinctLearned : (a.learned.map (canonicalKey a.numVars)).Nodup

/-- The internal padding is fixed by the real initializer, including n = 0. -/
structure Certificate (formula : Formula) (m : CDCL.Machine)
    (a : LogicalState) (w : RepresentationWitness) : Prop where
  input : WellFormed formula
  variables : a.numVars = max 1 formula.numVars
  representation : Rep m a w
  semantic : SemanticInv (formulaView formula) a
  control : ControlInv (formulaView formula) m a w
  progress : ProgressInv a

def Inv (formula : Formula) (m : CDCL.Machine) : Prop :=
  ∃ a w, Certificate formula m a w

end MicrosatLean.Verification
