import MicrosatLean.CDCL.Search

open MicrosatLean MicrosatLean.CDCL

namespace CDCLTests

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)

private def lits (values : Array Int) : Array Lit := values.map Lit.ofInt

private def formula (n : Nat) (clauses : Array (Array Int)) : Formula :=
  ⟨n, clauses.map lits⟩

private def state (f : Formula) : IO State :=
  match initState f with
  | .ok (some s) => pure s
  | .ok none => throw (IO.userError "test expected an initially consistent formula")
  | .error message => throw (IO.userError message)

private def readClause (s : State) (clauseId : Nat) : Array Lit := Id.run do
  let mut result := #[]
  for i in [clauseId:s.arena.size] do
    let lit := s.db i
    if lit == 0 then break
    result := result.push lit
  return result

private def positiveDecision (s : State) (var : Nat) : State :=
  ({ s with phases := s.phases.set! var true }).decide var

/-- Independent representation checks for the linked watch lists. -/
private def validWatches (s : State) : Bool := Id.run do
  let mut heads := Array.replicate (2 * s.arena.size + 2) 0
  for lit in [2:s.first.size] do
    let mut ref := s.first[lit]!
    for _ in [:s.arena.size] do
      if ref == 0 then break
      let clauseId := watchClause ref
      if ref >= heads.size || clauseId < 4 || clauseId + 1 >= s.arena.size then
        return false
      if heads[ref]! != 0 then return false
      heads := heads.set! ref lit
      if s.db clauseId != lit && s.db (clauseId + 1) != lit then return false
      ref := s.db (watchLinkPos ref)
    if ref != 0 then return false
  let mut start := 2
  for _ in [:s.arena.size] do
    if start >= s.arena.size then break
    let clauseId := start + 2
    let clause := readClause s clauseId
    let firstHead := heads[2 * clauseId]!
    let secondHead := heads[2 * clauseId + 1]!
    if clause.size > 1 then
      if firstHead == secondHead then return false
      if !((firstHead == clause[0]! && secondHead == clause[1]!) ||
          (firstHead == clause[1]! && secondHead == clause[0]!)) then return false
    else if firstHead != 0 || secondHead != 0 then
      return false
    start := clauseId + clause.size + 1
  return start == s.arena.size

private def watchChecks : IO Unit := do
  let s ← state (formula 2 #[#[1, 2]])
  check (validWatches s) "watch fixture must begin with valid watches"
  let first := Lit.ofInt 1
  let second := Lit.ofInt 2
  let firstRef := s.first[first]!
  let secondRef := s.first[second]!
  -- Both references still exist, but both incorrectly watch the first literal.
  let corrupted := { s with
    first := s.first.set! second 0
    arena := s.arena.set! (watchLinkPos firstRef) secondRef }
  check (!validWatches corrupted) "two clause references on one literal head must be rejected"
  check (validWatches s) "the original watch state must remain intact"

private def analysisChecks : IO Unit := do
  -- A branching implication diamond resolves through both implications to
  -- the decision, learning a root unit and undoing the entire decision level.
  let s ← state (formula 3 #[])
  let (s, bReason) := s.addClause (lits #[2, -1]) true
  let (s, cReason) := s.addClause (lits #[3, -1]) true
  let (s, conflict) := s.addClause (lits #[-2, -3]) true
  let s := ((positiveDecision s 1).assign bReason false).assign cReason false
  let (s, learned) := analyze s conflict
  check (readClause s learned == lits #[-1]) "diamond should learn the negated decision"
  check (s.assigned == 0 && s.processed == 0) "root-unit analysis must empty the nonroot trail"
  check (s.fast == 16777216 - (16777216 >>> 5) + (1 <<< 15)) "diamond LBD should be one"
  check (validWatches s) "analysis must preserve complete watch lists"

  -- A nondecision first UIP must be retained. Backjumping removes the entire
  -- second level, including its unmarked decision, while keeping level one.
  let s ← state (formula 4 #[])
  let (s, cReason) := s.addClause (lits #[3, -2]) true
  let (s, dReason) := s.addClause (lits #[4, -3]) true
  let (s, conflict) := s.addClause (lits #[-3, -4, -1]) true
  let s := positiveDecision (positiveDecision s 1) 2
  let s := (s.assign cReason false).assign dReason false
  let (s, learned) := analyze s conflict
  check (readClause s learned == lits #[-3, -1]) "analysis must stop at the first UIP"
  check (s.assigned == 1 && s.processed == 1) "backjump must remove the prior decision of the UIP level"
  check (s.mark (Lit.ofInt (-1)) == 1 && s.mark (Lit.ofInt (-2)) == 0 &&
    s.mark (Lit.ofInt (-3)) == 0 && s.mark (Lit.ofInt (-4)) == 0)
    "backjump must preserve exactly the lower-level assignment"
  let s := s.assign learned false
  check (s.mark (Lit.ofInt 3) == 1 && s.reason (Lit.ofInt 3) == learned)
    "learned clause must assert its first literal after backjump"

  -- An earlier implied literal is redundant when its reason depends only on
  -- another marked literal. Its assignment nevertheless remains after backjump.
  let s ← state (formula 3 #[])
  let (s, bReason) := s.addClause (lits #[2, -1]) true
  let (s, conflict) := s.addClause (lits #[-1, -2, -3]) true
  let s := positiveDecision ((positiveDecision s 1).assign bReason false) 3
  let (s, learned) := analyze s conflict
  check (readClause s learned == lits #[-3, -1]) "recursive minimization must remove the implied literal"
  check (s.assigned == 2 && s.mark (Lit.ofInt (-2)) == 1)
    "minimization must preserve lower-level implied assignments and clear cached tags"

  -- The minimization cache has distinct true and false states; exhaustion is
  -- conservative and never discards a literal without establishing implication.
  let s ← state (formula 2 #[])
  let (s, reason) := s.addClause (lits #[2, -1]) true
  let s := (positiveDecision s 1).assign reason false
  let (failed, answer) := implied 3 (s.setMark (Lit.ofInt (-2)) 2) (Lit.ofInt (-2))
  check (!answer && failed.mark (Lit.ofInt (-2)) == 5) "failed minimization must cache tag five"
  let marked := (s.setMark (Lit.ofInt (-1)) 2).setMark (Lit.ofInt (-2)) 2
  let (cached, answer) := implied 3 marked (Lit.ofInt (-2))
  check (answer && cached.mark (Lit.ofInt (-2)) == 6) "successful minimization must cache tag six"
  check ((implied 1 cached (Lit.ofInt (-2))).2) "cached implication must be reusable"
  check (!(implied 0 marked (Lit.ofInt (-2))).2) "exhausted minimization must retain the literal"

private def restartChecks : IO Unit := do
  let s ← state (formula 3 #[#[1], #[3, 2]])
  let s := { s with forced := s.assigned, processed := s.assigned }
  let (s, reason) := s.addClause (lits #[3, 2]) false
  let s := (s.decide 2).assign reason false
  let restarted := s.restart
  check (restarted.assigned == 1 && restarted.processed == 1 && restarted.forced == 1)
    "restart must retain the forced prefix"
  check (restarted.mark (Lit.ofInt (-1)) == 6 && restarted.mark (Lit.ofInt 2) == 0 &&
    restarted.mark (Lit.ofInt (-3)) == 0) "restart must clear every nonroot mark"
  check (restarted.phases == s.phases) "restart must preserve saved phases"
  check (restarted.stats.restarts == s.stats.restarts + 1) "restart must update its statistic"

private def reductionChecks : IO Unit := do
  let f := formula 4 #[#[1], #[2, -1], #[3, -2]]
  let s ← state f
  let (s, bReason) := s.addClause (lits #[2, -1]) false
  let s := s.assign bReason true
  let (s, _) := s.addClause (lits #[1, 2, 3, 4]) false
  let (s, cReason) := s.addClause (lits #[3, -2]) false
  let s := s.assign cReason true
  let (s, _) := s.addClause (lits #[1, 4]) false
  let s := { s with forced := s.assigned, processed := s.assigned, maxLemmas := 0 }
  check (validWatches s) "reduction fixture must begin with valid watches"
  let reduced := s.reduceDB 2
  check (reduced.nLemmas == 3 && reduced.stats.removedLearned == 1)
    "reduction must discard exactly the phase-satisfied long lemma"
  check (reduced.maxLemmas == 300 && reduced.stats.reductions == 1)
    "reduction must grow the limit in source-compatible increments"
  check (reduced.arena.extract 0 reduced.fixed == s.arena.extract 0 s.fixed)
    "reduction must preserve the original arena prefix"
  check (readClause reduced (reduced.reason (Lit.ofInt 2)) == lits #[2, -1] &&
    readClause reduced (reduced.reason (Lit.ofInt 3)) == lits #[3, -2])
    "compaction must remap retained root reasons to their clauses"
  check (reduced.reason (Lit.ofInt 3) != cReason) "root reason test must exercise an actual relocation"
  check (validWatches reduced) "compaction must rebuild complete acyclic watch lists"
  check (reduced.trail == s.trail && reduced.marks == s.marks && reduced.phases == s.phases)
    "reduction must preserve assignments and phases"

  -- Force the adaptive restart and reduction branches through the actual
  -- search transition, then resume to a model of the original formula.
  let s := { s with fast := 1, slow := 0, config := { reductionK := 2 } }
  match step { solver := s, decision := s.head, phase := .choose, oldLemmas := 3 } with
  | .finished _ => throw (IO.userError "forced reduction should leave variable four to decide")
  | .running machine =>
    check (machine.solver.stats.restarts == 1 && machine.solver.stats.reductions == 1 &&
      machine.solver.nLemmas == 3) "search transition must execute restart and reduction"
    check (validWatches machine.solver) "search reduction must retain valid watch lists"
    match runFor 1000 machine with
    | .finished (.sat model _) => check (f.satisfiedBy model) "resumed reduction search returned an invalid model"
    | _ => throw (IO.userError "resumed reduction search should finish SAT")

private def resume (fuel : Nat) : Progress → Progress
  | .running machine => runFor fuel machine
  | result@(.finished _) => result

private def bruteForce (f : Formula) : Bool := Id.run do
  for bits in [:2 ^ f.numVars] do
    let mut model := Array.replicate (f.numVars + 1) false
    for var in [1:f.numVars + 1] do
      model := model.set! var ((bits >>> (var - 1)) &&& 1 != 0)
    if f.satisfiedBy model then return true
  return false

private def checkResult (f : Formula) (expected : Bool) (progress : Progress) : IO Unit :=
  match progress with
  | .running _ => throw (IO.userError "small regression formula exhausted its transition budget")
  | .finished (.sat model _) => do
    check expected "bounded search incorrectly classified an UNSAT formula as SAT"
    check (f.satisfiedBy model) "bounded search returned an invalid SAT model"
  | .finished (.unsat _) => check (!expected) "bounded search incorrectly classified a SAT formula as UNSAT"

private def chunkChecks : IO Unit := do
  let examples := #[formula 0 #[], formula 4 #[#[1, 2, 3, 4], #[-1], #[-2], #[-3]],
    formula 2 #[#[1, 2], #[1, -2], #[-1, 2], #[-1, -2]],
    formula 3 #[#[2, -1], #[3, -1], #[-2, -3]]]
  for f in examples do
    let s ← state f
    let machine : Machine := { solver := s, decision := s.head }
    for first in #[0, 1, 2, 7, 31] do
      for second in #[0, 1, 3, 11, 100] do
        let combined := runFor (first + second) machine
        let split := resume second (runFor first machine)
        check (reprStr combined == reprStr split) "runFor chunking must preserve the entire machine and result"
    checkResult f (bruteForce f) (runFor 10000 machine)

private def exhaustiveChecks : IO Unit := do
  -- Every subset of the four unit and four binary clauses over two variables.
  let candidates := #[#[1], #[-1], #[2], #[-2], #[1, 2], #[1, -2], #[-1, 2], #[-1, -2]]
  for mask in [:256] do
    let mut clauses := #[]
    for idx in [:candidates.size] do
      if (mask >>> idx) &&& 1 != 0 then clauses := clauses.push candidates[idx]!
    let f := formula 2 clauses
    let expected := bruteForce f
    match initState f with
    | .error message => throw (IO.userError message)
    | .ok none => check (!expected) "initialization rejected a satisfiable exhaustive formula"
    | .ok (some s) =>
      checkResult f expected (runFor 10000 { solver := s, decision := s.head })

def run : IO Unit := do
  watchChecks
  analysisChecks
  restartChecks
  reductionChecks
  chunkChecks
  exhaustiveChecks
  IO.println "CDCL regressions passed: watches, analysis, restart, reduction, chunking, and 256 exhaustive formulas"

end CDCLTests

def main : IO Unit := CDCLTests.run
