import MicrosatLean.Faithful.Memory

/-!
# Faithful port of `upstream/microsat.c`

Each C function is a Lean function with the same name, in the same order as the C
file. `C:NN` refers to lines of `upstream/microsat.c`. Since Lean values are
immutable, a function that mutates `*S` in C takes `S` and returns the updated
`S` (paired with C's return value, if any).

Translation rules:

* Every memory access is `S.ld p` (`*p`) or `S.st p v` (`*p = v`) on the one `DB`.
* `int`s used as booleans are tested with `!= 0`, as C does.
* C `while` loops are Lean `while` loops on C's condition, with no fuel. A C
  condition with a side effect, such as `while (*(++p))`, is written as
  `repeat` + side effect + `if !cond then break`.
* `for` loops with a plain counter use a Lean range over the same bounds.

Deviations, kept to the ones Lean forces:

* `analyze`'s `goto build` (C:109) is a `Bool` flag that ends both loops.
* `solve`'s `for (;;)` (C:162) is split into `step` (one iteration of its body)
  and `run` (the loop), so that proofs can later treat `step` as a transition.
* `parse` (C:216) starts from DIMACS tokens. Reading characters is deferred.
* Out of memory (C:53) and parse errors (C:233) panic, where C exits; after an
  out-of-memory panic the state is left unchanged (`panicWith`).
* `run` and `implied` are defined by `partial_fixpoint` (unfolding equations, no
  termination proof needed to define them). `implied` is not tail-recursive, so it
  returns an `Option` (`none` = C's recursion does not return, unreachable on valid
  states) and its `while (*(++p))` loop is the tail-recursive helper `impliedLoop`.
-/

namespace MicrosatLean.Faithful

-- C:36
/-- Unassign the literal. -/
@[inline] def unassign (S : solver) (lit : CInt) : solver :=
  S.st (S.false + lit) 0

-- C:38–40
/-- Perform a restart (i.e., unassign all variables). -/
def restart (S : solver) : solver := Id.run do
  let mut S := S
  while S.assigned > S.forced do                  -- remove all unforced false lits from falseStack
    S := { S with assigned := S.assigned - 1 }    -- *(--S->assigned)
    S := unassign S (S.ld S.assigned)
  S := { S with processed := S.forced }           -- reset the processed pointer
  return S

-- C:42–47
/-- Make the first literal of the reason true. -/
def assign (S : solver) (reason : Ptr) (forced : CInt) : solver := Id.run do
  let lit := S.ld reason                                       -- let lit be the first literal in the reason
  let mut S := S.st (S.false + -lit) (if forced != 0 then IMPLIED else 1)  -- mark lit as true and IMPLIED if forced
  S := S.st S.assigned (-lit)                                  -- *(S->assigned++) = -lit
  S := { S with assigned := S.assigned + 1 }
  S := S.st (S.reason + abs lit) (1 + reason)                  -- reason[abs(lit)] = 1 + (reason - DB)
  S := S.st (S.model + abs lit) (if lit > 0 then 1 else 0)     -- model[abs(lit)] = (lit > 0)
  return S

-- C:49–50
/-- Add a watch pointer to a clause containing lit. -/
@[inline] def addWatch (S : solver) (lit : CInt) (mem : Ptr) : solver :=
  let S := S.st mem (S.ld (S.first + lit))   -- S->DB[mem] = S->first[lit]
  S.st (S.first + lit) mem                   -- S->first[lit] = mem

-- C:52–57
/-- Allocate memory of size `mem_size`; returns the pointer `store`. -/
def getMemory (S : solver) (mem_size : CInt) : solver × Ptr :=
  if S.mem_used + mem_size > S.mem_max then
    panicWith (S, S.mem_used) "c out of memory"    -- C:54 prints and exits (E3)
  else
    let store : Ptr := S.mem_used                  -- store = S->DB + S->mem_used
    ({ S with mem_used := S.mem_used + mem_size }, store)

-- C:59–66
/-- Add the clause stored in `*in_` of size `size`; returns a pointer to it in DB.
(`in` is a Lean keyword, hence `in_`.) -/
def addClause (S : solver) (in_ : Ptr) (size : CInt) (irr : CInt) : solver × Ptr := Id.run do
  let used := S.mem_used                             -- a pointer to the beginning of the clause
  let (S', store) := getMemory S (size + 3)
  let mut S := S'
  let clause : Ptr := store + 2
  if size > 1 then                                   -- if the clause is not unit, add
    S := addWatch S (S.ld (in_ + 0)) used            -- two watch pointers to the datastructure
    S := addWatch S (S.ld (in_ + 1)) (used + 1)
  for i in (0 : CInt)...size do                      -- copy the clause from the buffer to the database
    S := S.st (clause + i) (S.ld (in_ + i))
  S := S.st (clause + size) 0                        -- clause[i] = 0, with i == size after the loop
  if irr != 0 then S := { S with mem_fixed := S.mem_used }
  else S := { S with nLemmas := S.nLemmas + 1 }
  return (S, clause)

-- C:68–83
/-- Removes "less useful" lemmas from DB. -/
def reduceDB (S : solver) (k : CInt) : solver := Id.run do
  let mut S := S
  while S.nLemmas > S.maxLemmas do                   -- allow more lemmas in the future
    S := { S with maxLemmas := S.maxLemmas + 300 }
  S := { S with nLemmas := 0 }                       -- reset the number of lemmas

  for i in (-S.nVars)...=S.nVars do                  -- loop over the variables
    if i == 0 then continue
    let mut watch : Ptr := S.first + i               -- int* watch = &S->first[i]
    while S.ld watch != END do                       -- as long as there are watched clauses
      if S.ld watch < S.mem_fixed then
        watch := S.ld watch                          -- watch = S->DB + *watch (keep: input clause)
      else
        S := S.st watch (S.ld (S.ld watch))          -- *watch = S->DB[*watch] (unlink: lemma)

  let old_used := S.mem_used
  S := { S with mem_used := S.mem_fixed }            -- virtually remove all lemmas
  let mut i : CInt := S.mem_fixed + 2
  while i < old_used do                              -- for (i = mem_fixed + 2; i < old_used; i += 3)
    let mut count : CInt := 0
    let head := i                                    -- the lemma to which head is pointing
    while S.ld i != 0 do                             -- count the number of literals
      let lit := S.ld i
      i := i + 1
      if (if lit > 0 then 1 else 0) == S.ld (S.model + abs lit) then
        count := count + 1                           -- that are satisfied by the current model
    if count < k then                                -- if the latter is smaller than k, add it back
      S := (addClause S head (i - head) 0).1
    i := i + 3
  return S

-- C:85–91
/-- Move the variable to the front of the decision list. -/
def bump (S : solver) (lit : CInt) : solver := Id.run do
  let mut S := S
  if S.ld (S.false + lit) != IMPLIED then
    S := S.st (S.false + lit) MARK                   -- MARK the literal as involved if not a top-level unit
    let var := abs lit
    if var != S.head then                            -- in case var is not already the head of the list
      S := S.st (S.prev + S.ld (S.next + var)) (S.ld (S.prev + var))   -- update the prev link, and
      S := S.st (S.next + S.ld (S.prev + var)) (S.ld (S.next + var))   -- update the next link, and
      S := S.st (S.next + S.head) var                                  -- add a next link to the head, and
      S := S.st (S.prev + var) S.head                                  -- make var the new head
      S := { S with head := var }
  return S

-- C:93–100
mutual
/-- Check if lit(eral) is implied by MARK literals. `none` would mean C's recursion
never returns; for valid states it always returns (proved: `implied_spec`). On `none`
`analyze` continues with a dummy state: a fallback that mentioned `S` would keep a
second reference to it during the call, so that every write in `implied` would copy
`DB`. The `while (*(++p))` loop (C:97) is the
tail-recursive `impliedLoop`: Lean can only define this non-tail recursion by
`partial_fixpoint` in `Option`, which does not reach into `while` loops. -/
def implied (S : solver) (lit : CInt) : Option (solver × CInt) :=
  if S.ld (S.false + lit) > MARK then                -- if checked before return old result
    some (S, S.ld (S.false + lit) &&& MARK)
  else if S.ld (S.reason + abs lit) == 0 then        -- in case lit is a decision, it is not implied
    some (S, 0)
  else
    impliedLoop S lit (S.ld (S.reason + abs lit) - 1)  -- get the reason of lit(eral)
partial_fixpoint

/-- C:97–100: `while (*(++p))`, with `p` one before the next reason literal. -/
def impliedLoop (S : solver) (lit : CInt) (p : Ptr) : Option (solver × CInt) := do
  let p := p + 1
  if S.ld p == 0 then                                -- end of the reason: mark lit IMPLIED
    return (S.st (S.false + lit) IMPLIED, 1)
  if (S.ld (S.false + S.ld p) ^^^ MARK) != 0 then    -- recursively check if non-MARK literals are implied
    let (S, r) ← implied S (S.ld p)
    if r == 0 then                                   -- mark and return not implied (IMPLIED - 1)
      return (S.st (S.false + lit) (IMPLIED - 1), 0)
    impliedLoop S lit p
  else impliedLoop S lit p
partial_fixpoint
end

-- C:102–130
/-- Compute a resolvent from falsified clause; returns a pointer to the lemma. -/
def analyze (S : solver) (clause : Ptr) : solver × Ptr := Id.run do
  let mut S := S
  let mut clause := clause
  S := { S with res := S.res + 1, nConflicts := S.nConflicts + 1 }  -- bump restarts and update the statistic
  while S.ld clause != 0 do                          -- MARK all literals in the falsified clause
    S := bump S (S.ld clause)                        -- bump (S, *(clause++))
    clause := clause + 1
  -- `goto build` (C:109) leaves both loops below; Lean has no labelled break.
  let mut gotoBuild := false
  repeat                                             -- while (S->reason[abs (*(--S->assigned))])
    S := { S with assigned := S.assigned - 1 }
    if S.ld (S.reason + abs (S.ld S.assigned)) == 0 then break  -- loop until the last decision
    if S.ld (S.false + S.ld S.assigned) == MARK then  -- if the tail of the stack is MARK
      let mut check : Ptr := S.assigned              -- pointer to check if first-UIP is reached
      repeat                                         -- while (S->false[*(--check)] != MARK)
        check := check - 1
        if S.ld (S.false + S.ld check) == MARK then break  -- check for a MARK literal before decision
        if S.ld (S.reason + abs (S.ld check)) == 0 then    -- otherwise it is the first-UIP so break
          gotoBuild := true
          break
      if gotoBuild then break
      clause := S.ld (S.reason + abs (S.ld S.assigned))   -- get the reason and ignore first literal
      while S.ld clause != 0 do                      -- MARK all literals in reason
        S := bump S (S.ld clause)
        clause := clause + 1
    S := unassign S (S.ld S.assigned)                -- unassign the tail of the stack

  -- build:
  let mut size : CInt := 0                           -- build conflict clause; empty the clause buffer
  let mut lbd : CInt := 0
  let mut flag : CInt := 0
  S := { S with processed := S.assigned }            -- int* p = S->processed = S->assigned
  let mut p : Ptr := S.processed                     -- loop from tail to front
  while p ≥ S.forced do                              -- only literals on the stack can be MARKed
    if S.ld (S.false + S.ld p) == MARK then          -- if MARKed and not implied
      let mut r : CInt := 0
      (S, r) := (implied S (S.ld p)).getD (default, 0)
      if r == 0 then
        S := S.st (S.buffer + size) (S.ld p)         -- add literal to conflict clause buffer
        size := size + 1
        flag := 1
    if S.ld (S.reason + abs (S.ld p)) == 0 then      -- increase LBD for a decision with a true flag
      lbd := lbd + flag
      flag := 0
      if size == 1 then S := { S with processed := p }  -- and update the processed pointer
    S := S.st (S.false + S.ld p) 1                   -- reset the MARK flag for all variables on the stack
    p := p - 1                                       -- S->false[*(p--)] = 1

  S := { S with fast := S.fast - (S.fast >>> 5) }    -- update the fast moving average
  S := { S with fast := S.fast + (lbd <<< 15) }
  S := { S with slow := S.slow - (S.slow >>> 15) }   -- update the slow moving average
  S := { S with slow := S.slow + (lbd <<< 5) }

  while S.assigned > S.processed do                  -- loop over all unprocessed literals
    S := unassign S (S.ld S.assigned)                -- unassign (S, *(S->assigned--))
    S := { S with assigned := S.assigned - 1 }
  S := unassign S (S.ld S.assigned)                  -- assigned now equal to processed
  S := S.st (S.buffer + size) 0                      -- terminate the buffer
  return addClause S S.buffer size 0                 -- add new conflict clause to redundant DB

-- C:132–158
/-- Performs unit propagation; returns `SAT`, or `UNSAT` for a root level conflict. -/
def propagate (S : solver) : solver × CInt := Id.run do
  let mut S := S
  let mut forced := S.ld (S.reason + abs (S.ld S.processed))  -- initialize forced flag
  while S.processed < S.assigned do                  -- while unprocessed false literals
    let lit := S.ld S.processed                      -- get first unprocessed literal
    S := { S with processed := S.processed + 1 }
    let mut watch : Ptr := S.first + lit             -- obtain the first watch pointer
    while S.ld watch != END do                       -- while there are watched clauses (watched by lit)
      let mut unit : CInt := 1                       -- let's assume that the clause is unit
      let mut clause : Ptr := S.ld watch + 1         -- get the clause from DB
      if S.ld (clause - 2) == 0 then clause := clause + 1  -- set the pointer to the first literal in the clause
      if S.ld clause == lit then                     -- ensure that the other watched literal is in front
        S := S.st clause (S.ld (clause + 1))
      let mut i : CInt := 2
      while unit != 0 && S.ld (clause + i) != 0 do   -- scan the non-watched literals
        if S.ld (S.false + S.ld (clause + i)) == 0 then  -- when clause[i] is not false, it is either true or unset
          S := S.st (clause + 1) (S.ld (clause + i)) -- swap literals
          S := S.st (clause + i) lit
          let store := S.ld watch                    -- store the old watch
          unit := 0
          S := S.st watch (S.ld (S.ld watch))        -- remove the watch from the list of lit
          S := addWatch S (S.ld (clause + 1)) store  -- add the watch to the list of clause[1]
        i := i + 1
      if unit != 0 then                              -- if the clause is indeed unit
        S := S.st (clause + 1) lit                   -- place lit at clause[1] and update next watch
        watch := S.ld watch
        if S.ld (S.false + -(S.ld clause)) != 0 then continue  -- if the other watched literal is satisfied continue
        if S.ld (S.false + S.ld clause) == 0 then    -- if the other watched literal is falsified,
          S := assign S clause forced                -- a unit clause is found, and the reason is set
        else
          if forced != 0 then return (S, UNSAT)      -- found a root level conflict -> UNSAT
          let mut lemma : Ptr := 0
          (S, lemma) := analyze S clause             -- analyze the conflict return a conflict clause
          if S.ld (lemma + 1) == 0 then forced := 1  -- in case a unit clause is found, set forced flag
          S := assign S lemma forced                 -- assign the conflict clause as a unit
          break
  if forced != 0 then S := { S with forced := S.processed }  -- set S->forced if applicable
  return (S, SAT)                                    -- finally, no conflict was found

/-- The state between two iterations of `solve`'s `for (;;)` loop (C:162), or
the value `solve` returned. -/
inductive Progress where
  | running (S : solver) (decision : CInt)
  | finished (S : solver) (result : CInt)
  deriving Inhabited

-- C:163–179
/-- One iteration of the body of `solve`'s main loop. -/
def step (S : solver) (decision : CInt) : Progress := Id.run do
  let mut S := S
  let mut decision := decision
  let old_nLemmas := S.nLemmas                       -- to see whether propagate adds lemmas
  let mut r : CInt := 0
  (S, r) := propagate S
  if r == UNSAT then return .finished S UNSAT        -- propagation returns UNSAT for a root level conflict

  if S.nLemmas > old_nLemmas then                    -- if the last decision caused a conflict
    decision := S.head                               -- reset the decision heuristic to head
    if S.fast > (S.slow.tdiv 100) * 125 then         -- C `/` truncates: `Int.tdiv`
      S := { S with res := 0, fast := (S.slow.tdiv 100) * 125 }  -- restart and update the averages
      S := restart S
      if S.nLemmas > S.maxLemmas then S := reduceDB S 6  -- reduce the DB when it contains too many lemmas

  while S.ld (S.false + decision) != 0 || S.ld (S.false + -decision) != 0 do  -- as long as decision is assigned
    decision := S.ld (S.prev + decision)             -- replace it with the next variable in the decision list
  if decision == 0 then return .finished S SAT       -- if the end of the list is reached, a solution is found
  decision := if S.ld (S.model + decision) != 0 then decision else -decision  -- phase from the model
  S := S.st (S.false + -decision) 1                  -- assign the decision literal to true
  S := S.st S.assigned (-decision)                   -- and push it on the assigned stack
  S := { S with assigned := S.assigned + 1 }
  decision := abs decision
  S := S.st (S.reason + decision) 0                  -- decisions have no reason clauses
  return .running S decision

/-- `solve`'s `for (;;)` (C:162): iterate `step` until it returns.

`partial_fixpoint` defines `run` as the least solution of its equation (the
tail call makes that always possible), with no termination proof. Proofs can
unfold it with `run.eq_1`. On a state where C's loop runs forever, `run` is an
unspecified value; termination from valid states is a theorem to prove later.
The compiled code is the plain recursive loop. -/
def run (S : solver) (decision : CInt) : solver × CInt :=
  match step S decision with
  | .finished S result => (S, result)
  | .running S decision => run S decision
partial_fixpoint

-- C:160–162
/-- Determine satisfiability. -/
def solve (S : solver) : solver × CInt :=
  let decision := S.head                             -- initialize the solver
  let S := { S with res := 0 }
  run S decision

-- C:181–210
/-- Allocate and initialize the solver. Fields C leaves uninitialized
(`mem_fixed` until the first input clause, `res` until `solve`) start at 0.
`mem_max` is C's constant `1 << 30` by default; it is a parameter so that the
proofs can state how much memory suffices (`ASSUMPTIONS.md`, E3). -/
def initCDCL (n m : CInt) (mem_max : CInt := 1 <<< 30) : solver := Id.run do
  let n := if n < 1 then 1 else n                    -- the code assumes that there is at least one variable
  let mut S : solver := {
    DB := #[]                                        -- malloc: an all-zero block (see `ld`/`st`)
    nVars := n                                       -- set the number of variables
    nClauses := m                                    -- set the number of clauses
    mem_max := mem_max                               -- set the initial maximum memory (C: 1 << 30)
    mem_used := 0                                    -- the number of integers allocated in the DB
    nLemmas := 0                                     -- the number of learned clauses
    nConflicts := 0                                  -- number of conflicts used to update scores
    maxLemmas := 2000                                -- initial maximum number of learned clauses
    fast := 1 <<< 24                                 -- initialize the fast and slow moving averages
    slow := 1 <<< 24
    mem_fixed := 0, buffer := 0, model := 0, reason := 0, falseStack := 0, «false» := 0, first := 0
    forced := 0, processed := 0, assigned := 0, next := 0, prev := 0, head := 0, res := 0 }

  let mut p : Ptr := 0
  (S, p) := getMemory S (n + 1); S := { S with model := p }       -- full assignment of the variables
  (S, p) := getMemory S (n + 1); S := { S with next := p }        -- next variable in the heuristic order
  (S, p) := getMemory S (n + 1); S := { S with prev := p }        -- previous variable in the heuristic order
  (S, p) := getMemory S n;       S := { S with buffer := p }      -- a buffer to store a temporary clause
  (S, p) := getMemory S (n + 1); S := { S with reason := p }      -- array of clauses
  (S, p) := getMemory S (n + 1); S := { S with falseStack := p }  -- stack of falsified literals
  S := { S with forced := S.falseStack }             -- points inside *falseStack at first decision
  S := { S with processed := S.falseStack }          -- points inside *falseStack at first unprocessed literal
  S := { S with assigned := S.falseStack }           -- points inside *falseStack at last unprocessed literal
  (S, p) := getMemory S (2 * n + 1); S := { S with «false» := p }; S := { S with «false» := S.false + n }
  (S, p) := getMemory S (2 * n + 1); S := { S with first := p };   S := { S with first := S.first + n }
  S := S.st S.mem_used 0                             -- make sure there is a 0 before the clauses are loaded
  S := { S with mem_used := S.mem_used + 1 }

  for i in (1 : CInt)...=n do                        -- initialize the main datastructures:
    S := S.st (S.prev + i) (i - 1)                   -- the double-linked list for variable-move-to-front,
    S := S.st (S.next + (i - 1)) i
    S := S.st (S.false + i) 0                        -- model[i] = false[-i] = false[i] = 0 (right to left):
    S := S.st (S.false + -i) 0                       -- the model (phase-saving), the false array,
    S := S.st (S.model + i) 0
    S := S.st (S.first + -i) END                     -- first[i] = first[-i] = END (right to left):
    S := S.st (S.first + i) END                      -- and first (watch pointers)
  S := { S with head := n }                          -- initialize the head of the double-linked list
  return S

-- C:216–243
/-- Initialize from a DIMACS header (`nVars`, `nClauses`) and the literal tokens
that follow it, with `0` ending each clause. This is C's `parse` after its
character-level reading (C:217–222, C:227–231), which is deferred. -/
def parse (nVars nClauses : CInt) (tokens : Array CInt) (mem_max : CInt := 1 <<< 30) :
    solver × CInt := Id.run do
  let mut S := initCDCL nVars nClauses mem_max       -- allocate the main datastructures
  let mut nZeros := S.nClauses                       -- initialize the number of clauses to read
  let mut size : CInt := 0
  let mut next : Nat := 0                            -- position in the token stream
  while nZeros > 0 do                                -- while there are clauses in the file
    let some lit := tokens[next]?                    -- read a literal
      | return panic! "s parse error: header incorrect"  -- C:233 prints and exits (deferred)
    next := next + 1
    if lit == 0 then                                 -- if reaching the end of the clause
      let mut clause : Ptr := 0
      (S, clause) := addClause S S.buffer size 1     -- then add the clause to data_base
      if size == 0 || (size == 1 && S.ld (S.false + S.ld clause) != 0) then
        return (S, UNSAT)                            -- empty clause or conflicting unit
      if size == 1 && S.ld (S.false + -(S.ld clause)) == 0 then  -- check for a new unit
        S := assign S clause 1                       -- directly assign new units (forced = 1)
      size := 0                                      -- reset buffer
      nZeros := nZeros - 1
    else
      S := S.st (S.buffer + size) lit                -- add literal to buffer
      size := size + 1
  return (S, SAT)                                    -- return that no conflict was observed

end MicrosatLean.Faithful
