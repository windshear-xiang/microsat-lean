/-!
# Fast port of `upstream/microsat.c`

Same search as C (same decisions, propagations, conflicts and lemmas), with a
representation chosen for speed (see `FAST_PORT_NOTES.md`):

* `db` is C's arena with C's layout, as an `Array Int32` (C's `int`).
* The array offsets (`next`, `prev`, …) never change after `initCDCL`; they live in
  the read-only `Lay`. The mutable scalars live in `St`, unboxed.
* Every loop is a self tail-recursive function (compiled to a C loop, no
  allocation per iteration). The hot loops of `propagate` take `db` and the trail
  pointers as separate arguments, so that no structure is rebuilt per write.
* Running out of memory is an outcome (`OOM`) instead of an exit.
-/

namespace MicrosatLean.Fast

/-- C's `int`. -/
abbrev Cell := Int32

/-- Numerals of type `Int32` built from a `UInt32` literal: they compile to C literals. (The
default instance goes through `Int32.ofNat`, which the compiler computes once at run time
and checks at every use.) Definitionally equal to the default one. -/
scoped instance (priority := high) instOfNatCell (n : Nat) : OfNat Int32 n := ⟨⟨OfNat.ofNat n⟩⟩

/-- C:30. Negative constants as two's complement literals. -/
@[inline] def END : Cell := ⟨4294967287⟩
/-- `-1`, the pointer `addClause` returns when memory runs out. -/
@[inline] def NONE : Cell := ⟨4294967295⟩
@[inline] def MARK : Cell := 2
@[inline] def IMPLIED : Cell := 6

/-- Results: C's `UNSAT`/`SAT`, and out of memory (C prints `c out of memory`). -/
@[inline] def UNSAT : UInt8 := 0
@[inline] def SAT : UInt8 := 1
@[inline] def OOM : UInt8 := 2
/-- C:233 (`s parse error: header incorrect`): the tokens end before `nClauses` zeros. -/
@[inline] def PARSE_ERROR : UInt8 := 3

/-- C's `mem_max` (C:186). -/
@[inline] def memMax : Cell := 1073741824

@[inline] def absC (x : Cell) : Cell := if x < 0 then -x else x

/-- `DB[p]`; cells beyond the physical array read as 0 (C's zeroed block). A negative
`p` maps beyond the array as well. -/
@[inline] def ld (db : Array Cell) (p : Cell) : Cell :=
  let i := p.toUInt32.toUSize
  if h : i < db.usize then
    db.uget i (Nat.lt_of_lt_of_le (by simpa [Array.usize, USize.lt_iff_toNat_lt] using h) (Nat.mod_le _ _))
  else 0

/-- Extend with zero cells up to index `i`, then store `v` at `i`. -/
def growAndStore (db : Array Cell) (i : Nat) (v : Cell) : Array Cell :=
  (db ++ Array.replicate (i - db.size) 0).push v

/-- `DB[p] = v`. -/
@[inline] def st (db : Array Cell) (p v : Cell) : Array Cell :=
  let i := p.toUInt32.toUSize
  if h : i < db.usize then
    db.uset i v (Nat.lt_of_lt_of_le (by simpa [Array.usize, USize.lt_iff_toNat_lt] using h) (Nat.mod_le _ _))
  else if p < 0 then db else growAndStore db p.toUInt32.toNat v

/-- The offsets of the arrays inside `db` (C:197–205), fixed after `initCDCL`. -/
structure Lay where
  nVars : Cell
  next : Cell
  prev : Cell
  buffer : Cell
  reason : Cell
  falseStack : Cell
  fls : Cell
  first : Cell

/-- The layout for `n` variables (`model` is at 0). -/
def Lay.mk' (n : Cell) : Lay :=
  { nVars := n, next := n + 1, prev := 2 * n + 2, buffer := 3 * n + 3, reason := 4 * n + 3,
    falseStack := 5 * n + 4, fls := 7 * n + 5, first := 9 * n + 6 }

/-- The mutable part of C's `struct solver` (`res` is never read; `nClauses` only by
`parse`). -/
structure St where
  db : Array Cell
  memUsed : Cell
  memFixed : Cell
  maxLemmas : Cell
  nLemmas : Cell
  nConflicts : Cell
  forced : Cell
  processed : Cell
  assigned : Cell
  head : Cell
  fast : Cell
  slow : Cell

/-- Detach `db` from the state, so that writes to it happen in place. -/
@[inline] def St.take (s : St) : Array Cell × St := (s.db, { s with db := #[] })

-- C:36, C:38–40
/-- `restart`: unassign everything above `forced`. Returns `db` and `assigned`. -/
def restartLoop (L : Lay) (db : Array Cell) (assigned forced : Cell) : Array Cell × Cell :=
  if assigned > forced then
    let a := assigned - 1
    restartLoop L (st db (L.fls + ld db a) 0) a forced
  else (db, assigned)
partial_fixpoint

def restart (L : Lay) (s : St) : St :=
  let (db, s) := s.take
  let (db, assigned) := restartLoop L db s.assigned s.forced
  { s with db, assigned, processed := s.forced }

-- C:42–47
/-- `assign`: make the first literal of the clause at `reason` true. The caller
increments `assigned`. -/
@[inline] def assign (L : Lay) (db : Array Cell) (assigned reason : Cell) (forced : Bool) :
    Array Cell :=
  let lit := ld db reason
  let db := st db (L.fls - lit) (if forced then IMPLIED else 1)
  let db := st db assigned (-lit)
  let db := st db (L.reason + absC lit) (1 + reason)
  st db (absC lit) (if lit > 0 then 1 else 0)

-- C:49–50
@[inline] def addWatch (L : Lay) (db : Array Cell) (lit mem : Cell) : Array Cell :=
  let h := L.first + lit
  st (st db mem (ld db h)) h mem

-- C:59–66
/-- Copy `size` cells from `src` to `dst` (ascending; `dst ≤ src` when they overlap). -/
def copyLoop (db : Array Cell) (dst src i size : Cell) : Array Cell :=
  if i < size then copyLoop (st db (dst + i) (ld db (src + i))) dst src (i + 1) size else db
partial_fixpoint

/-- `addClause` of the `size` literals at `src`: returns `db`, the new `mem_used`, and
the clause pointer, or `NONE` (-1) when memory runs out (C:53–54). -/
@[inline] def addClause (L : Lay) (db : Array Cell) (memUsed src size : Cell) :
    Array Cell × Cell × Cell :=
  if memUsed + size + 3 > memMax then (db, memUsed, NONE)
  else
    let db := if size > 1 then
      let db := addWatch L db (ld db src) memUsed
      addWatch L db (ld db (src + 1)) (memUsed + 1)
    else db
    let clause := memUsed + 2
    let db := copyLoop db clause src 0 size
    (st db (clause + size) 0, memUsed + size + 3, clause)

-- C:68–83
/-- `while (nLemmas > maxLemmas) maxLemmas += 300` -/
def raiseLoop (nLemmas maxLemmas : Cell) : Cell :=
  if nLemmas > maxLemmas then raiseLoop nLemmas (maxLemmas + 300) else maxLemmas
partial_fixpoint

/-- Unlink the lemma watches from the list starting at cell `watch`. -/
def unlinkLoop (db : Array Cell) (memFixed watch : Cell) : Array Cell :=
  let w := ld db watch
  if w == END then db
  else if w < memFixed then unlinkLoop db memFixed w
  else unlinkLoop (st db watch (ld db w)) memFixed watch
partial_fixpoint

/-- The unlink loop over all literals `i ≤ nVars` (`i ≠ 0`). -/
def unlinkAll (L : Lay) (db : Array Cell) (memFixed i : Cell) : Array Cell :=
  if i ≤ L.nVars then
    unlinkAll L (if i == 0 then db else unlinkLoop db memFixed (L.first + i)) memFixed (i + 1)
  else db
partial_fixpoint

/-- Count the literals from `i` on that agree with the model; returns the count and the
position of the terminating 0. -/
def countLoop (db : Array Cell) (i count : Cell) : Cell × Cell :=
  let lit := ld db i
  if lit == 0 then (count, i)
  else countLoop db (i + 1) (if (if lit > 0 then (1 : Cell) else 0) == ld db (absC lit) then count + 1 else count)
partial_fixpoint

/-- Re-add the lemmas with fewer than `k` literals agreeing with the model. -/
def keepLoop (L : Lay) (db : Array Cell) (memUsed nLemmas oldUsed k i : Cell) :
    Array Cell × Cell × Cell :=
  if i < oldUsed then
    let (count, e) := countLoop db i 0
    if count < k then
      let (db, memUsed, _) := addClause L db memUsed i (e - i)
      keepLoop L db memUsed (nLemmas + 1) oldUsed k (e + 3)
    else keepLoop L db memUsed nLemmas oldUsed k (e + 3)
  else (db, memUsed, nLemmas)
partial_fixpoint

def reduceDB (L : Lay) (s : St) (k : Cell) : St :=
  let (db, s) := s.take
  let maxLemmas := raiseLoop s.nLemmas s.maxLemmas
  let db := unlinkAll L db s.memFixed (-L.nVars)
  let (db, memUsed, nLemmas) := keepLoop L db s.memFixed 0 s.memUsed k (s.memFixed + 2)
  { s with db, memUsed, nLemmas, maxLemmas }

-- C:85–91
/-- `bump` the literals of the clause from cell `c` on (C:104, C:112). Returns `db` and
`head`. -/
def bumpLoop (L : Lay) (db : Array Cell) (head c : Cell) : Array Cell × Cell :=
  let lit := ld db c
  if lit == 0 then (db, head)
  else if ld db (L.fls + lit) == IMPLIED then bumpLoop L db head (c + 1)
  else
    let db := st db (L.fls + lit) MARK
    let v := absC lit
    if v == head then bumpLoop L db head (c + 1)
    else
      let db := st db (L.prev + ld db (L.next + v)) (ld db (L.prev + v))
      let db := st db (L.next + ld db (L.prev + v)) (ld db (L.next + v))
      let db := st db (L.next + head) v
      let db := st db (L.prev + v) head
      bumpLoop L db v (c + 1)
partial_fixpoint

-- C:93–100
mutual
/-- `implied`: whether `lit` is implied by MARKed literals. The answer is left in the
flag of `lit` (`IMPLIED` means implied); `none` only if C's recursion never returns. -/
def implied (L : Lay) (db : Array Cell) (lit : Cell) : Option (Array Cell) :=
  if ld db (L.fls + lit) > MARK then some db
  else if ld db (L.reason + absC lit) == 0 then some db
  else impliedLoop L db lit (ld db (L.reason + absC lit) - 1)
partial_fixpoint

/-- C:97–100: `while (*(++p))`. -/
def impliedLoop (L : Lay) (db : Array Cell) (lit p : Cell) : Option (Array Cell) := do
  let p := p + 1
  let x := ld db p
  if x == 0 then return st db (L.fls + lit) IMPLIED
  if ld db (L.fls + x) != MARK then
    let db ← implied L db x
    if ld db (L.fls + x) != IMPLIED then return st db (L.fls + lit) 5
    impliedLoop L db lit p
  else impliedLoop L db lit p
partial_fixpoint
end

-- C:102–130
/-- C:108–109: from `check`, whether a decision comes before the next MARK (`goto build`). -/
def checkLoop (L : Lay) (db : Array Cell) (check : Cell) : Bool :=
  let c := check - 1
  let y := ld db c
  if ld db (L.fls + y) == MARK then false
  else if ld db (L.reason + absC y) == 0 then true
  else checkLoop L db c
partial_fixpoint

/-- C:105–113: resolve down to the first UIP. Returns `db`, `head` and `assigned`. -/
def resolveLoop (L : Lay) (db : Array Cell) (head assigned : Cell) : Array Cell × Cell × Cell :=
  let a := assigned - 1
  let x := ld db a
  let r := ld db (L.reason + absC x)
  if r == 0 then (db, head, a)
  else if ld db (L.fls + x) == MARK then
    if checkLoop L db a then (db, head, a)
    else
      let (db, head) := bumpLoop L db head r
      resolveLoop L (st db (L.fls + x) 0) head a
  else resolveLoop L (st db (L.fls + x) 0) head a
partial_fixpoint

/-- C:116–122: collect the lemma into `buffer` and find the backjump point. Returns
`db`, `size`, `lbd` and `processed`. -/
def buildLoop (L : Lay) (db : Array Cell) (forced p size lbd : Cell) (flag : Bool)
    (processed : Cell) : Array Cell × Cell × Cell × Cell :=
  if p ≥ forced then
    let x := ld db p
    if ld db (L.fls + x) == MARK then
      let db := (implied L db x).getD #[]
      if ld db (L.fls + x) != IMPLIED then
        let db := st db (L.buffer + size) x
        if ld db (L.reason + absC x) == 0 then
          buildLoop L (st db (L.fls + x) 1) forced (p - 1) (size + 1) (lbd + 1) false
            (if size + 1 == 1 then p else processed)
        else buildLoop L (st db (L.fls + x) 1) forced (p - 1) (size + 1) lbd true processed
      else if ld db (L.reason + absC x) == 0 then
        buildLoop L (st db (L.fls + x) 1) forced (p - 1) size (if flag then lbd + 1 else lbd) false
          (if size == 1 then p else processed)
      else buildLoop L (st db (L.fls + x) 1) forced (p - 1) size lbd flag processed
    else if ld db (L.reason + absC x) == 0 then
      buildLoop L (st db (L.fls + x) 1) forced (p - 1) size (if flag then lbd + 1 else lbd) false
        (if size == 1 then p else processed)
    else buildLoop L (st db (L.fls + x) 1) forced (p - 1) size lbd flag processed
  else (db, size, lbd, processed)
partial_fixpoint

/-- C:127–128: unassign from `assigned` down to `processed` (inclusive). -/
def unassignLoop (L : Lay) (db : Array Cell) (assigned processed : Cell) : Array Cell :=
  let db := st db (L.fls + ld db assigned) 0
  if assigned > processed then unassignLoop L db (assigned - 1) processed else db
partial_fixpoint

/-- `analyze` (C:102–130). Returns the state and the lemma pointer (`NONE` = out of memory). -/
def analyze (L : Lay) (s : St) (clause : Cell) : St × Cell :=
  let (db, s) := s.take
  let (db, head) := bumpLoop L db s.head clause
  let (db, head, assigned) := resolveLoop L db head s.assigned
  let (db, size, lbd, processed) := buildLoop L db s.forced assigned 0 0 false assigned
  let fast := s.fast - (s.fast >>> 5) + (lbd <<< 15)
  let slow := s.slow - (s.slow >>> 15) + (lbd <<< 5)
  let db := unassignLoop L db assigned processed
  let db := st db (L.buffer + size) 0
  let (db, memUsed, lemma) := addClause L db s.memUsed L.buffer size
  ({ s with
      db, head, assigned := processed, processed, fast, slow, memUsed,
      nLemmas := s.nLemmas + 1, nConflicts := s.nConflicts + 1 }, lemma)

-- C:132–158
/-- C:143: the first `i` from which `clause[i]` is 0 or not false. -/
def scanLoop (L : Lay) (db : Array Cell) (clause i : Cell) : Cell :=
  let x := ld db (clause + i)
  if x == 0 then i
  else if ld db (L.fls + x) == 0 then i
  else scanLoop L db clause (i + 1)
partial_fixpoint

/-- `propagate`'s two loops as one: processing the watch list of `lit` at the cell
`watch` (`watch < 0`: no list, take the next literal); `s` holds the rest of the
state (with an empty `db`). Returns the state and `SAT`, `UNSAT` or `OOM`. -/
def propLoop (L : Lay) (s : St) (db : Array Cell) (assigned processed : Cell) (forced : Bool)
    (lit watch : Cell) : St × UInt8 :=
  let w := if watch < 0 then END else ld db watch
  if w == END then
    if processed < assigned then
      let lit := ld db processed
      propLoop L s db assigned (processed + 1) forced lit (L.first + lit)
    else
      ({ s with db, assigned, processed, forced := if forced then processed else s.forced }, SAT)
  else
    let clause := if ld db (w - 1) == 0 then w + 2 else w + 1
    let db := if ld db clause == lit then st db clause (ld db (clause + 1)) else db
    let i := scanLoop L db clause 2
    let x := ld db (clause + i)
    if x != 0 then
      let db := st db (clause + 1) x
      let db := st db (clause + i) lit
      let db := st db watch (ld db w)
      let db := addWatch L db x w
      propLoop L s db assigned processed forced lit watch
    else
      let db := st db (clause + 1) lit
      let other := ld db clause
      if ld db (L.fls - other) != 0 then propLoop L s db assigned processed forced lit w
      else if ld db (L.fls + other) == 0 then
        propLoop L s (assign L db assigned clause forced) (assigned + 1) processed forced lit w
      else if forced then ({ s with db, assigned, processed }, UNSAT)
      else
        let (s, lemma) := analyze L { s with db, assigned, processed } clause
        if lemma < 0 then (s, OOM)
        else
          let forced := ld s.db (lemma + 1) == 0
          let (db, s) := s.take
          let db := assign L db s.assigned lemma forced
          propLoop L s db (s.assigned + 1) s.processed forced 0 NONE
partial_fixpoint

/-- `propagate` (C:132–158). -/
def propagate (L : Lay) (s : St) : St × UInt8 :=
  let forced := ld s.db (L.reason + absC (ld s.db s.processed)) != 0
  let (db, s) := s.take
  propLoop L s db s.assigned s.processed forced 0 NONE

-- C:160–179
/-- C:173–174: the first unassigned variable along `prev` from `d`. -/
def decideLoop (L : Lay) (db : Array Cell) (d : Cell) : Cell :=
  if ld db (L.fls + d) != 0 || ld db (L.fls - d) != 0 then decideLoop L db (ld db (L.prev + d))
  else d
partial_fixpoint

/-- `solve`'s main loop (C:162–179): returns the state and `SAT`, `UNSAT` or `OOM`. -/
def run (L : Lay) (s : St) (decision : Cell) : St × UInt8 :=
  let old := s.nLemmas
  let (s, r) := propagate L s
  if r != SAT then (s, r)
  else
    let (s, decision) :=
      if s.nLemmas > old then
        if s.fast > (s.slow / 100) * 125 then
          let s := restart L { s with fast := (s.slow / 100) * 125 }
          (if s.nLemmas > s.maxLemmas then reduceDB L s 6 else s, s.head)
        else (s, s.head)
      else (s, decision)
    let d := decideLoop L s.db decision
    if d == 0 then (s, SAT)
    else
      let d := if ld s.db d != 0 then d else -d
      let (db, s) := s.take
      let db := st db (L.fls - d) 1
      let db := st db s.assigned (-d)
      let db := st db (L.reason + absC d) 0
      run L { s with db, assigned := s.assigned + 1 } (absC d)
partial_fixpoint

def solve (L : Lay) (s : St) : St × UInt8 := run L s s.head

-- C:181–210
/-- C:206–209 for the variables `i … n`. -/
def initLoop (L : Lay) (db : Array Cell) (i : Cell) : Array Cell :=
  if i ≤ L.nVars then
    let db := st db (L.prev + i) (i - 1)
    let db := st db (L.next + (i - 1)) i
    let db := st db (L.fls + i) 0
    let db := st db (L.fls - i) 0
    let db := st db i 0
    let db := st db (L.first - i) END
    let db := st db (L.first + i) END
    initLoop L db (i + 1)
  else db
partial_fixpoint

/-- `initCDCL` (C:181–210); `none` when the arrays do not fit in memory. -/
def initCDCL (n : Cell) : Option (Lay × St) :=
  let n := if n < 1 then 1 else n
  if n > (memMax - 7) / 10 then none
  else
    let L := Lay.mk' n
    let used := 10 * n + 8
    let db := initLoop L (Array.replicate used.toUInt32.toNat 0) 1
    some (L, {
      db, memUsed := used, memFixed := 0, maxLemmas := 2000, nLemmas := 0, nConflicts := 0,
      forced := L.falseStack, processed := L.falseStack, assigned := L.falseStack,
      head := n, fast := 16777216, slow := 16777216 })

-- C:216–243
/-- The clause loop of `parse` over the literal tokens (`0` ends a clause). -/
def parseLoop (L : Lay) (s : St) (tokens : Array Int) (next : Nat) (nZeros : Int) (size : Cell) : St × UInt8 :=
  if nZeros > 0 then
    match tokens[next]? with
    | none => (s, PARSE_ERROR)
    | some t =>
      let lit : Cell := Int32.ofInt t
      let (db, s) := s.take
      if lit == 0 then
        let (db, memUsed, clause) := addClause L db s.memUsed L.buffer size
        if clause < 0 then ({ s with db, memUsed }, OOM)
        else
          let s := { s with db, memUsed, memFixed := memUsed }
          if size == 0 || (size == 1 && ld db (L.fls + ld db clause) != 0) then (s, UNSAT)
          else
            let s := if size == 1 && ld db (L.fls - ld db clause) == 0 then
              { s with db := assign L db s.assigned clause true, assigned := s.assigned + 1 }
            else s
            parseLoop L s tokens (next + 1) (nZeros - 1) 0
      else parseLoop L { s with db := st db (L.buffer + size) lit } tokens (next + 1) nZeros (size + 1)
  else (s, SAT)
partial_fixpoint

/-- `parse` from the DIMACS header and literal tokens. `none` = out of memory in
`initCDCL`. The arrays of more than `(memMax - 7) / 10` variables do not fit (C:186–205
then runs out of memory); checking this before the conversion to `Int32` keeps `nVars`
and every literal of a valid input exact. `nClauses` stays an `Int`. -/
def parse (nVars nClauses : Int) (tokens : Array Int) : Option (Lay × St × UInt8) :=
  if nVars > 107374181 then none
  else match initCDCL (Int32.ofInt nVars) with
  | none => none
  | some (L, s) =>
    let (s, r) := parseLoop L s tokens 0 nClauses 0
    some (L, s, r)

end MicrosatLean.Fast
