import MicrosatLean.Fast.Solver

/-!
`main` of `upstream/microsat.c` (C:245–251) for the fast port, with the extra output of
`tools/microsat_ref.c` for differential testing: a `v` model line and a hash of
`DB[0..mem_used)` after `parse` and at the end. Running out of memory prints C's
`c out of memory` (C:54).
-/

open MicrosatLean.Fast

/-- FNV-1a over `DB[0..mem_used)` as 32-bit cells, as in `tools/microsat_ref.c`. -/
def dbHash (s : St) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for i in [0:s.memUsed.toUInt32.toNat] do
    h := h ^^^ (s.db.getD i 0).toUInt32.toUInt64
    h := h * 1099511628211
  return h

def report (s : St) (tag : String) : IO Unit :=
  IO.println s!"c db {tag} mem_used: {s.memUsed} hash: {dbHash s}"

def printModel (L : Lay) (s : St) : IO Unit := do
  let mut line := "v"
  for i in [1:L.nVars.toUInt32.toNat + 1] do
    let v : Cell := Int32.ofNat i
    line := line ++ s!" {if ld s.db v != 0 then v else -v}"
  IO.println s!"{line} 0"

/-- A byte-level DIMACS reader (C:217–233 for well-formed files): skips comment lines
(`c …`), reads the header `p cnf n m`, then every integer that follows. Returns `n`, `m`
and the integer tokens; `none` if there is no header. Outside the proved model, like
C's `fscanf` loop (`ASSUMPTIONS.md`, E4). -/
partial def readDimacsFast (bytes : ByteArray) : Option (Int × Int × Array Int) :=
  let size := bytes.size
  let isSpace (b : UInt8) : Bool := b == 32 || b == 10 || b == 13 || b == 9
  let rec skipLine (i : Nat) : Nat :=
    if i < size then (if bytes.get! i == 10 then i + 1 else skipLine (i + 1)) else i
  let rec number (i : Nat) (acc : Nat) : Nat × Nat :=
    if i < size then
      let b := bytes.get! i
      if 48 ≤ b && b ≤ 57 then number (i + 1) (acc * 10 + (b - 48).toNat) else (acc, i)
    else (acc, i)
  let rec signed (i : Nat) : Int × Nat :=
    if i < size && bytes.get! i == 45 then
      let (v, j) := number (i + 1) 0
      (-(v : Int), j)
    else
      let (v, j) := number i 0
      ((v : Int), j)
  let rec skipSpace (i : Nat) : Nat :=
    if i < size && isSpace (bytes.get! i) then skipSpace (i + 1) else i
  let rec skipWord (i : Nat) : Nat :=
    if i < size && !isSpace (bytes.get! i) then skipWord (i + 1) else i
  let rec body (i : Nat) (acc : Array Int) : Array Int :=
    let i := skipSpace i
    if i < size then
      if bytes.get! i == 99 then body (skipLine i) acc
      else
        let (v, j) := signed i
        if j == i then body (i + 1) acc else body j (acc.push v)
    else acc
  let rec header (i : Nat) : Option (Int × Int × Array Int) :=
    let i := skipSpace i
    if i < size then
      if bytes.get! i == 112 then
        let i := skipSpace (skipWord (skipSpace (i + 1)))
        let (n, i) := signed i
        let (m, i) := signed (skipSpace i)
        some (n, m, body i #[])
      else header (skipLine i)
    else none
  header 0

def main (args : List String) : IO UInt32 := do
  let some path := args.head?
    | IO.println "no input file provided"; return 0
  match readDimacsFast (← IO.FS.readBinFile path) with
  | none =>
    (← IO.getStderr).putStrLn s!"microsat-fast: no DIMACS header in {path}"
    return 1
  | some (nVars, nClauses, tokens) =>
    match parse nVars nClauses tokens with
    | none => IO.println "c out of memory"; return 0
    | some (L, s, r) =>
      if r == OOM then IO.println "c out of memory"; return 0
      if r == PARSE_ERROR then IO.println "s parse error: header incorrect"; return 0
      report s "parse"
      let (s, r) := if r == UNSAT then (s, r) else solve L s
      if r == OOM then IO.println "c out of memory"; return 0
      IO.println (if r == UNSAT then "s UNSATISFIABLE" else "s SATISFIABLE")
      if r == SAT then printModel L s
      IO.println s!"c statistics of {path}: mem: {s.memUsed} conflicts: {s.nConflicts} max_lemmas: {s.maxLemmas}"
      report s "final"
      return 0
