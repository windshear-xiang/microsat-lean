import MicrosatLean.Dimacs
import MicrosatLean.Faithful

/-!
`main` of `upstream/microsat.c` (C:245–251) for the faithful port, plus the
extra output `tools/microsat_ref.c` prints for differential testing: a `v`
model line and a hash of `DB[0..mem_used)` after `parse` and at the end.
`--dump` also prints every cell of `DB[0..mem_used)`.

Character-level DIMACS reading is deferred: the file is read by the existing
`readDimacsFile`, and its clauses are passed to `parse` as a token stream.
-/

open MicrosatLean MicrosatLean.Faithful

/-- FNV-1a over `DB[0..mem_used)` as 32-bit cells, as in `tools/microsat_ref.c`. -/
def dbHash (S : solver) : UInt64 := Id.run do
  let mut h : UInt64 := 14695981039346656037
  for i in [0:S.mem_used.toNat] do
    h := h ^^^ UInt64.ofNat ((S.ld i % 4294967296).toNat)
    h := h * 1099511628211
  return h

def report (S : solver) (tag : String) (dump : Bool) : IO Unit := do
  IO.println s!"c db {tag} mem_used: {S.mem_used} hash: {dbHash S}"
  if dump then
    for i in [0:S.mem_used.toNat] do
      IO.println s!"d {tag} {i} {S.ld i}"

def printModel (S : solver) : IO Unit := do
  let mut line := "v"
  for i in (1 : CInt)...=S.nVars do
    line := line ++ s!" {if S.ld (S.model + i) != 0 then i else -i}"
  IO.println s!"{line} 0"

/-- The DIMACS literal tokens after the header, each clause ended by `0`. -/
def tokens (formula : Formula) : Array CInt :=
  formula.clauses.foldl (init := #[]) fun acc clause =>
    (clause.foldl (init := acc) fun acc lit => acc.push lit.toInt).push 0

def main (args : List String) : IO UInt32 := do
  let dump := args.contains "--dump"
  let some path := args.find? (· != "--dump")
    | IO.println "no input file provided"; return 0
  match ← readDimacsFile path with
  | .error message =>
    (← IO.getStderr).putStrLn s!"microsat-faithful: {message}"
    return 1
  | .ok formula =>
    let (S, result) := parse formula.numVars formula.clauses.size (tokens formula)
    report S "parse" dump
    let (S, result) := if result == UNSAT then (S, result) else solve S
    IO.println (if result == UNSAT then "s UNSATISFIABLE" else "s SATISFIABLE")
    if result == SAT then printModel S
    IO.println s!"c statistics of {path}: mem: {S.mem_used} conflicts: {S.nConflicts} max_lemmas: {S.maxLemmas}"
    report S "final" dump
    return 0
