import MicrosatLean.Dimacs
import MicrosatLean.Solver

open MicrosatLean

private structure Options where
  path : Option System.FilePath := none
  printModel : Bool := true
  printStats : Bool := false
  help : Bool := false

private def usage : String :=
  "Usage: microsat-lean [--no-model] [--stats] FILE.cnf\n" ++
  "Solve a standard DIMACS CNF file using Microsat's CDCL algorithm.\n" ++
  "  --no-model  Print only the SAT/UNSAT status\n" ++
  "  --stats     Print solver statistics as DIMACS comments\n" ++
  "  --help      Show this help\n" ++
  "Exit codes: 10 = SAT, 20 = UNSAT, 1 = input or solver error."

private def parseOptions (arguments : List String) : Except String Options := do
  let mut options : Options := {}
  let mut literal := false
  for argument in arguments do
    if !literal && argument == "--" then
      literal := true
    else if !literal && (argument == "--help" || argument == "-h") then
      options := { options with help := true }
    else if !literal && argument == "--no-model" then
      options := { options with printModel := false }
    else if !literal && argument == "--stats" then
      options := { options with printStats := true }
    else if !literal && argument.startsWith "-" then
      throw s!"unknown option '{argument}'"
    else
      if options.path.isSome then throw "expected exactly one CNF input file"
      options := { options with path := some argument }
  if !options.help && options.path.isNone then throw "missing CNF input file"
  return options

private def reportError (message : String) : IO UInt32 := do
  (← IO.getStderr).putStrLn s!"microsat-lean: {message}"
  return 1

/-- Keep model lines short while retaining the conventional final zero. Index
zero is reserved; the model contains one Boolean for each DIMACS variable. -/
private def printModel (model : Array Bool) (numVars : Nat) : IO Unit := do
  let mut line := "v"
  let mut columns := 0
  for var in [1:numVars + 1] do
    let value := if model[var]! then Int.ofNat var else -(Int.ofNat var)
    line := line ++ s!" {value}"
    columns := columns + 1
    if columns == 16 then
      IO.println line
      line := "v"
      columns := 0
  IO.println s!"{line} 0"

private def printStatistics (stats : CDCL.Stats) : IO Unit := do
  IO.println s!"c conflicts={stats.conflicts} decisions={stats.decisions} propagations={stats.propagations} restarts={stats.restarts} reductions={stats.reductions} removed_learned={stats.removedLearned}"

def main (arguments : List String) : IO UInt32 := do
  match parseOptions arguments with
  | .error message => reportError s!"{message}\n{usage}"
  | .ok options =>
    if options.help then
      IO.println usage
      return 0
    let some path := options.path | reportError "missing CNF input file"
    try
      match ← readDimacsFile path with
      | .error message => reportError message
      | .ok formula =>
        match ← CDCL.solve formula with
        | .error message => reportError message
        | .ok (.sat model stats) =>
          if model.size <= formula.numVars || !formula.satisfiedBy model then
            return ← reportError "internal error: the returned model does not satisfy the input"
          IO.println "s SATISFIABLE"
          if options.printModel then printModel model formula.numVars
          if options.printStats then printStatistics stats
          return 10
        | .ok (.unsat stats) =>
          IO.println "s UNSATISFIABLE"
          if options.printStats then printStatistics stats
          return 20
    catch error =>
      reportError s!"{error}"
