import MicrosatLean.Formula

namespace MicrosatLean

namespace Dimacs

/-- A byte offset with a human-readable location. `lineStart` permits comments
after leading whitespace, but never in the middle of a clause line. -/
private structure Cursor where
  offset : Nat := 0
  line : Nat := 1
  column : Nat := 1
  lineStart : Bool := true

private structure Token where
  start : Nat
  stop : Nat
  line : Nat
  column : Nat

@[inline] private def isWhitespace (byte : UInt8) : Bool :=
  byte == 32 || (byte >= 9 && byte <= 13)

@[inline] private def advance (cursor : Cursor) (byte : UInt8) : Cursor :=
  if byte == 10 then
    { offset := cursor.offset + 1, line := cursor.line + 1, column := 1 }
  else
    { cursor with offset := cursor.offset + 1, column := cursor.column + 1 }

/-- Scan one token without allocating token strings. Both loops are bounded by
the remaining input bytes, so the scanner is total independently of the input. -/
private def nextToken (input : ByteArray) (initial : Cursor) : Option (Token × Cursor) := Id.run do
  let mut cursor := initial
  let mut comment := false
  for _ in [:input.size - initial.offset] do
    let byte := input[cursor.offset]!
    if comment then
      cursor := advance cursor byte
      if byte == 10 then comment := false
    else if isWhitespace byte then
      cursor := advance cursor byte
    else if cursor.lineStart && byte == 99 then
      comment := true
      cursor := advance cursor byte
    else
      break
  if cursor.offset >= input.size then return none
  let start := cursor
  cursor := { cursor with lineStart := false }
  for _ in [:input.size - start.offset] do
    let byte := input[cursor.offset]!
    if isWhitespace byte then break
    cursor := advance cursor byte
  let token : Token := {
    start := start.offset
    stop := cursor.offset
    line := start.line
    column := start.column }
  return some (token, cursor)

private def tokenText (input : ByteArray) (token : Token) : String :=
  (String.fromUTF8? (input.extract token.start token.stop)).getD "<non-UTF-8 token>"

private def atToken (token : Token) (message : String) : String :=
  s!"line {token.line}, column {token.column}: {message}"

private def requireToken (input : ByteArray) (cursor : Cursor) (expected : String) :
    Except String (Token × Cursor) :=
  match nextToken input cursor with
  | some result => .ok result
  | none => .error s!"unexpected end of input; expected {expected}"

/-- Read a signed decimal integer directly from its byte span. A separate sign
bit retains negative zero so that the parser can reject it explicitly. -/
private def decimal (input : ByteArray) (token : Token) : Except String (Bool × Nat) := do
  let negative := input[token.start]! == 45
  let firstDigit := token.start + if negative then 1 else 0
  if firstDigit == token.stop then
    throw (atToken token "expected a decimal integer")
  let mut value := 0
  for offset in [firstDigit:token.stop] do
    let byte := input[offset]!
    if byte < 48 || byte > 57 then
      throw (atToken token s!"invalid integer '{tokenText input token}'")
    value := value * 10 + (byte.toNat - 48)
  return (negative, value)

private def natural (input : ByteArray) (token : Token) : Except String Nat := do
  let (negative, value) ← decimal input token
  if negative then
    throw (atToken token "header counts must be nonnegative decimal integers")
  return value

private def headerToken (input : ByteArray) (cursor : Cursor) (line : Nat)
    (expected : String) : Except String (Token × Cursor) := do
  let result ← requireToken input cursor expected
  if result.1.line != line then
    throw (atToken result.1 "the complete 'p cnf' header must be on one line")
  return result

end Dimacs

/-- Parse standard DIMACS CNF. Clauses remain in input order, including empty
clauses, repeated literals, and tautologies. The solver normalizes its own copy.
Comments are full lines beginning with `c` after optional whitespace. -/
def parseDimacsBytes (input : ByteArray) : Except String Formula := do
  let (p, cursor) ← Dimacs.requireToken input {} "a 'p cnf' header"
  if Dimacs.tokenText input p != "p" then
    throw (Dimacs.atToken p "expected a 'p cnf' header before clauses")
  let (cnf, cursor) ← Dimacs.headerToken input cursor p.line "'cnf'"
  if Dimacs.tokenText input cnf != "cnf" then
    throw (Dimacs.atToken cnf "expected 'cnf' after 'p'")
  let (variables, cursor) ← Dimacs.headerToken input cursor p.line "a variable count"
  let numVars ← Dimacs.natural input variables
  let (count, cursor) ← Dimacs.headerToken input cursor p.line "a clause count"
  let numClauses ← Dimacs.natural input count
  let mut cursor := cursor
  let mut clauses := #[]
  let mut clause := #[]
  -- Each iteration consumes a nonempty token, or returns at EOF. The extra
  -- iteration permits the final EOF check even when the last byte is a token.
  for _ in [:input.size + 1] do
    let some (token, next) := Dimacs.nextToken input cursor
      | if !clause.isEmpty then
          throw "unexpected end of input; the final clause is missing its terminating zero"
        else if clauses.size != numClauses then
          throw s!"header declares {numClauses} clauses, but found {clauses.size}"
        else
          return { numVars, clauses }
    cursor := next
    if token.line == p.line then
      throw (Dimacs.atToken token "unexpected token after the 'p cnf' header")
    let (negative, var) ← Dimacs.decimal input token
    if negative && var == 0 then
      throw (Dimacs.atToken token "negative zero is not a clause terminator")
    if var == 0 then
      if clauses.size >= numClauses then
        throw (Dimacs.atToken token s!"more than the declared {numClauses} clauses")
      clauses := clauses.push clause
      clause := #[]
    else
      if var > numVars then
        throw (Dimacs.atToken token s!"variable {var} exceeds the declared bound {numVars}")
      if clauses.size >= numClauses then
        throw (Dimacs.atToken token s!"literal after the declared {numClauses} clauses")
      clause := clause.push (2 * var + if negative then 1 else 0)
  throw "DIMACS parser exhausted its input bound"

/-- String convenience wrapper; file parsing can use `parseDimacsBytes` directly. -/
def parseDimacs (input : String) : Except String Formula :=
  parseDimacsBytes input.toUTF8

/-- File I/O is separate from the total parser and preserves parse diagnostics. -/
def readDimacsFile (path : System.FilePath) : IO (Except String Formula) := do
  try
    return parseDimacsBytes (← IO.FS.readBinFile path)
  catch error =>
    return .error s!"cannot read '{path}': {error}"

end MicrosatLean
