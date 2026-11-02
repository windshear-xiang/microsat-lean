import MicrosatLean.Formula

/-!
DIMACS CNF 解析：按字节扫描并提供行列诊断。解析器使用显式有限循环，与求解器及其验证框架分开。
-/

namespace MicrosatLean

namespace Dimacs

/-- 扫描位置：记录字节偏移以及便于报错的行列号。
`lineStart` 允许注释前有空白，但不允许在子句行中间开始注释。 -/
private structure Cursor where
  /-- 下一个待扫描字节的偏移量，从 0 开始。 -/
  offset : Nat := 0
  /-- 当前行号，从 1 开始。 -/
  line : Nat := 1
  /-- 当前列号，从 1 开始。 -/
  column : Nat := 1
  /-- 当前位置是否仍位于行首空白区，用于识别整行注释。 -/
  lineStart : Bool := true

/-- 一个 token 在输入字节数组中的半开区间，以及起始行列号。 -/
private structure Token where
  /-- token 的首字节偏移量。 -/
  start : Nat
  /-- token 结束后的首个字节偏移量。 -/
  stop : Nat
  /-- token 起点的行号。 -/
  line : Nat
  /-- token 起点的列号。 -/
  column : Nat

/-- 识别空格和 ASCII 的制表、换行等空白字节。 -/
@[inline] private def isWhitespace (byte : UInt8) : Bool :=
  byte == 32 || (byte >= 9 && byte <= 13)

/-- 消费一个字节并更新位置；换行时重置列号和行首状态。 -/
@[inline] private def advance (cursor : Cursor) (byte : UInt8) : Cursor :=
  if byte == 10 then
    { offset := cursor.offset + 1, line := cursor.line + 1, column := 1 }
  else
    { cursor with offset := cursor.offset + 1, column := cursor.column + 1 }

/-- 扫描下一个 token，避免分配临时字符串。
两个循环都由剩余字节数限制，因此扫描器对任意输入都会终止。 -/
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

/-- 提取 token 对应的 UTF-8 文本；无效 UTF-8 使用占位文本显示。 -/
private def tokenText (input : ByteArray) (token : Token) : String :=
  (String.fromUTF8? (input.extract token.start token.stop)).getD "<non-UTF-8 token>"

/-- 为诊断信息加上 token 的起始行列号。 -/
private def atToken (token : Token) (message : String) : String :=
  s!"line {token.line}, column {token.column}: {message}"

/-- 读取必需的下一个 token；若输入结束，则报告预期内容。 -/
private def requireToken (input : ByteArray) (cursor : Cursor) (expected : String) :
    Except String (Token × Cursor) :=
  match nextToken input cursor with
  | some result => .ok result
  | none => .error s!"unexpected end of input; expected {expected}"

/-- 直接从 token 的字节区间读取有符号十进制整数。
单独保留负号，使 parser 能显式拒绝负零。 -/
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

/-- 读取 header 中的非负十进制计数，并拒绝带负号的输入。 -/
private def natural (input : ByteArray) (token : Token) : Except String Nat := do
  let (negative, value) ← decimal input token
  if negative then
    throw (atToken token "header counts must be nonnegative decimal integers")
  return value

/-- 读取 header 的下一个 token，并要求它与 `p` 位于同一行。 -/
private def headerToken (input : ByteArray) (cursor : Cursor) (line : Nat)
    (expected : String) : Except String (Token × Cursor) := do
  let result ← requireToken input cursor expected
  if result.1.line != line then
    throw (atToken result.1 "the complete 'p cnf' header must be on one line")
  return result

end Dimacs

/-- 解析标准 DIMACS CNF，按输入顺序保留空子句、重复文字和重言式。
求解器会规范化自己的子句副本。注释必须是以 `c` 开头的整行，前面可以有空白。 -/
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
  -- 每次循环消费一个非空 token，或在 EOF 处返回。多预留一次循环，
  -- 使最后一个字节属于 token 时，仍能执行最终 EOF 检查。
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

/-- 面向字符串的便捷入口；文件解析可以直接调用 `parseDimacsBytes`。 -/
def parseDimacs (input : String) : Except String Formula :=
  parseDimacsBytes input.toUTF8

/-- 读取文件并调用会终止的 parser；保留解析诊断，将文件 I/O 错误转为错误结果。 -/
def readDimacsFile (path : System.FilePath) : IO (Except String Formula) := do
  try
    return parseDimacsBytes (← IO.FS.readBinFile path)
  catch error =>
    return .error s!"cannot read '{path}': {error}"

end MicrosatLean
