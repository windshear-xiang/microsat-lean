import MicrosatLean.Formula

/-! DIMACS 解析：先扫描字节 token，再检查头部、literal 范围及子句数。
扫描循环都以有限输入长度为界；文件 IO 与纯解析器分开。
当前 solver correctness theorem 的输入边界是 Formula，不包含本模块的解析与文件 IO。
-/

namespace MicrosatLean

namespace Dimacs

/-- 字节扫描位置及用于报错的行列信息。lineStart 允许前导空白后的整行注释，不允许子句行中间的注释。 -/
private structure Cursor where
  /-- 下一次读取的字节偏移。 -/
  offset : Nat := 0
  /-- 从 1 开始的当前行号。 -/
  line : Nat := 1
  /-- 从 1 开始的当前列号。 -/
  column : Nat := 1
  /-- 当前是否仍处于本行首个非空白 token 之前。 -/
  lineStart : Bool := true

/-- 一个 token 的字节起止区间和起始行列；stop 是不包含在区间内的末端位置。 -/
private structure Token where
  /-- token 首字节的偏移。 -/
  start : Nat
  /-- token 末尾之后的字节偏移。 -/
  stop : Nat
  /-- token 起始行号。 -/
  line : Nat
  /-- token 起始列号。 -/
  column : Nat

/-- 识别 DIMACS 扫描器接受的 ASCII 空白字节。 -/
@[inline] private def isWhitespace (byte : UInt8) : Bool :=
  byte == 32 || (byte >= 9 && byte <= 13)

/-- 消费一个字节并更新 offset、行列和行首状态；换行重新进入行首。 -/
@[inline] private def advance (cursor : Cursor) (byte : UInt8) : Cursor :=
  if byte == 10 then
    { offset := cursor.offset + 1, line := cursor.line + 1, column := 1 }
  else
    { cursor with offset := cursor.offset + 1, column := cursor.column + 1 }

/-- 跳过空白与整行注释，再扫描下一个 token；扫描时不分配 token 字符串。
两个循环均以剩余字节数为界，因此任意输入上的扫描都是 total 的。
-/
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

/-- 仅在需要 token 文本时解码对应的 UTF-8 字节片段；无效 UTF-8 使用诊断占位文本。 -/
private def tokenText (input : ByteArray) (token : Token) : String :=
  (String.fromUTF8? (input.extract token.start token.stop)).getD "<non-UTF-8 token>"

/-- 把 token 的起始行列附加到错误信息。 -/
private def atToken (token : Token) (message : String) : String :=
  s!"line {token.line}, column {token.column}: {message}"

/-- 读取必须存在的下一个 token；遇到 EOF 时报告期望的内容。 -/
private def requireToken (input : ByteArray) (cursor : Cursor) (expected : String) :
    Except String (Token × Cursor) :=
  match nextToken input cursor with
  | some result => .ok result
  | none => .error s!"unexpected end of input; expected {expected}"

/-- 直接从 token 的字节区间读取带符号十进制整数。
返回独立的负号标志和绝对值，保留负零，以便调用者显式拒绝它。
-/
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

/-- 读取 header 中的非负计数；任何负号（包括负零）都会触发错误。 -/
private def natural (input : ByteArray) (token : Token) : Except String Nat := do
  let (negative, value) ← decimal input token
  if negative then
    throw (atToken token "header counts must be nonnegative decimal integers")
  return value

/-- 读取 header 的下一个 token，并要求它与 p 位于同一行。 -/
private def headerToken (input : ByteArray) (cursor : Cursor) (line : Nat)
    (expected : String) : Except String (Token × Cursor) := do
  let result ← requireToken input cursor expected
  if result.1.line != line then
    throw (atToken result.1 "the complete 'p cnf' header must be on one line")
  return result

end Dimacs

/-- 解析标准 DIMACS CNF，并检查 header、变量编号、终止零和子句数量。
原样保留输入子句的顺序、重复 literals、空子句与 tautology；求解器随后规范化自己的副本。
注释行以可选空白之后的 c 开始。
-/
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

  -- 每轮消费一个非空 token，或在 EOF 返回；额外一轮允许最后一个字节也是 token 时仍执行 EOF 检查。
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

/-- 接受 String 的便捷包装；字节输入可以直接调用 parseDimacsBytes。 -/
def parseDimacs (input : String) : Except String Formula :=
  parseDimacsBytes input.toUTF8

/-- 读取文件字节并调用 total parser；保留解析诊断，将文件 IO 异常转换为错误信息。 -/
def readDimacsFile (path : System.FilePath) : IO (Except String Formula) := do
  try
    return parseDimacsBytes (← IO.FS.readBinFile path)
  catch error =>
    return .error s!"cannot read '{path}': {error}"

end MicrosatLean
