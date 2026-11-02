import MicrosatLean.CDCL.State

namespace MicrosatLean.CDCL

/-!
冲突分析对应 `upstream/microsat.c` 中的 `analyze` 和 `implied`。
具体 trail 保存为假的文字。reason 子句以被赋为真的文字开头，
因此 resolution 和最小化只需检查各 reason 的 head 之后的文字。

可执行辅助函数采用显式上界：已赋值变量的 reason 只依赖更早的 trail 项，
且每个 arena 子句都有零结束标记。这些是后续 refinement 证明需要建立的 invariant。
最小化预算耗尽时，会保守地将文字留在学习子句中。
-/

/-- 检查某个假文字是否可由当前已标记文字推出，用于学习子句的递归最小化。
与 Microsat 一致，标记 5 和 6 分别缓存失败和成功。
在良构 implication graph 上，递归深度不超过 `nVars + 1`。 -/
def implied : Nat → State → Lit → State × Bool
  | 0, s, _ => (s, false)
  | fuel + 1, s, lit => Id.run do
    let tag := s.mark lit
    if tag > 2 then
      return (s, tag &&& 2 != 0)
    let reason := s.reason lit
    if reason == 0 then
      return (s, false)
    let mut s := s
    for i in [reason + 1 : s.arena.size] do
      let antecedent := s.db i
      if antecedent == 0 then
        break
      if s.mark antecedent != 2 then
        let (next, follows) := implied fuel s antecedent
        s := next
        if !follows then
          return (s.setMark lit 5, false)
    return (s.setMark lit 6, true)

/-- 标记子句中从指定位置开始的后缀，并将相关变量移到启发式链表前端。 -/
def markClause (s : State) (start : Nat) : State := Id.run do
  let mut s := s
  for i in [start : s.arena.size] do
    let lit := s.db i
    if lit == 0 then
      break
    s := s.bump lit
  return s

/-- 向前扫描当前 decision level，检查候选项之前是否还存在分析标记。
若在遇到该层 decision 前没有更早的已标记文字，则候选项是 first UIP（唯一蕴含点）。 -/
def firstUIP (s : State) (candidate : Nat) : Bool := Id.run do
  for offset in [:candidate] do
    let lit := s.trail[candidate - 1 - offset]!
    if s.mark lit == 2 then
      return false
    if s.reason lit == 0 then
      return true
  return true

/-- 按 trail 的逆序构造最小化的学习子句，同时记录 backjump 游标和 LBD（涉及的 decision level 数）。
更早的分析标记仍可供 `implied` 使用。 -/
def buildLearned (s : State) (candidate : Nat) : State × Array Lit × Nat := Id.run do
  let mut s := { s with processed := candidate }
  let mut learned : Array Lit := #[]
  let mut lbd := 0
  let mut levelUsed := false
  for offset in [:candidate + 1 - s.forced] do
    let p := candidate - offset
    let lit := s.trail[p]!
    if s.mark lit == 2 then
      let (next, follows) := implied (s.nVars + 1) s lit
      s := next
      if !follows then
        learned := learned.push lit
        levelUsed := true
    if s.reason lit == 0 then
      if levelUsed then
        lbd := lbd + 1
      levelUsed := false
      if learned.size == 1 then
        s := { s with processed := p }
    s := s.setMark lit 1
  return (s, learned, lbd)

/-- 清除分析候选项以及 backjump 游标以上的所有赋值。
被弹出的内容仍保留在固定容量的 trail 数组中，但不再是活动赋值。 -/
def backjump (s : State) (candidate : Nat) : State := Id.run do
  let mut s := s
  for offset in [:candidate + 1 - s.processed] do
    s := s.unassign s.trail[candidate - offset]!
  return { s with assigned := s.processed }

/-- 沿冲突的 implication graph 回退，直到遇到 decision 或 first UIP。
此阶段中 `assigned` 从赋值个数临时变为候选项索引。 -/
def resolveToUIP (s : State) : State := Id.run do
  let mut s := s
  for _ in [:s.assigned] do
    let candidate := s.assigned - 1
    s := { s with assigned := candidate }
    let lit := s.trail[candidate]!
    if s.reason lit == 0 then break
    if s.mark lit == 2 then
      if firstUIP s candidate then break
      s := markClause s (s.reason lit + 1)
    s := s.unassign lit
  return s

/-- 对非 root 冲突进行 resolution，最小化 first-UIP 子句并 backjump。
`assigned` 通常表示个数，分析期间则表示候选项索引，对应源实现中递减后的赋值指针。
固定容量 trail 保留弹出的内容，直到子句构造结束；返回学习子句首文字位置。 -/
def analyze (s : State) (conflictClauseId : Nat) : State × Nat := Id.run do
  let mut s := { s with
    res := s.res + 1
    stats := { s.stats with conflicts := s.stats.conflicts + 1 } }
  s := markClause s conflictClauseId
  s := resolveToUIP s
  let candidate := s.assigned
  let (next, learned, lbd) := buildLearned s candidate
  s := next
  s := { s with
    fast := s.fast - (s.fast >>> 5) + (lbd <<< 15)
    slow := s.slow - (s.slow >>> 15) + (lbd <<< 5) }
  s := backjump s candidate
  return s.addClause learned false

end MicrosatLean.CDCL
