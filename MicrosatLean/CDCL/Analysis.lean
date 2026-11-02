import MicrosatLean.CDCL.State

/-! 冲突分析对应 upstream/microsat.c 中的 analyze 与 implied。
trail 保存假 literal，reason 子句的首项是由它推出的真 literal，因此分析和 minimization 扫描 reason 的尾部。
有效 reason graph 的依赖指向更早的 trail 位置；所有扫描均使用显式有限界。
minimization 的递归预算耗尽时会保守保留 literal，不会据此删去尚未证明冗余的项。
-/

namespace MicrosatLean.CDCL

/-- 判断一个假 literal 是否可由当前标记的 literals 推出，同时缓存结果。
tag 5 与 6 分别缓存失败和成功；有效 reason graph 上 nVars + 1 足以限制递归深度。
预算耗尽返回 false，含义是尚未证明可删去该 literal。
-/
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

/-- 从 start 扫描 clause 后缀到零终止符，对每个 literal 调用 bump，并调整变量的启发式顺序。 -/
def markClause (s : State) (start : Nat) : State := Id.run do
  let mut s := s
  for i in [start : s.arena.size] do
    let lit := s.db i
    if lit == 0 then
      break
    s := s.bump lit
  return s

/-- 从 candidate 之前反向扫描当前 decision level；在遇到该 level 的 decision 之前没有其他标记项时，candidate 是 first UIP。 -/
def firstUIP (s : State) (candidate : Nat) : Bool := Id.run do
  for offset in [:candidate] do
    let lit := s.trail[candidate - 1 - offset]!
    if s.mark lit == 2 then
      return false
    if s.reason lit == 0 then
      return true
  return true

/-- 按逆 trail 顺序构造经过 minimization 的 learned clause，同时记录 backjump cursor 和 LBD。
尚未清除的 MARK tags 可供 implied 使用；每处理一个 trail 项就把它恢复为普通假值标记。
-/
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

/-- 清除 candidate 及 backjump cursor 以上的赋值，并将 assigned 收缩到 processed。
固定容量的 trail 数组仍保留弹出项，只有活动区间的边界发生改变。
-/
def backjump (s : State) (candidate : Nat) : State := Id.run do
  let mut s := s
  for offset in [:candidate + 1 - s.processed] do
    s := s.unassign s.trail[candidate - offset]!
  return { s with assigned := s.processed }

/-- 沿冲突 implication graph 反向展开 reason，直到遇到 decision 或 first UIP。
分析期间 assigned 临时表示 candidate 的索引，而非通常的活动项数量。
-/
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

/-- 分析非 root 冲突，构造并最小化 first-UIP clause，更新 LBD 启发式并回跳，最后存入 learned clause。
分析期间 assigned 的临时索引含义与参考实现递减后的赋值指针对应；trail 旧项保留到构造完成。
返回更新后的 state 和 learned clause 首 literal 的地址，交给调用者执行 asserting propagation。
-/
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
