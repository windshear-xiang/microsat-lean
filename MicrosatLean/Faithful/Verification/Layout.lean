import MicrosatLean.Faithful.Microsat

/-!
# Where `initCDCL` puts each array

The offsets of C's arrays in `DB` for `n` variables (C:193–204), and the invariant
that the solver's pointer fields keep these values forever.
-/

namespace MicrosatLean.Faithful.Verification

/-- `model`, `n + 1` cells (C:193). -/
def modelAt (_n : CInt) : Ptr := 0
/-- `next`, `n + 1` cells (C:194). -/
def nextAt (n : CInt) : Ptr := n + 1
/-- `prev`, `n + 1` cells (C:195). -/
def prevAt (n : CInt) : Ptr := 2 * (n + 1)
/-- `buffer`, `n` cells (C:196). -/
def bufferAt (n : CInt) : Ptr := 3 * (n + 1)
/-- `reason`, `n + 1` cells (C:197). -/
def reasonAt (n : CInt) : Ptr := 4 * n + 3
/-- `falseStack`, `n + 1` cells (C:198). -/
def stackAt (n : CInt) : Ptr := 5 * n + 4
/-- `false`, `2n + 1` cells starting at `6n + 5`, shifted by `n` (C:202). -/
def falseAt (n : CInt) : Ptr := 7 * n + 5
/-- `first`, `2n + 1` cells starting at `8n + 6`, shifted by `n` (C:203). -/
def firstAt (n : CInt) : Ptr := 9 * n + 6
/-- The first clause record. The cell before it is the extra `0` of C:204. -/
def clausesAt (n : CInt) : Ptr := 10 * n + 8

/-- The pointer fields hold `initCDCL`'s offsets for `S.nVars` variables. Nothing
after `initCDCL` writes these fields, so every part of the invariant relies on this. -/
structure Layout (S : solver) : Prop where
  nVars_pos : 1 ≤ S.nVars
  model : S.model = modelAt S.nVars
  next : S.next = nextAt S.nVars
  prev : S.prev = prevAt S.nVars
  buffer : S.buffer = bufferAt S.nVars
  reason : S.reason = reasonAt S.nVars
  falseStack : S.falseStack = stackAt S.nVars
  «false» : S.false = falseAt S.nVars
  first : S.first = firstAt S.nVars
  /-- C:204: the cell before the first record is 0 (used by the `clause[-2]` test). -/
  sentinel : S.ld (clausesAt S.nVars - 1) = 0

end MicrosatLean.Faithful.Verification
