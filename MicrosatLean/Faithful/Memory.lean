/-!
# The C memory model for the faithful port of `microsat.c`

`microsat.c` allocates one `int` block, `DB`, and carves every array out of it
with a bump allocator (`getMemory`). Every C pointer is therefore modelled as an
offset into one Lean array, and every memory access goes through `ld` (`*p`) and
`st` (`*p = v`).

Stated assumptions (see `FAITHFUL_PORT_HANDOFF.md` §1 and §2):

* `CInt` is unbounded for now. It is an alias so it can become `Int32` in one place.
* C's `malloc` of `mem_max` cells is modelled as an array that is zero beyond its
  physical size. C relies on that block starting zeroed (e.g. C:133, C:204).
-/

namespace MicrosatLean.Faithful

/-- C `int`. Unbounded for now; switch to `Int32` here later. A notation rather than
an `abbrev`, so that `omega` and `simp` see `Int` directly in proofs. -/
notation "CInt" => Int

/-- A C `int*`, modelled as an offset into `DB`. -/
notation "Ptr" => Int

-- C:30  enum { END = -9, UNSAT = 0, SAT = 1, MARK = 2, IMPLIED = 6 };
abbrev END : CInt := -9
abbrev UNSAT : CInt := 0
abbrev SAT : CInt := 1
abbrev MARK : CInt := 2
abbrev IMPLIED : CInt := 6

/-- C `abs` on `int`. -/
@[inline] def abs (x : CInt) : CInt := if x < 0 then -x else x

/-- C `&` on `int` (two's complement). Only applied to small nonnegative values. -/
scoped instance : AndOp CInt := ⟨fun a b => ((Int64.ofInt a) &&& (Int64.ofInt b)).toInt⟩

/-- C `^` on `int` (two's complement). Only applied to small nonnegative values. -/
scoped instance : XorOp CInt := ⟨fun a b => ((Int64.ofInt a) ^^^ (Int64.ofInt b)).toInt⟩

/-- C:32–34 `struct solver`, same fields in the same order. Pointer fields are
offsets into `DB`; `false` and `first` are already shifted by `nVars` exactly as
in C:202–203, so `S.false + lit` is `&S->false[lit]` for negative `lit` too. -/
structure solver where
  DB : Array CInt
  nVars : CInt
  nClauses : CInt
  mem_used : CInt
  mem_fixed : CInt
  mem_max : CInt
  maxLemmas : CInt
  nLemmas : CInt
  buffer : Ptr
  nConflicts : CInt
  model : Ptr
  reason : Ptr
  falseStack : Ptr
  «false» : Ptr
  first : Ptr
  forced : Ptr
  processed : Ptr
  assigned : Ptr
  next : Ptr
  prev : Ptr
  head : CInt
  res : CInt
  fast : CInt
  slow : CInt
  deriving Inhabited

/-- `panic!` that, after reporting `msg`, continues with `fallback` rather than an
arbitrary default. Used where C exits or has undefined behaviour (out of memory, a
negative pointer): the theorems exclude those cases, and continuing with the
unchanged state keeps every other field unaffected in proofs. -/
@[inline] def panicWith {α : Type} (fallback : α) (msg : String) : α :=
  @panic α ⟨fallback⟩ msg

namespace solver

/-- `*p`. Cells beyond the physical array are the zeroed rest of C's block.
A negative pointer is outside C's block: it never happens in a valid state
(a proof obligation), and panics here so testing exposes it. -/
@[inline] def ld (S : solver) (p : Ptr) : CInt :=
  if p < 0 then panicWith 0 "ld: negative pointer" else S.DB.getD p.toNat 0

/-- Extend the physical array with zero cells up to index `i`, then store `v` at
`i`. Only called when `i` is at or beyond the physical size. -/
def growAndStore (DB : Array CInt) (i : Nat) (v : CInt) : Array CInt :=
  (DB ++ Array.replicate (i - DB.size) 0).push v

/-- `*p = v`. Writes beyond the physical array first extend it with the zero
cells it already reads as, so `DB` behaves like C's zeroed `mem_max` block.
`DB` is never shrunk: C keeps old contents past `mem_used` (see `reduceDB`). -/
@[inline] def st (S : solver) (p : Ptr) (v : CInt) : solver :=
  if p < 0 then panicWith S "st: negative pointer"
  else
    let i := p.toNat
    if h : i < S.DB.size then { S with DB := S.DB.set i v h }
    else { S with DB := growAndStore S.DB i v }

end solver

end MicrosatLean.Faithful
