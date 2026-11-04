# Handoff: a more faithful Lean port of `microsat.c`

Branch: `henry-faithful-db` (from `Tim-dev3`). C reference: `upstream/microsat.c`
(identical to `../microsat/microsat.c`). Line numbers `C:NN` refer to that file;
Lean line numbers refer to `MicrosatLean/CDCL/*.lean` on this branch.

## 1. Goal and the rule we're using

The goal is to verify **the C program**, not only the CDCL algorithm it implements.
So the Lean code should do what C does, the way C does it. Any change of
representation or control flow counts as a discrepancy, even if we believe it is
equivalent. "We reasoned that it behaves the same" is exactly what is still to be
proved.

The existing port is a good, fully tested model of the **algorithm**. Its
proofs are worth keeping. The plan is to write a **C-shaped layer** next to it,
then later prove that the C-shaped layer refines the current port. That way the
existing correctness proof is reused and does not have to be redone.

**This branch's scope** (most important first):

1. **One `DB` array, laid out exactly as C lays it out**, with C's pointers
   modelled as offsets into it.
2. **C's pointer tricks done the C way** (the `clause[-2]` sentinel,
   `reason = 1 + offset`, the `int* watch` that points at either a list head or a
   link cell, in-place compaction in `reduceDB`).
3. **No extra logic**: remove everything the port added that C doesn't have.
4. **C's loops**: `while` loops stop on C's condition, without fuel.

**Deferred** (put back later, not part of this pass):

- `Nat`/`Int` vs 32-bit `int` (overflow). Use one alias, `abbrev CInt := Int`, so
  it can be switched to `Int32` in one place later.
- The 4 GiB `mem_max` cap and "out of memory".
- DIMACS parsing and input normalization (see §6, item 1, for why
  normalization still matters for testing).
- Proofs. Get the executable model right and differentially tested first.

## 2. What C actually does with memory (the thing to copy)

C allocates **one** `int` block, `DB`, with `mem_max = 1 << 30` cells (C:185, C:192),
and carves every array out of it with a bump allocator, `getMemory` (C:52–57):
`store = DB + mem_used; mem_used += size`.

`initCDCL` (C:181–210) lays it out in this order (`n = nVars`, at least 1):

| Region | Size | Pointer kept in `S` |
|---|---|---|
| `model` | n+1 | `model` |
| `next` | n+1 | `next` |
| `prev` | n+1 | `prev` |
| `buffer` | n | `buffer` (learned clause is built here) |
| `reason` | n+1 | `reason` |
| `falseStack` | n+1 | `falseStack`; `forced`, `processed`, `assigned` point into it |
| `false` | 2n+1 | `false = base + n` (shifted, so `false[-v]` works) |
| `first` | 2n+1 | `first = base + n` (shifted) |
| one `0` cell | 1 | `DB[mem_used++] = 0` (C:204), needed by the sentinel trick |
| clauses... | | input clauses, then `mem_fixed`, then learned clauses |

**Each clause** takes `size + 3` cells (C:59–66):

```
offset:  used        used+1      used+2 ... used+1+size   used+2+size
         [link 0]    [link 1]    [lit0]  ...  [lit size-1] [0]
```

- `addClause` returns `clause = DB + used + 2`, a pointer to the first literal.
- Literals are **signed ints** `±v`, not the port's `2v / 2v+1`.
- The watch lists are linked lists **threaded through the link cells**. `first[lit]`
  holds the DB offset of the first link cell watching `lit`. Each link cell holds the
  offset of the next one, or `END = -9`.
- A clause watches `clause[0]` through `link 0` (offset `used`) and `clause[1]`
  through `link 1` (offset `used+1`), see C:62–63.
- `mem_fixed` is the end of the input clauses (C:65, set by each `irr = 1` add).
  Everything after it is learned clauses (lemmas).
- **Memory is assumed to start zeroed.** C relies on this in a few reads that happen
  before a write, for example `reason[abs(*processed)]` at C:133 when
  `processed == assigned`. On a real OS a fresh 4 GiB `malloc` comes from zeroed pages.
  Record this as a stated assumption.

## 3. How to model it in Lean

### 3.1 The state

```lean
abbrev CInt := Int          -- switch to Int32 later (§1, deferred)
abbrev Ptr  := Int          -- a C pointer = an offset into DB

structure S where
  DB        : Array CInt    -- the one block; see 3.3 for "zeroed reserve"
  nVars nClauses memUsed memFixed memMax maxLemmas nLemmas nConflicts : CInt
  model next prev buffer reason falseStack false_ first : Ptr   -- base offsets (false_/first already shifted by n)
  forced processed assigned : Ptr
  head res fast slow : CInt
```

Keep exactly C's fields: no `stats`, no `config`, no `phases : Array Bool`,
no separate `trail`, `marks`, `reasons`, `first`, `previous` or `next` arrays.

### 3.2 Pointer operations (C → Lean)

Write two tiny helpers and use them everywhere, so every memory access looks like C:

```lean
@[inline] def S.ld (s : S) (p : Ptr) : CInt := s.DB.getD p.toNat 0      -- *p
@[inline] def S.st (s : S) (p : Ptr) (v : CInt) : S := { s with DB := s.DB.set! p.toNat v }  -- *p = v
```

| C | Lean (offsets) |
|---|---|
| `*p`, `p[i]` | `s.ld p`, `s.ld (p + i)` |
| `S->false[lit]` | `s.ld (s.false_ + lit)`, which also works for negative `lit` |
| `S->DB + off` | just `off` (a pointer *is* an offset) |
| `*(S->assigned++) = x` | `s := s.st s.assigned x; s := { s with assigned := s.assigned + 1 }` |
| `*(--S->assigned)` | decrement first, then `s.ld s.assigned` |
| `int* watch = &S->first[lit]` | `let watch : Ptr := s.first + lit` |
| `watch = S->DB + *watch` | `watch := s.ld watch` |
| `*watch = S->DB[*watch]` | `s := s.st watch (s.ld (s.ld watch))` |
| `reason[v] = 1 + (clause - DB)` | `st (reason + v) (1 + clause)` |
| `DB + reason[v]`, `DB + reason[v] - 1` | `ld (reason + v)`, `ld (reason + v) - 1` |

**Why one array matters (the big win):** in C, `watch` can point at `first[lit]`
or at a link cell inside a clause, and the update is the same `*watch = ...` either
way. Once `first` lives inside `DB`, `watch` is a single `Ptr` and the update is one
`st`. The current port needs `previousLink : Option Nat` and two code paths
(`State.lean`, `removeLearnedWatches`; `Search.lean`, `propagateWatches`), because
`first` is a separate array.

**Out-of-range reads:** `getD ... 0` reads a cell beyond the physical array as `0`,
which matches the zeroed reserve. A negative pointer (`p.toNat = 0`) would silently
read `DB[0]`. That never happens in a valid state, but it is a proof obligation, not
something to rely on. If you want such reads to be visible, add a `dbg_trace` or
`panic!` branch in `ld`/`st` while testing.

### 3.3 The 4 GiB reserve without allocating 4 GiB

Don't `Array.replicate (1 <<< 30) 0`. Instead:

- `memMax` is a field (`1 <<< 30` as in C).
- `getMemory size` does C's check (`memUsed + size > memMax` → out of memory;
  deferred, so for now just a `panic!` or an explicit result), then **pushes zeros**
  until the physical array covers `memUsed + size`, and returns the old `memUsed`.
- Reads beyond the physical size return `0` (§3.2), so the array behaves like a
  zeroed `memMax`-cell block.
- **Never shrink `DB`.** C's `reduceDB` only moves `mem_used` back, and the old
  contents stay in memory (§5). Do the same: no `extract`, no `shrink`.

### 3.4 Arrays are values: keep updates in place

Facts we checked with compiled tests (refcount / `dbgTraceIfShared` experiments):

- `set!`/`push` update **in place only if the array has exactly one reference**.
  Otherwise the whole array is copied first (`lean_ensure_exclusive_array`).
  With one giant `DB`, an accidental copy costs the whole database.
- Threading the state linearly (`s := s.st p v` in a `do` block, never keeping the
  old `s`) gave **0 copies** over repeated writes. Keeping the old state or array
  alive gave **1 full copy** at the first write.
- So **never write `let old := s.DB`** and then keep writing `s.DB`. The current
  `reduceDB` does exactly this (`let oldArena := s.arena`, `State.lean` reduceDB).
  The faithful version reads and writes the **same** `DB` through two offsets (§5), so
  this goes away.
- Don't pass `DB` to a helper while also keeping it in `s`. Pass `s` and return `s`.
- To check for copies while testing, wrap a write in `dbgTraceIfShared "DB copied" s.DB`.
  The env var `LEAN_ABORT_ON_NONLINEAR` did **not** catch a copy in our quick test,
  so don't rely on it.
- Out of bounds: `a[i]!` panics and returns the default; `set!` panics and leaves the
  array **unchanged** (logically `setIfInBounds`). With `getD`/`st` as above, keep
  every write within `memUsed`.

## 4. Loops and control flow

### 4.1 Loops

- **C `for` loops with a plain counter** (`for (i = 1; i <= n; i++)`, the copy loop in
  `addClause`, the `i = -nVars .. nVars` loop in `reduceDB`) → Lean `for i in [a:b]`.
  This is fine as is.
- **C `while` loops, and `for` loops whose stop condition is not a counter** → Lean
  `while cond do ...` (or `repeat ... if !cond then break`) inside `Id.run do`,
  stopping on **C's condition**. Use **no fuel**. Fuel adds a "ran out" exit that C
  doesn't have, and then the bound has to be proved sufficient. The current port proves
  that for some loops and not others.
- Termination is proved separately. Lean 4.35 lets proofs unfold a `while` loop:
  `Lean.Loop.forIn_eq_of_monadTail` (`Init/Internal/Order/While.lean:50`) gives the
  one-step equation for any `MonadTail` monad. So you can prove "terminates and
  satisfies P" by induction on a measure, while the code itself stays an honest `while`.
  Check that the instance you need (e.g. `Id`) applies, with a tiny test lemma first.
- Loops to port as `while` (not counted, or the counter changes in the body):
  - restart pop loop C:39
  - `maxLemmas` bump C:69 (**not** the division the port uses)
  - watch-list walk C:74
  - lemma scan C:79 (`i` also advances in the body) and its inner `while (DB[i])` C:81
  - `implied`'s literal loop C:97
  - analyze's trail loop C:105 and the UIP check loop C:108
  - the build loop `while (p >= forced)` C:116
  - the unassign loop C:126
  - propagate's outer loop C:134 and watch loop C:137
  - the replacement scan `for (i = 2; unit && clause[i]; i++)` C:142
  - `solve`'s `for (;;)` C:162
  - the decision scan C:173

### 4.2 Recursion

- `implied` (C:93–100) is recursive. Port it as a recursive function, without fuel.
  Two options:
  - `partial def` runs, but its body can't be unfolded in proofs (opaque).
  - Better: write it in a monad that can express nontermination (for example
    `Option`) with `partial_fixpoint`. That gives real equations, and termination is
    proved later.
- `solve`'s `for (;;)` and the top-level run have the same choice.

### 4.3 Keep C's function structure

- Keep `propagate` as **one function**, with the conflict analysis call **inside**
  the watch loop, `return UNSAT`, `continue` and `break` exactly where C has them
  (C:132–158).
- **Drop** the `Machine` / `Phase` / `step` / `runFor` state machine
  (`Search.lean`). It exists to make every step total, which the faithful version
  doesn't need.
- `analyze` (C:102–130) has `goto build`. Lean has no labeled `break`, so use a
  `Bool` flag (`found := true; break`) that the outer `while` also tests. Note
  this in the code as the one forced deviation.
- Lean `do` supports `return`/`break`/`continue` inside `while`/`for`, so the rest
  ports line for line.

## 5. Pointer tricks to reproduce exactly (and why they're safe in C)

These are what we want to *verify*, so port them as is. Don't replace them with
something "equivalent".

1. **Finding the clause from a watch (C:139–140):**
   `clause = DB + *watch + 1; if (clause[-2] == 0) clause++;`
   - If `*watch = used` (link 0): `clause = used+1`, and `clause[-2] = DB[used-1]` is the
     previous clause's terminating `0`, or the extra `0` from C:204. So `clause++` →
     `used+2`, the first literal.
   - If `*watch = used+1` (link 1): `clause = used+2` already, and `clause[-2] = DB[used]`
     is a link value: an offset > 0, or `END = -9`, so never `0`.
   - The invariant: "the cell before every clause is `0`, and link values are never `0`".
     Compaction in `reduceDB` must keep it (it does, since `addClause` writes the terminator).
2. **`reason[v] = 1 + offset`**, so that `0` can mean "decision". `implied` uses
   `DB + reason - 1` and then `*(++p)` (C:96–97), so it starts at the clause's
   first literal and skips it.
3. **`int* watch` unlinking** (C:72–77 and C:144–146): see §3.2.
4. **`reduceDB` compaction in place (C:68–83):**
   - Unlink every watch to a lemma: any watch `>= mem_fixed`, kept lemmas included.
   - Set `mem_used = mem_fixed`. The old lemmas stay in memory.
   - Walk the old area with `i`. Count the literals that are true under `model`, and
     re-add the lemma with `addClause(S, DB + head, ...)` when `count < k`.
   - That copy is **from `DB` to `DB`**. The destination is never after the source,
     it copies front to back, and the count loop reads the lemma before anything
     overwrites it. So it is safe, and this is a lemma to prove.
   - In Lean this is one `DB`, a read offset and a write offset. No `oldArena`, no
     `extract`.
5. **Stale reasons after `reduceDB`:**
   - C **never updates `reason[]`**. `reduceDB` runs right after `restart` (C:169–171),
     so only root-level (forced) literals are still assigned, and some of their reasons
     point at lemmas that were deleted or moved.
   - It is still safe, because these reasons are never followed:
     - forced literals have `false = IMPLIED` (C:44), so `implied` returns at its
       first line (C:94);
     - `bump` skips `IMPLIED` (C:86);
     - the analyze loop stops at the last decision, which is above `forced` (C:105);
     - every other use of a reason is only a zero/nonzero test (C:119, C:133).
   - Reproduce this. Do **not** add the port's `locked` set or reason `remap`. Proving
     "stale reasons are never followed" is part of verifying C.
6. **The learned clause is built in `buffer`, inside `DB`** (C:118, C:129–130), then
   copied by `addClause`.
   - `analyze` returns the clause **pointer**.
   - `propagate` checks `lemma[1]` (C:155): for a unit lemma, that cell is the
     terminator `0`.
7. **`falseStack` holds false literals; `forced`, `processed` and `assigned` are
   pointers into it.** Levels are never stored. The UIP is found by rescanning
   the trail (C:108–109).

## 6. Extra logic in the current port to remove

From the audit (link in §8), the items that add or change behaviour. File:line refer to this branch.

| # | Current port | C | Action |
|---|---|---|---|
| 1 | `initState` normalizes clauses: removes duplicate literals, drops tautologies (`State.lean`, `normalizeClause` / `initState`) | `parse` adds clauses as read (C:228–241) | Add clauses as given. **This changes behaviour**: on `aim-200-6_0-yes1-1` the conflict count differs unless C is fed the normalized file. Parsing itself is deferred. |
| 2 | `reduceDB`: `locked` set, reason `remap`, `extract`, `oldArena` copy | C:68–83 | Replace with the in-place version (§5, items 4–5) |
| 3 | `maxLemmas` bump computed by division | `while` loop C:69 | Use the `while` |
| 4 | `beginPropagation` guard `processed < assigned && reason ≠ 0` (`Search.lean`, `step`) | `forced = reason[abs(*processed)]`, unguarded (C:133) | Read it unguarded. Relies on zeroed memory (§2) |
| 5 | Detaching `arena`/`first` from the state during the watch scan (`restoreWatchArrays`) | none | Remove. A performance device that one `DB` makes unnecessary |
| 6 | Fuel on `implied`, the watch walk, the replacement scan, the decision scan, `runFor`; `partial def drive` with 4096-step batches | none | Remove (§4) |
| 7 | `firstUIP` / `resolveToUIP` / `buildLearned` / `backjump` split into separate functions with counted loops | one `analyze` (C:102–130) | One function, C's loops |
| 8 | `Stats` counters, and `Config` (`initialLemmaLimit`, `reductionK`) | constants `2000`, `6`; only `nConflicts` and `res` | Keep only C's fields. If you need statistics for testing, compute them in the test harness |
| 9 | Representation: literals `2v/2v+1`; watch ref `2·clauseId+slot`; `0` = end of list; `reason` = `clauseId`; arena starts `#[0,0]`; `phases : Array Bool`; marks indexed by encoded literal | signed literals, link-cell offsets, `END = -9`, `1 + offset`, C's layout (§2) | All replaced by §2–3 |

## 7. Testing (do this before any proofs)

- **Differential test against C, step for step.** Compare the status, the model and
  the conflict count; restarts and reductions give extra coverage. C's `main` prints
  only `s SATISFIABLE` / `s UNSATISFIABLE` and the stats line (C:251). Add a
  `model` printout to a copy of `microsat.c` (`v` lines from `model[1..n]`), since
  the earlier harness lived in a scratch folder that no longer exists.
- With one `DB` laid out like C's, you can go further: **dump `DB[0..mem_used)` at
  the same points in both programs** (after `initCDCL`/parse, after each `reduceDB`)
  and compare them cell by cell. That checks the layout directly.
- Previous results with the current port, for reference:
  - corpus: 95/96 identical in status, conflicts and model (the one difference is
    normalization, §6 item 1);
  - 17 random 3-SAT instances: all identical, including restarts and reductions;
  - 7 instances exercised restarts, 96 reductions in total.
  - Instances that reach `reduceDB` need ≥ 2000 lemmas, e.g. random 3-SAT with
    n = 200–250 and ratio ≈ 4.26.
- Existing tools: `tools/test_solver.py`, `tools/check_cnf_corpus.py`, `tests/cnf/`,
  `lake exe cdcl-tests`.

## 8. Suggested order of work

1. **New namespace and files** (e.g. `MicrosatLean/Faithful/`), leaving
   `MicrosatLean/CDCL/` and `MicrosatLean/Verification/` untouched. They keep building
   and their proofs remain the abstract layer for a later refinement proof.
2. **The state and `ld`/`st`/`getMemory` (§3); `initCDCL`; `addWatch`/`addClause`;
   `assign`/`unassign`/`restart`; `bump`.** Then compare a `DB` dump after loading a
   few small CNFs.
3. **`propagate` + `analyze` + `implied` (one function each, C's loops);
   `solve`.** Then run the differential test on instances without restarts.
4. **`reduceDB` in place.** Then run the differential test on instances with
   restarts and reductions, and check for zero `DB` copies with `dbgTraceIfShared`.
5. **Later:**
   - `CInt := Int32`;
   - out of memory as an explicit outcome;
   - termination proofs (via `Loop.forIn_eq_of_monadTail` / `partial_fixpoint`);
   - invariants: the sentinel, stale reasons never followed, compaction safety, and
     region bounds (no writes outside a region);
   - a refinement to the existing `CDCL` port, reusing `solve_correct` / the
     `Verification` proofs.

Assumptions to state in the final spec: memory starts zeroed; no 32-bit overflow
(or a stated input bound); "out of memory" is an allowed outcome.

References:

- Fidelity audit page (83 differences, how each of the 21 C loops is ported, and a
  per-function table): https://claude.ai/artifact/HXbs62nZNi1ALetvMPUtN3 (private).
- Branch `Tim-dev-verification` has the fully proved version of the current port
  (`solveVerified_correct`, no `sorry`). `Tim-dev3` (this branch's base) has the
  restructured proof layer.
