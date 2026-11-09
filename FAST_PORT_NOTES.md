# Fast port: notes

Goal: an optimized Lean version of `upstream/microsat.c` (`MicrosatLean/Fast/`,
executable `microsat-fast`), as close to C's speed as pure Lean allows, with the
soundness and completeness theorems proved again for it.

## Rules (set by Henry, 2026-11-09)

- **Same search as C.** Same decisions, propagations, conflicts and learned clauses, so the
  answers and conflict counts match C on every instance. Data layout, integer types,
  control flow and I/O may change.
- **Pure Lean:** no FFI, no `unsafe`.
- **Correctness:** soundness and completeness are proved again, under reasonable
  assumptions (valid input).
  - Out of memory is an explicit outcome (C prints `c out of memory`); it replaces
    assumption E3.
  - Cells are `Int32` (C's `int`).
- **Interleave proving with optimizing.** Some changes are only possible once something
  about them is proved.
- **Fallback:** if the same-search rule blocks real speedups, freeze that version and start a
  new directory that keeps only the main CDCL loop and the same heuristics. Its code
  must be no longer than now; no new features.

## Testing and measuring

- `python3 -B tools/diff_faithful.py <paths> --lean-bin microsat-fast --random 30` checks
  that the whole output equals C's: status, model, statistics, and the FNV hash of
  `DB[0..mem_used)` after `parse` and at the end. The hash check works because the fast
  port keeps C's memory layout exactly.
- `python3 -B tools/fast_bench.py [--sat] [--faithful]` times C and the fast port on a
  fixed subset and checks their outputs again:
  - 14 UNSAT agile instances where C takes 0.3–2.4 s, plus one SAT instance where C
    takes about 21 s;
  - `--sat` adds three longer SAT instances.
- The C reference is `tools/microsat_ref.c`, built with `gcc -O2`.
- Dev node: AMD EPYC 9354. Times are CPU seconds.

## Log

### Step 0: why the verified ("faithful") port is slow (2026-11-09)

Measured with `valgrind --tool=callgrind` on `25cafd2d…` (4,553 variables, 15,988
clauses, 4,162 conflicts). C executes 0.51 G instructions; the faithful port executes
29.4 G.

| Share | Where the faithful port's instructions go |
|---|---|
| ~51% | Loop bodies on boxed `Int`. |
| ~29% | Allocation and reference counting. Each `while` iteration in `Id.run do` allocates a tuple of the mutable variables and a step marker, and calls the body as a closure. |
| ~10% | `Int.toNat` calls in `ld`/`st`. |
| — | Every write rebuilds the 24-field `solver` record. |

In the old port (`MicrosatLean/CDCL`), 72% of instructions go to copying whole arrays,
because its arrays lose exclusive ownership.

A 7× regression was also found and fixed in the verified port: the fallback in
`(implied …).getD (S, 0)` kept a second reference to `S`, so every write inside
`implied` copied `DB`.

### Step 1: first fast port (2026-11-09)

Representation decisions:

- `db : Array Int32` with C's layout: same offsets, records, link cells, `END`. This
  keeps the `DB` hash check, and lets the correctness proof reuse the verified port (see
  the plan below).
- The array offsets (`next`, `prev`, `buffer`, `reason`, `falseStack`, `false`, `first`;
  `model` is at 0) go in a read-only `Lay`. The mutable scalars go in `St`, as unboxed
  `Int32` fields. `res` is dropped: C never reads it.
- Every loop is a self tail-recursive function defined by `partial_fixpoint`. The
  compiler turns these into C loops with no allocation per iteration. Results are scalars
  where possible:
  - `scanLoop` returns the index found;
  - `checkLoop` returns a `Bool`;
  - `implied` returns only the array, with its answer read back from the literal's flag
    (`IMPLIED` means implied).
- `propagate`'s outer loop and watch-list loop are one function, `propLoop`. Its
  arguments are `db`, `assigned`, `processed`, the `forced` flag, `lit` and the watch
  cell; `watch < 0` means "take the next literal". The rest of the state is passed
  untouched.
- **Ownership rule:** before writing to `db`, detach it from `St` (`St.take`). Reading
  `s.db` while `s` is still in use makes the array shared, and then every write copies
  it. This was the cause of the 7× regression above.
- `ld` uses `p.toUInt32.toNat`: a negative `p` lands beyond the array and reads 0, as in
  the faithful `ld`. `st` keeps the faithful growth semantics, so the arrays stay
  identical to the faithful port's.
- Out of memory:
  - `addClause` returns pointer `-1`, and `propagate`/`solve` return the outcome `OOM`;
  - `initCDCL` returns `none` when `10n + 7 > 2^30`, the same check as C's `getMemory`.

Results:

- `diff_faithful.py`: identical to C on `tests/cnf` (128 instances) and on 16 agile plus
  30 random instances (7 of them reach `reduceDB`).
- `fast_bench.py`: geometric mean 1.70× C, total 1.74× C. On `25cafd2d…`: 0.18 s; C
  0.10 s; the faithful port 2.0 s.

### Step 2: constants and indices (2026-11-09)

- **Constants.** An `Int32` numeral goes through `Int32.ofNat`, which the compiler
  evaluates once at run time and then checks at every use (`lean_uint32_once`).
  - A scoped high-priority `OfNat Int32 n` instance builds numerals as `⟨n : UInt32⟩`;
    these compile to C literals, and the instance is definitionally equal to the default.
  - Negation is not constant-folded, so `END` (−9) and `NONE` (−1) are written as
    two's-complement literals.
- **Indices.** `ld`/`st` index with `USize` through `Array.uget`/`uset`, with one native
  bounds check against `db.usize`. With a `Nat` index, every access went through a boxed
  `Nat` comparison.
- Result: 1.70× → 1.46× C (geometric mean, quick subset).

### Step 3: tried and rejected — a `ByteArray` arena (2026-11-09)

`Array Int32` still stores 8-byte boxed scalars, against C's 4-byte cells. A `ByteArray`
with 4 bytes per cell (prototyped in a scratch copy) was slower:

| Version | `25cafd2d…` | `cb3a2be5…` |
|---|---|---|
| `Array Int32` | 0.155 s | 2.88 s |
| `ByteArray`, `Nat` indices with `get!` | 0.33 s | — |
| `ByteArray`, `USize` indices | 0.18 s | 3.36 s |

The four byte accesses are not merged into one 32-bit access, and every byte write
checks exclusive ownership. Kept `Array Int32`.

### Step 4: loop shapes and the DIMACS reader (2026-11-09)

- **`buildLoop`.** Results computed as tuples inside `if`/`else` cost allocations and
  branches. Rewritten with an explicit tail call in each branch: on `aee20862…`, 29.5 s →
  27.1 s (a branch-free variant had been slower). Merging the reason's `bump` loop into
  `resolveLoop` gained nothing (27.08 s vs 27.17 s), so it stays a separate `bumpLoop`,
  closer to C.
- **DIMACS reader.** `readDimacsFast` is a byte-level reader in `FastMain.lean`, outside
  the proved model like C's `fscanf` loop (E4). It replaces the shared validating reader:
  119 M → 32 M instructions on `25cafd2d…`, where C's `fscanf` path takes about 40 M.
- **Result:** 1.42× C (geometric mean), 1.43× total CPU. All outputs identical to C on
  `tests/cnf`, the 16 agile instances and 30 random ones (174/174).
- **Longer SAT instances** (`fast_bench.py --sat`, adding `ff852713`, `d9caf7ae`,
  `a6d5c1d5`, where C takes 35–46 s): 1.44–1.49× each; whole set 1.43× geometric mean,
  1.46× total CPU (154.8 s C vs 225.4 s fast). All outputs identical to C. The ratio holds
  on long runs.
- **What remains** (callgrind, `25cafd2d…`): 1.37 G instructions vs C's 0.51 G;
  `propLoop` is 0.78 G of them. Each access costs a bounds check, plus unboxing on reads,
  and an exclusive-ownership check and unboxing on writes. Removing the bounds checks
  would need proofs inside the code that every index is in range.

### Step 5: `parse` guards `nVars` before converting it (2026-11-09)

While stating `parse_fast`, I found a correctness gap. `Int32.ofInt` wraps, so a header
with `nVars ≥ 2^31` could become a small variable count. The fast `parse` now:
- returns out of memory for `nVars > 107374181 = (2^30 - 7) / 10`, before the conversion.
  At that size C's `initCDCL` runs out of memory too.
- keeps `nClauses` as an `Int` counter.

For a valid input, `nVars` and every literal are then converted exactly. There is no
measurable cost (it runs once).

## Correctness plan

The theorems are proved for the fast port by simulation to the verified faithful port,
reusing its invariant and its proved lemmas.

**Relation `Sim L s S`** between a fast state (`Lay`, `St`) and a faithful `solver`:
- the cells agree: `S.DB = toDB s.db`, the cells mapped by `Int32.toInt`, with
  `s.db.size ≤ 2^31`;
- the offsets agree with `L`, and the counters and pointers agree with `s`;
- `res`, `fast`, `slow`, `mem_max` and `nClauses` are left free.

**Base lemmas** (done, `MicrosatLean/Fast/Verification/Sim.lean`):
- `ld_sim`: a fast read gives the faithful read;
- `st_sim`: a fast write gives the faithful write, and the arena stays at most 2^31
  cells;
- `toInt_add`/`sub`/`neg`/`absC`: `Int32` arithmetic is `Int` arithmetic when there is
  no overflow;
- `assign_sim`: the first function-level simulation.

**Loops.** Each fast loop is proved by induction on its own iterations (unfolding equations
of the `partial_fixpoint` definitions, with the faithful port's loop variants as measures).
The invariant at each iteration is the faithful port's loop invariant (`WInv`, `ScanInv`,
`ResInv`, `BState`, …) for a faithful state related to the fast state by `Sim`. Each
iteration then uses the faithful port's per-case lemmas:
- in `propagate`: `Visit.true_step`, the unit/assign step, the found-literal step,
  `Visit.conflict_step`;
- in `analyze`: `BumpInv.step`, `ResInv.resolve`, `BState.step`, …

So the faithful `while` code is not reasoned about a second time; only its invariants and
lemmas are reused. The bounds needed for "no overflow" (literals within ±n with
n ≤ 1.07·10^8; pointers below `memMax = 2^30`) come from those invariants.

**Memory.**
- The faithful state is taken with `mem_max := memoryBound input`. The faithful
  invariant (`Core.memory`) then holds, and the faithful `getMemory` never takes its
  out-of-memory branch.
- The fast `addClause` checks against `2^30` itself. When the check passes, both
  ports do the same writes; when it fails, the fast port stops with `OOM`.

**Restarts.**
- The restart test is the only place where `Int32` wraparound (`fast`/`slow`) can
  differ from `Int`.
- The fast iteration is simulated by the faithful parts separately: `propagate_spec`,
  then `afterConflict`, then the decision.
- `afterConflict` runs on a faithful state with `fast`/`slow` set so that it makes the
  same restart decision as the fast port. `Settled` does not read these fields
  (`Settled.withStats`).
- The step-level contracts (preserve, decrease, finish) are then re-derived for the fast
  step as in the faithful `Step.lean`.

**Decision (2026-11-09): physical equality through an abstraction function.**
- The faithful state stands for the fast one exactly: `S.DB = toDB s.db`, the same physical
  array, not just equal reads. Both ports grow the array the same way (`growAndStore`),
  so the arrays stay identical write by write (`st_sim`).
- Then a faithful lemma that describes its next state as a sequence of `st`, e.g.
  `foundState`, `Visit.true_step`, `copied_step`, applies directly to the fast state.
  The fast code performs the same writes in the same order.
- Plan: replace the relation `Sim` by a function
  `abs (L : Lay) (s : St) (mem_max fast slow : Int) : solver`, so that "abstraction of
  the next fast state = faithful next state" is an equation, proved with `solver.ext`.

**Per loop: two ways.** The faithful contracts are stated about the exact output of the
faithful functions (e.g. "`restart S` satisfies …"). So each fast loop gets one of:
- **(a) Equality** with the faithful loop, proved by `mvcgen` on the faithful code with
  the invariant "the fast loop from the related state yields the same final result". Used
  for small loops whose faithful reasoning lives inline in `mvcgen` conditions
  (`restart`, the decision scan, `addClause`'s copy loop).
- **(b) The same postcondition re-proved** by induction on the fast loop, with the faithful
  loop invariant and the faithful per-iteration lemmas. Used where those lemmas are
  separate (`propagate`, `analyze`, `reduceDB`).

**Theorem.** For a valid input, the fast solver terminates, and either reports out of
memory, or answers SAT with a satisfying model, or answers UNSAT for an unsatisfiable
input.

**Proof status (2026-11-09): complete.** No `sorry`. The main theorems depend only on
`propext`, `Classical.choice` and `Quot.sound`. Check with
`lake build MicrosatLean.Fast.Verification.Main` (the default `lake build` does not build
the proofs, as for the faithful port). The proof is 5.4k lines on top of the faithful
proof's lemmas. Files in `MicrosatLean/Fast/Verification/`:

| File | What it proves | Method |
|---|---|---|
| `Sim.lean` | reads/writes, `assign`, `addWatch`, `unassign`, `addClause` (`AddClausePost`) | base |
| `Restart.lean` | `restart_fast` (faithful `restart_spec`) | (b) |
| `Decide.lean` | `decideLoop_spec` (faithful `scan_spec`), `assignDecision_sim` | (b), equality |
| `Inv.lean` | `Bounds` (no-overflow facts), `conflictNext` | definitions |
| `Propagate.lean` | `propagate_fast` (faithful `propagate_spec`, plus `OOM`) | (b) |
| `ReduceDB*.lean` | `reduceDB_fast` (faithful `reduceDB_spec`) | (b) |
| `Parse*.lean` | `parse_fast` (faithful `parse_correct`, plus `OOM`) | (b) |
| `Step.lean` | `fstep_cases`, `frun_correct` (termination by the faithful `rank`) | |
| `Main.lean` | `microsatFast_correct` and its corollaries | |
| `Analyze*.lean` | `conflict_fast` (faithful `Visit.conflict_step`): bump, `implied`, resolve, build, unassign, learn | (b) |

- **`propagate`**: two nested inductions. The outer one is on `outMeasure`, with the cursor at
  a list end. The inner one is on the links left (`linksAfter`), with the faithful `WInv`
  as the invariant. Each visited link uses the faithful `Visit.found_step`, `true_step`,
  `assign_step` and `scan_all_false`. The fast writes equal the faithful `foundState`/`assign`
  exactly (`found_sim`, `assign_abs`, through `abs_st`).
- **Conflicts**: `propagate`'s proof takes `conflict_fast`'s statement as a hypothesis
  (`ConflictSpec`), so the two proofs were written in parallel; `Main.lean` discharges it.
- **`implied`**: the fast one returns only the arena (the answer is the flag of the
  literal). Its proof copies the faithful `implied_at` induction and shows that the faithful
  answer `r ≠ 0` holds exactly when the flag ends `IMPLIED`, at all four return points.
- **`reduceDB`'s ignored `addClause` pointer**: proved never `NONE`. The re-added lemmas
  move down, so they fit below the old `memUsed ≤ 2^30`.
- **`fast`/`slow`**: `abs` leaves them free, so both restart branches are proved. No faithful
  state has to mimic the `Int32` restart test.
- **Generalized faithful lemmas**: the faithful lemmas about "the result of the faithful
  `addClause`" were restated for any state meeting `AddClausePost`, copying the faithful
  proofs. Examples: `ParseCore.after_add'`, `KeepInv.add_of_post`. The faithful files are
  untouched.

**Main theorem** (`Main.lean`). For every valid input (`Input.Valid` only; no memory
assumption, no `Int` assumption):
- `microsatFast_correct`: `microsatFast input` (the fast `main` without I/O) terminates
  (`FTerminates`: `solve`'s loop reaches its end in finitely many steps).
- It answers out of memory, or SAT with the printed model (`fastModel`, read from `db` as
  `printModel` does) satisfying the input, or UNSAT for an unsatisfiable input.
- Corollaries: SAT and UNSAT are sound. A satisfiable input gives SAT or out of memory; an
  unsatisfiable one gives UNSAT or out of memory.
