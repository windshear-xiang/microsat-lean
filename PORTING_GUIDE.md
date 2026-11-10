# Porting a C SAT solver to Lean: faithful, verified, then fast

A guide for anyone (human or agent) repeating this project for another SAT solver. It
summarizes what was done here for `microsat.c` (251 lines of C), what worked, what did
not, and the criteria we used. Details are in `FAITHFUL_PORT_HANDOFF.md`,
`ASSUMPTIONS.md` and `FAST_PORT_NOTES.md`.

## 0. The three stages and their results

| Stage | Code | Proof | What it establishes |
|---|---|---|---|
| Existing port (`MicrosatLean/CDCL`) | ~600 lines | its own (`MicrosatLean/Verification`) | A correct CDCL *algorithm*, not the C program |
| Faithful port (`MicrosatLean/Faithful`) | ~510 lines | ~12,200 lines | The C program itself terminates, is sound and complete, under stated assumptions |
| Fast port (`MicrosatLean/Fast`) | ~460 lines | ~5,400 lines | The same, re-proved for optimized code, assuming only a valid input |

All three make the same search as C (same answers and conflict counts) on all 98
benchmark instances that C solves. The faithful and fast ports also leave the same
memory contents as C.

| CPU time vs C (geometric mean) | Cluster, 97 instances | One machine, 15 instances |
|---|---|---|
| Existing port | 27.8× | 23.8× |
| Faithful port | 18.2× | 24.0× |
| Fast port | 1.3× (approximate: different nodes) | 1.6× |

The benchmark is a random 100 of the 1,579 instances in the SAT Competition 2016 Agile
track.

## 1. What a faithful translation must do

The goal is to verify **the program**, not the algorithm it implements. Every change of
representation or control flow counts as a discrepancy, even when it seems equivalent:
"we reasoned that it behaves the same" is exactly what the proof is supposed to establish.

**Memory**
- Model C's memory as C has it. microsat allocates one `int` block and carves every array
  out of it with a bump allocator. The faithful port has one `DB : Array Int` with exactly
  that layout, and every C pointer is an offset into it.
- Reproduce the pointer tricks the C way. In microsat:
  - the `clause[-2]` sentinel;
  - `reason = 1 + offset`;
  - an `int* watch` that points either at a list head or at a link cell inside a clause;
  - watch lists threaded through link cells, ended by `END = -9`;
  - in-place compaction in `reduceDB`.
- Copy the environment's semantics, and write them down as assumptions:
  - memory starts zeroed (C reads cells before writing them): reads past the physical
    array return 0, writes past it grow the array;
  - integer width;
  - running out of memory.

**Control flow**
- Each C function becomes one Lean function with the same name and structure. Each C loop
  becomes one Lean loop with C's exit condition: no fuel, no counted loops, no splitting
  into helpers.
- Annotate each line with its C source line (`-- C:143`) so the correspondence can be
  reviewed by reading side by side.
- Recursion C does not bound (microsat's `implied`) goes in `partial_fixpoint` in
  `Option`. The `while` loops stay as `while` in `Id.run do`.

**Logic**
- No extra logic. The existing port removed duplicate literals and tautologies on input,
  rebuilt the clause store in `reduceDB`, computed a limit by division instead of C's
  `while`, kept statistics and settings, and guarded a read C does unguarded. Each of
  these changes behaviour on some input (conflict counts differed on
  `aim-200-6_0-yes1-1`).
- No missing logic either: keep C's dead-looking fields only if C reads them. microsat's
  `res` is never read.

**What to defer, explicitly**
- Integer width: write `abbrev CInt := Int` so it can switch to `Int32` in one place.
- Running out of memory: assume a bound.
- Character-level parsing: start from a token list.
- List each deferral in an `ASSUMPTIONS.md` with an ID (E1–E4 here), the exact condition,
  why it is needed and the date. Never add or change one silently.

**Input validity.** Find, by fuzzing, what inputs C misbehaves on, and state each condition
with a concrete counterexample (`ASSUMPTIONS.md`, V1–V3).
- V1: literals out of range. C hung on 39 of 200 fuzzed files.
- V2: a literal repeated in a clause.
- V3: a clause longer than `nVars`. It overflows C's `buffer` into the trail, and C loops
  forever on a 2-clause file.

These become the fields of `Input.Valid`, the only hypothesis about the input.

## 2. Criteria for faithfulness, from weakest to strongest

Build the checks into a C reference binary (`tools/microsat_ref.c` `#include`s the
unmodified C, replaces only `main`, and adds the extra output; `--dump` prints every
memory cell for finding the first difference) and a differential tester (`tools/diff_faithful.py`).
Compare the whole output; it must be byte-identical.

| Level | Check | What it catches | Used here |
|---|---|---|---|
| 1 | Same answer (SAT/UNSAT) | Wrong solver | yes |
| 2 | Same model for SAT | Different decisions or phases | yes |
| 3 | Same search statistics: conflicts, final `mem_used`, `max_lemmas` | Different decisions, propagation order, learned clauses (`mem_used` sums the clause sizes), reduction schedule | yes |
| 4 | Same memory: a hash of the whole memory after parsing and at the end | Different clause order, watch-list order (link cells are in memory), literal order inside clauses, compaction | yes (the strongest black-box check) |
| 5 | Structural: one function per C function, one loop per C loop, the same fields | Representation changes that happen to give the same output | by review, C line comments |
| 6 | Proof: termination, soundness, completeness of this code | Everything tests miss (overflow, rare paths) | yes |

Further checks we did not need but that help with another solver:
- **Hash at more checkpoints** (every restart, every `reduceDB`) to find where two runs
  first diverge.
- **Counters**: decisions, propagations, watch-list visits, calls to each function,
  restarts, reductions, learned clauses and their total length. Use these when the memory
  layout is not reproduced (then level 4 is impossible), and to localize a difference.
- **Counts of constraints over time**: clauses, learned clauses and memory in use, sampled
  at each restart.

**Test inputs.** Use three sources:
- a corpus of small CNFs;
- seeded random 3-SAT near the phase transition, large enough to reach restarts and
  `reduceDB`. Check that some instances actually exercise both; many benchmarks never
  reach `reduceDB`;
- a real benchmark sample on a cluster.

Generate inputs that satisfy your validity conditions, or normalize them for both sides.

## 3. Proving the faithful port

- The invariant of the main loop (`Inv`, made of `Core`, `Settled` and `Mode`) covers:
  - the memory layout;
  - the trail;
  - the clause database as a list of records tiling the memory;
  - the watch lists as paths through link cells;
  - the reasons, units, decision order and memory bound.
- **Termination**: a lexicographic rank (`maxLemmas` raised, new lemmas learned, trail
  length). `run` is a `partial_fixpoint`. An inductive `RunsTo` relation plus
  well-founded induction on the rank gives a finite derivation, and `RunsTo.run_eq`
  connects it to `run`'s value.
- **`while` loops** are proved with `mvcgen` (`Std.Do`), supplying invariants and
  variants.
- **The most important design decision for reuse**: factor every loop's reasoning into
  named per-iteration lemmas (`Visit.found_step`, `ResInv.resolve`, `BState.step`, …) and
  keep the `mvcgen` proof as glue. The fast port's proof then reused those lemmas almost
  unchanged. Monolithic `mvcgen` proofs would not have been reusable.
- **State lemmas about postconditions, not about one function's result**. Lemmas phrased
  as "for `R = addClause S …`" had to be copied and generalized to "for any `R`
  satisfying `AddClausePost S …`". Phrase them generally from the start.
- **Performance of the verified code matters**. A fallback `(implied …).getD (S, 0)` kept
  a second reference to `S`, so every write inside `implied` copied the whole array: a 7×
  slowdown in the verified port, invisible to the proofs.

## 4. Optimizing

**The rule that made this tractable: the optimized code makes exactly the same search as
C.** Data layout, integer types, control flow and I/O may change. The memory layout
stays, so the level 4 memory-hash check still applies to every optimization, and the
proof can reuse the faithful proof.

**Profile first.**
- Use `valgrind --tool=callgrind` (no `perf` on the cluster) and compare instruction
  counts with C.
- The faithful port ran 29.4 G instructions against C's 0.51 G, spent as follows:
  - about 51% in loop bodies on boxed `Int`;
  - about 29% in allocation and reference counting, because each `while` iteration in
    `Id.run do` allocates a tuple of the mutable variables and calls the body as a closure;
  - about 10% in `Int.toNat` in reads and writes;
  - the rest includes rebuilding the 24-field state record on every write.
- In the existing port, 72% went to copying whole arrays that had lost exclusive
  ownership.

**What worked**

| Change | Why it helps | Effect |
|---|---|---|
| `Array Int32` cells instead of `Int` | Machine arithmetic, no heap numbers | part of 18× → 1.7× |
| Read-only `Lay` for the array offsets, scalars as unboxed fields of a small `St` | No 24-field record rebuilt per write | part of 18× → 1.7× |
| Every loop a self tail-recursive function (`partial_fixpoint`) | Compiles to a plain C loop, nothing allocated per iteration, and gives an unfolding equation for proofs | part of 18× → 1.7× |
| Detach the array from the state before writing (`let (db, s) := s.take`); never read `s.db` while `s` is alive | Writes stay in place instead of copying | part of 18× → 1.7× |
| `propagate`'s outer and watch loops merged into one function over scalar arguments; scalar results (`scanLoop` returns an index, `implied` returns only the array with its answer in a flag) | The hot loop keeps its values in registers, no tuples | part of 18× → 1.7× |
| A scoped `OfNat Int32 n := ⟨⟨n⟩⟩` instance; negative constants written in two's complement | The default instance runs `Int32.ofNat` once and checks it at every use | 1.70× → 1.46× together with the next row |
| `USize` indices with `uget`/`uset`, one native bounds check | `Nat` indices went through boxed comparisons | (above) |
| Explicit tail call in each branch instead of building tuples in `if`/`else` | Fewer allocations and branches | 29.5 s → 27.1 s on one instance |
| Byte-level DIMACS reader | 119 M → 32 M instructions (C takes ~40 M) | 1.46× → 1.42× with the above |

**What did not work**
- A `ByteArray` memory with 4-byte cells: the four byte reads are not merged, and every
  byte write checks ownership. Slower.
- A branch-free variant of the clause-building loop. Slower.
- Merging the reason's bump loop into the resolve loop: no gain, so it was kept separate,
  closer to C.

**Remaining overhead (about 1.3–1.6× C, depending on the CPU)**
- `Array Int32` stores 8 bytes per cell, twice C's memory traffic. Older CPUs suffer more
  (1.6× on a 2014 Xeon against 1.3–1.4× on AMD EPYC).
- Every write checks exclusive ownership.
- Every access does a bounds check. **This one a proof can remove**: `Array.uget` takes a
  proof `h : i < a.size`, erased at compile time. The proof must come from invariants
  carried inside the code (loop arguments holding proofs), which means moving the
  external proof's facts into the code. Measure the gain with an unchecked prototype in a
  scratch copy before doing that work.

**Measuring**
- Keep a quick subset that finishes in about a minute (15 instances here,
  `tools/fast_bench.py`), and check identical output on every run.
- **Record the CPU model with every timing.** The same binaries gave 1.42× on an AMD EPYC
  9354 and 1.59× on an Intel Xeon E5-2670 v3.
- On a cluster, run all solvers for one instance on the same node. Reusing C times from
  other nodes makes ratios approximate.
- Report the geometric mean of per-instance ratios, the median, and total CPU time.
  Exclude instances under 0.1 s from ratios.

## 5. Re-proving the optimized port

- **Abstraction function**: `abs L s M fa sl : solver` maps a fast state to a faithful
  one, with **physical** array equality (`S.DB = toDB s.db = s.db.map Int32.toInt`). The
  fast port grows its array exactly as the faithful one does, so "the same writes in the
  same order" becomes an equation (`ld_sim`, `st_sim`, `abs_st`). Faithful lemmas that
  describe a next state as a sequence of writes (`foundState`, `assign`) then apply
  directly.
- **Leave fields free** where no invariant reads them. Here these are the restart averages
  `fast`/`slow`, `res` and `nClauses`, so `Int32` wraparound in the restart heuristic
  needs no modelling: both restart branches are proved.
- **A `Bounds` invariant** for the no-overflow facts the faithful invariant lacks: array
  size ≤ 2^31, `10n + 7 ≤ 2^30`, `memUsed ≤ 2^30`, `maxLemmas ≤ 2^30`. Every component
  keeps it.
- **Out of memory as an outcome** (`OOM`) instead of a memory assumption. The final
  theorem: for every valid input the fast port terminates, and answers out of memory, or
  SAT with a model that satisfies the input, or UNSAT only for unsatisfiable inputs.
- **Per loop, one of two methods**:
  - equality with the faithful function, for small loops;
  - induction on the fast loop re-proving the faithful postcondition with the faithful
    per-iteration lemmas, for `propagate`, `analyze`, `reduceDB` and `parse`.
- **Parallel proving**:
  - Write each component's statement first, as a theorem with `sorry` in its own file.
  - Let other provers (agents) fill them in.
  - Where one proof needs another component, take its statement as a hypothesis
    (`ConflictSpec`) and discharge it at the end.
  - Freeze the shared files (solver, simulation base) while others build on them.
- **The proof found a real bug.** `Int32.ofInt` wraps, so a header with `nVars ≥ 2^31`
  would have solved a different formula. The fix rejects large `nVars` before the
  conversion. Tests would not have found it.

**Lean pitfalls we hit**
- Kernel "deep recursion" when checking equalities between nested structure updates by
  `rfl`. Fixes:
  - name intermediate states with `generalize`;
  - prove read lemmas once (`ldA`, `ld_abs_eq_ldA`) and rewrite with them.
- `omega` does not see through `Int32.toInt` of compound terms. First rewrite with no-overflow
  lemmas (`toInt_add` and friends), and put the field equalities of the abstraction
  (`(abs …).nVars = L.nVars.toInt`, by `rfl`) in context.
- A `match` in a lemma statement whose discriminant appears in a hypothesis gets
  generalized and then fails to unify. Use `match (generalizing := false) R with`.
- In a multi-line `{ s with … }`, put the fields on a new line after `with`.
- A field named like a global function shadows it inside the structure's namespace.

## 6. Checklist for a new solver

1. Read the C source completely. List its memory layout, pointer tricks, loops, and every
   read that relies on zeroed memory.
2. Write the faithful port with C line comments, `CInt := Int`, and no extra logic.
3. Build a C reference that prints the extra output (model, statistics, memory hashes),
   and a differential tester. Reach byte-identical output on a corpus, random instances
   that exercise every phase (restarts, reductions), and a benchmark sample.
4. Fuzz for inputs where C misbehaves; record validity conditions and assumptions with
   counterexamples.
5. Prove the faithful port with per-iteration lemmas and general postconditions.
6. Profile, then optimize under "same search as C", checking the memory hash after every
   change.
7. Re-prove the optimized port by simulation: an abstraction function with physical
   memory equality, a bounds invariant, out of memory as an outcome, and parallel
   components behind fixed statements.
8. Benchmark C and every port on the same nodes, and record the CPU model.

## 7. File map

| Path | Content |
|---|---|
| `upstream/microsat.c` | The C program |
| `tools/microsat_ref.c` | C reference with the extra output (model, memory hashes) |
| `MicrosatLean/CDCL/` | Existing algorithm-level port |
| `MicrosatLean/Faithful/` | Faithful port (`Microsat.lean`, `Memory.lean`, `Valid.lean`) and its proof (`Verification/`) |
| `MicrosatLean/Fast/` | Fast port (`Solver.lean`) and its proof (`Verification/`, `Main.lean` has the main theorems) |
| `FaithfulMain.lean`, `FastMain.lean` | Executables `microsat-faithful`, `microsat-fast` |
| `tools/diff_faithful.py` | Differential test against C (`--lean-bin microsat-fast` for the fast port) |
| `tools/fast_bench.py` | Quick timing subset |
| `tools/cluster_bench.py` | SLURM benchmark runs (`prepare`, `shard`, `report`) |
| `ASSUMPTIONS.md`, `FAITHFUL_PORT_HANDOFF.md`, `FAST_PORT_NOTES.md` | Assumptions, faithful-port design, fast-port log |

Check the proofs with `lake build MicrosatLean.Fast.Verification.Main` (it builds the
faithful proof as a dependency). The default `lake build` does not build the proofs.
