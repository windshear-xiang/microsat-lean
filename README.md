# microsat-lean

A Lean port and formal-verification project for Microsat.

The native implementation follows the CDCL algorithm in the unmodified
[`upstream/microsat.c`](upstream/microsat.c), by Marijn Heule. The source's
copyright and permission notice are retained there and in
[`upstream/LICENSE`](upstream/LICENSE).

## Build and run

The pinned Lean toolchain is in `lean-toolchain`; no additional Lean packages
are required.

```sh
lake build
lake exe microsat-lean --stats tests/cnf/structured/queens-n08-sat.cnf
```

The executable accepts one DIMACS CNF file and prints `s SATISFIABLE` with a
complete `v` model, or `s UNSATISFIABLE`. Exit codes are 10 for SAT, 20 for UNSAT,
and 1 for an input or runtime error. `--no-model` suppresses the model and
`--stats` adds a DIMACS comment containing search statistics. The CLI checks SAT
models against the original input, including clauses normalized by the solver.

## Implementation

| Module | Responsibility |
| --- | --- |
| `Formula` | Literal encoding, input clauses and model evaluation |
| `Dimacs` | Total byte scanner and DIMACS parser; separate file I/O |
| `CDCL.State` | Packed arena, linked watches, false-literal trail, phases, decision list and database reduction |
| `CDCL.Analysis` | First-UIP resolution, recursive clause minimization, backjumping and LBD averages |
| `CDCL.Search` | Propagation, decisions, adaptive restart and resumable search |

The implementation preserves the source's watched-literal scan order,
move-to-front variable heuristic, phase saving, first-UIP minimization, integer
fast/slow LBD averages, restart threshold and model-based learned-clause
selection. It uses native arrays and compact nonnegative indices rather than
linked Lean lists or a clause object per watch. Arrays are consumed through
state updates so their uniquely owned storage can be updated in place.

The following representation and input-handling differences are deliberate:

- Literals encode variable `v` as `2*v` or `2*v+1`, with zero reserved for arena
  terminators. Watch references identify a clause and one of its two link cells.
- Arena storage grows with the actual clauses instead of reserving four GiB.
- Input initialization removes repeated literals and discards tautologies while
  retaining the original formula for independent model checks. Empty formulas,
  empty clauses, sparse numbering and zero declared variables are supported.
- Database compaction remaps root reason pointers and keeps their clauses.
  Under the source's default threshold, these clauses already meet its retention
  criterion; remapping avoids leaving stale references after compaction.

## Tests

```sh
lake exe cdcl-tests
python -B tools/test_solver.py
```

The Lean tests exercise first-UIP resolution and minimization, nonchronological
backjumping, root-preserving restarts, watch-list integrity and reason relocation
through database reduction. They also compare resumed execution across chunk
boundaries and check all 256 subsets of the eight nonempty, nontautological
canonical clauses on two variables against exhaustive truth tables. The CNF
corpus separately covers empty clauses, tautologies, duplicates and input order.

The Python runner executes all 128 CNF fixtures, checks statuses and complete
SAT models independently, rejects malformed inputs, and compares 512
deterministically generated small formulas with a brute-force oracle. It needs
only Python's standard library. Native processes have per-instance time limits;
reports stay in the ignored `tmp/` directory; temporary inputs are removed after
the run. `.agent-memory/` contains only concise, durable agent notes.

The complete native suite passed 657/657 checks: all 128 fixtures, all 512
brute-force cases and all 17 malformed inputs. The slowest corpus case took
1.815 seconds under a three-second limit on the development machine. The Lean
regressions also pass. Differential checks against a C reference matched all
96 structured/SATLIB statuses and conflict counts after applying the same input
normalization; the reference changed only the original four-GiB arena reserve
to 16 MiB for these tests. The checked-in C source remains unchanged.

## Verification status

The actual core CDCL solver is proved correct and terminating for every
well-formed `Formula` and every `Config`. A SAT result contains a complete model
of the input's standard CNF; an UNSAT result means that CNF has no assignment.
The public `CDCL.solve` interface executes this verified total solver. There
are no added axioms, `sorry` proofs, unsafe implementations, or partial drivers.
`runFor` remains available as a total resumable API; fuel exhaustion returns a
machine. The unbounded total evaluator follows the same actual `step` function
and is proved equal to a finite `runFor` execution.

The independent `MicrosatLean/Verification/` subtree uses the pinned toolchain's
`Std.Sat.CNF` API. Its checked results currently cover:

| Area | Proved scope |
| --- | --- |
| `Specification` | Evaluation agreement and satisfiability/UNSAT equivalence between executable formulas and standard CNFs |
| `Logic` | Resolution soundness, ordered clause minimization, model-preserving learning rules, and a canonical clause space of size `3^n` |
| `Representation` | Bounds, genuine packed database layout and meaning, actual clause/watch allocation, assignment/trail/phase updates, root-preserving restart, and move-to-front order preservation |
| `Initialization` | Actual normalization preserves clause models; well-formed initialization never errors, early UNSAT is sound, and successful initialization establishes database, trail, reason-graph, and complete watch-list invariants including cross-head reference uniqueness |
| `Propagation` | Actual replacement/unit branches, complete watch movement and retention, genuine linked-list cursor bounds excluding fuel exhaustion, and completed-watch witnesses for unit closure |
| `Analysis` | Actual reason expansion, resolution, recursive minimization, UIP assertion, decision-prefix history, canonical learned-clause freshness, and cleanup of transient minimization marks |
| `Reduction` | Actual compaction layout and meaning, scheduled limit/count progress, watch filtering, and retention/relocation of genuine active root reasons |
| `Search` | Concrete global machine invariants from actual initialization, preservation and result validity for all four phases, saved watch truth across backjumps/restarts, a strictly decreasing well-founded rank, and a computable total evaluator |
| `Solver` | Closed SAT-model validity, UNSAT soundness and termination of the initialized solver, with a computable input-bound check at the public entry point |

Check the proof modules and audit all their declarations, including private
helpers, with:

```sh
lake build MicrosatLean.Verification
lake env lean tests/Verification.lean
```

The audit checks private and generated declarations too, and permits only
Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms. The main
entry theorem is `MicrosatLean.Verification.solveVerified_correct` in
`MicrosatLean/Verification/Solver.lean`; `solveVerified_ok_valid` covers every
successful returned result. `Search.initialized_search_terminates` proves
finite actual search, and `solveWellFormed_runFor` connects the total evaluator
to the existing runner. Their search preservation and rank premises are proved
for the concrete algorithm.

The proof boundary starts at `Formula` with declared literal bounds. DIMACS
parsing and the thin filesystem/printing IO interface are covered by runtime
tests. Proofs and rank calculations erase from the native total runner, whose
generated C is a tail loop over the actual `step` function.

The [DIMACS CNF test corpus](tests/cnf/README.md) contains 128 boundary,
structured and SATLIB fixtures with expected SAT/UNSAT results. Validate it with:

```sh
python -B tools/check_cnf_corpus.py
```
