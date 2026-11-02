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
| `Solver` | Thin IO wrapper around the verified total solver |

The `Formula` and `CDCL` modules are copied unchanged from
`Tim-dev-verification` at `9aea98c`. The public `Solver` uses the readable
verification framework below: its total runner repeatedly executes the same
`step` function, with the existing input-bound precheck and initializer.

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
canonical clauses on two variables against exhaustive truth tables, including
the public solver under two configurations. Public-entry tests also check
input-bound errors before early UNSAT. The CNF
corpus separately covers empty clauses, tautologies, duplicates and input order.

The Python runner executes all 128 CNF fixtures, checks statuses and complete
SAT models independently, rejects malformed inputs, and compares 512
deterministically generated small formulas with a brute-force oracle. It needs
only Python's standard library. Native processes have per-instance time limits;
reports stay in the ignored `tmp/` directory; temporary inputs are removed after
the run. `.agent-memory/` contains only concise, durable agent notes.

The complete native suite passed 657/657 checks: all 128 fixtures, all 512
brute-force cases and all 17 malformed inputs. The slowest corpus case took
1.872 seconds under a ten-second limit on the development machine. The Lean
regressions also pass. Differential checks against a C reference matched all
96 structured/SATLIB statuses and conflict counts after applying the same input
normalization; the reference changed only the original four-GiB arena reserve
to 16 MiB for these tests. The checked-in C source remains unchanged.

## Verification status

The actual solver is proved correct and terminating for every well-formed
`Formula` and every `Config`. SAT includes a complete model of the original
input; UNSAT excludes every standard CNF assignment. `CDCL.solve` executes this
proved total runner. There are no admitted proofs, additional axioms, unsafe
implementations or partial execution drivers. The CDCL core and original C
reference remain unchanged. `runFor` still provides bounded resumable execution;
fuel exhaustion is never interpreted as SAT/UNSAT.

Read the public framework in this order:

| Module under `MicrosatLean/Verification/` | Reviewable interface |
| --- | --- |
| [`Specification`](MicrosatLean/Verification/Specification.lean) | Input bounds, standard CNF views, evaluation/model bridge, and SAT/UNSAT result specification |
| [`Model`](MicrosatLean/Verification/Model.lean) | True-literal logical trail and its relation to the real packed arena, false-literal trail, reasons, watches and variable order |
| [`Invariant`](MicrosatLean/Verification/Invariant.lean) | Present-state semantic, control/history and canonical-progress predicates |
| [`Transitions`](MicrosatLean/Verification/Transitions.lean) | Admissible logical moves and terminal gates; a real step may implement several moves or logical stuttering |
| [`Progress`](MicrosatLean/Verification/Progress.lean) | The `3^n` clause space and concrete lexicographic variant accounting for learning, reduction, restart and propagation |
| [`Contracts`](MicrosatLean/Verification/Contracts.lean) | Exact logical, initialization, four-phase and rank obligations for the actual solver |
| [`Correctness`](MicrosatLean/Verification/Correctness.lean) | Proved composition for finite `runFor`, a rank-based total runner and initialized solver results, instantiated with the closed implementation proofs |

[`Implementation/Obligations.lean`](MicrosatLean/Verification/Implementation/Obligations.lean)
assembles all eight completed obligations. Detailed proofs are organized below
that interface:

| Directory | Responsibility |
| --- | --- |
| `Implementation/Logic/` | Logical transition preservation, terminal soundness and trace composition |
| `Implementation/Bridge/` | Equivalence of readable/concrete certificates and exact logical views of assignment, analysis, initialization and rank |
| `Implementation/Search/` | Actual four-phase refinement, including watch traversal, learning/assertion, restart/reduction and SAT/UNSAT gates |
| `Implementation/Native/` | Checked packed-state proofs reused from `9aea98c`, with an isolated namespace and the original subfolder structure |

The watch and choice proofs produce actual `LogicalExecution` witnesses;
semantic validity is derived by the generic composition. They also preserve
the separate representation, control/history and progress facts. Learned
freshness, finite scan bounds, saved-prefix recovery and reason relocation are
proved from the implementation. The watch phase requires a real nonroot level
when its root flag is false; only an idle next-literal phase admits an empty
nonroot suffix.

`solveCertified_correct` is the main entry theorem;
`initialized_search_terminates` gives a finite real `runFor` execution with a
valid result. `CDCL.solve_correct` connects the same result to the public IO
wrapper. `solveScaffold` and `solveScaffold_correct` remain compatibility names
for the initial framework. Proofs and the termination rank erase from runtime
code. The boundary starts at bounded `Formula`; DIMACS parsing, filesystem IO,
printing and equivalence to the C implementation remain outside the proof.

Build and audit the full proof graph:

```sh
lake build MicrosatLean.Verification
lake env lean tests/Verification.lean
```

The audit checks all imported verification declarations, including private and
generated helpers, plus the public IO correctness theorem. It permits only
Lean's standard `propext`, `Classical.choice` and `Quot.sound`; any `sorryAx`
dependency or additional axiom fails the check.

The [DIMACS CNF test corpus](tests/cnf/README.md) contains 128 boundary,
structured and SATLIB fixtures with expected SAT/UNSAT results. Validate it with:

```sh
python -B tools/check_cnf_corpus.py
```
