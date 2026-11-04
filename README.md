# microsat-lean

A formally verified Lean port of [Microsat](https://github.com/marijnheule/microsat), a CDCL SAT solver.

For every well-formed input formula and every solver configuration, the solver
terminates and returns either a complete satisfying assignment or a correct
UNSAT result, using `Std.Sat.CNF` semantics.

## Build and run

Use the Lean toolchain pinned in [`lean-toolchain`](lean-toolchain). No additional
Lean packages are required.

```sh
lake build
lake exe microsat-lean --stats tests/cnf/structured/queens-n08-sat.cnf
```

The executable accepts one DIMACS CNF file. It prints `s SATISFIABLE` and a complete `v` model, or `s UNSATISFIABLE`. Exit codes are 10 for SAT, 20 for UNSAT, and 1 for an input or solver error. `--no-model` suppresses the model;
`--stats` prints search statistics as DIMACS comments.
`--help` lists the options.
SAT models are also checked against the original input before printing.

## Verification

The main theorems are `Verification.solvePure_correct` for the pure solver and
`CDCL.solve_correct` for its IO wrapper. Import `MicrosatLean.Verification` to
use them, or `MicrosatLean.Solver` for the executable API alone.

Execution follows:

```text
CDCL.solve -> CDCL.solvePure -> CDCL.run -> CDCL.step
```

`run` is a total recursive function justified by invariant preservation and a
strictly decreasing lexicographic rank. `Correctness.lean` proves its result
valid directly by well-founded induction on the same rank:

```text
step_correct_with -> run_correct -> solvePure_correct -> CDCL.solve_correct
```

The specification preserves the original input clauses, including duplicates,
tautologies and empty clauses. SAT requires a model covering every declared
variable and satisfying the original formula. UNSAT excludes every total
assignment under `Std.Sat.CNF`. Normalization, propagation, learning, backjumping,
restart and database reduction are included in the implementation proofs.

The proof boundary starts at a well-formed `Formula`. DIMACS parsing, filesystem
IO, printing, returned statistics and equivalence to the C source are outside
the correctness theorem. Proofs and the termination rank erase from runtime
code. `runFor` is a bounded helper for resumable regression tests.

## Code layout

| Module                                             | Responsibility                                                                      |
| -------------------------------------------------- | ----------------------------------------------------------------------------------- |
| [`Formula`](MicrosatLean/Formula.lean)             | Encoded literals, original input clauses, bounds check and model evaluation         |
| [`Dimacs`](MicrosatLean/Dimacs.lean)               | Total byte scanner, DIMACS parser and file reading                                  |
| [`CDCL/State`](MicrosatLean/CDCL/State.lean)       | Packed clause arena, watches, trail, variable order, restart and database reduction |
| [`CDCL/Analysis`](MicrosatLean/CDCL/Analysis.lean) | First-UIP resolution, clause minimization and backjumping                           |
| [`CDCL/Search`](MicrosatLean/CDCL/Search.lean)     | Propagation and the four-phase search transition                                    |
| [`CDCL/Runner`](MicrosatLean/CDCL/Runner.lean)     | Total execution of the actual transition                                            |
| [`Solver`](MicrosatLean/Solver.lean)               | Input validation, initialization and pure/IO entry points                           |

Read the public verification framework in this order:

| Module under `MicrosatLean/Verification/`                       | Responsibility                                                          |
| --------------------------------------------------------------- | ----------------------------------------------------------------------- |
| [`Specification`](MicrosatLean/Verification/Specification.lean) | Standard CNF views, input bounds and SAT/UNSAT specification            |
| [`Model`](MicrosatLean/Verification/Model.lean)                 | Logical state and its representation by concrete storage                |
| [`Invariant`](MicrosatLean/Verification/Invariant.lean)         | Semantic, control/history and progress invariants                       |
| [`Transitions`](MicrosatLean/Verification/Transitions.lean)     | Logical moves, their execution traces and terminal gates                |
| [`Progress`](MicrosatLean/Verification/Progress.lean)           | Step-decrease contract; `Progress/Rank.lean` defines the shared rank    |
| [`Contracts`](MicrosatLean/Verification/Contracts.lean)         | Initialization, phase, logical soundness and rank obligations           |
| [`Termination`](MicrosatLean/Verification/Termination.lean)     | Initialization, preservation and decrease proofs required by the runner |
| [`Correctness`](MicrosatLean/Verification/Correctness.lean)     | Direct correctness proofs for the runner and solver                     |

[`Implementation/Obligations.lean`](MicrosatLean/Verification/Implementation/Obligations.lean)
assembles the eight proved contracts. Detailed proofs are grouped under
`Implementation/{Representation,Initialization,Logic,Propagation,Analysis,Reduction,Search,Bridge}`.
`Search/Concrete` handles concrete search invariants and rank decrease.
`Bridge` relates logical and concrete states; the `Std.Sat.CNF` bridge belongs
to `Specification`. Storage predicates and rank definitions are shared across
these layers.

## Checks

```sh
lake build MicrosatLean MicrosatLean.Verification microsat-lean cdcl-tests
lake env lean tests/Verification.lean
lake exe cdcl-tests
python -B tools/check_cnf_corpus.py
python -B tools/test_solver.py --timeout 10
```

The axiom audit scans all imported library declarations, including private and
generated helpers. It rejects admissions and permits only Lean's standard
`propext`, `Classical.choice` and `Quot.sound` axioms.

Lean regressions cover watches, first-UIP analysis, minimization, backjumping,
restart, reason relocation, invalid input and chunked execution. They check all
256 subsets of the eight canonical nonempty clauses on two variables against
truth tables, including the public solver under two configurations.

The Python runner checks 128 CNF fixtures, 512 deterministic small formulas
against a brute-force oracle, and 17 malformed inputs. It independently checks
SAT models and uses a per-instance timeout. Only Python 3.10 or later is needed;
reports and temporary inputs stay under the ignored `tmp/` directory. See the [corpus documentation](tests/cnf/README.md) for fixture provenance and reproduction.

## Upstream

The algorithm follows Marijn Heule's unmodified
[`upstream/microsat.c`](upstream/microsat.c). Its copyright and permission notice
are retained there and in [`upstream/LICENSE`](upstream/LICENSE).

The port uses dynamically growing arrays and nonnegative literal/watch indices.
Initialization removes repeated literals and tautological clauses while keeping
the original formula for model checks. Database compaction relocates retained
root reason pointers. These changes are covered by the Lean proofs;
formal equivalence to the C implementation is not claimed. Third-party benchmark
provenance and licensing are documented separately in the corpus documentation.
