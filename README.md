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
1.713 seconds under a ten-second limit on the development machine. The Lean
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
reference remain unchanged. `runFor` supports bounded resumable regression
tests; fuel exhaustion is never interpreted as SAT/UNSAT.

Read the public framework in this order:

| Module under `MicrosatLean/Verification/` | Reviewable interface |
| --- | --- |
| [`Specification`](MicrosatLean/Verification/Specification.lean) | Input bounds, standard CNF views, evaluation/model bridge, and SAT/UNSAT result specification |
| [`Model`](MicrosatLean/Verification/Model.lean) | True-literal logical trail and its relation to the real packed arena, false-literal trail, reasons, watches and variable order |
| [`Invariant`](MicrosatLean/Verification/Invariant.lean) | Present-state semantic, control/history and canonical-progress predicates |
| [`Transitions`](MicrosatLean/Verification/Transitions.lean) | Admissible logical moves and terminal gates; a real step may implement several moves or logical stuttering |
| [`Progress`](MicrosatLean/Verification/Progress.lean) | The `3^n` clause space and step-decrease contract; `Progress/Rank.lean` supplies the shared concrete lexicographic rank |
| [`Contracts`](MicrosatLean/Verification/Contracts.lean) | Exact logical, initialization, four-phase and rank obligations for the actual solver |
| [`Termination`](MicrosatLean/Verification/Termination.lean) | Initialization, invariant preservation on running steps and strict rank decrease required by the executable runner |
| [`Correctness`](MicrosatLean/Verification/Correctness.lean) | Direct well-founded correctness proof for the actual runner, composed with initialization and the public solver |

Execution follows `CDCL.solve -> CDCL.solvePure -> CDCL.run -> CDCL.step`.
[`CDCL/Runner.lean`](MicrosatLean/CDCL/Runner.lean) contains the total recursive
loop and returns an ordinary `SolveResult`, with no result certificate or
implementation-proof package. [`Solver.lean`](MicrosatLean/Solver.lean) checks
input bounds, handles initialization outcomes and supplies the IO wrapper.
The runner imports `Verification/Termination` for the proofs needed to justify
recursion; it does not import `Verification/Correctness` or the completed
`Implementation/Obligations` package. `Correctness` imports the solver and
proves its result valid afterward. The invariant, rank and input semantics
remain shared with the existing proof framework.

[`Implementation/Obligations.lean`](MicrosatLean/Verification/Implementation/Obligations.lean)
assembles all eight completed obligations. Detailed proofs are organized below
that interface:

| Directory | Responsibility |
| --- | --- |
| `Implementation/Encoding.lean` | Auxiliary literal/clause lemmas using the single public CNF specification |
| `Implementation/Representation/` | Shared storage types, packed arena layout, trail, reasons and variable ordering |
| `Implementation/Initialization/` | Actual normalization, allocation, initial units and watches |
| `Implementation/Logic/` | Logical transition preservation, terminal soundness, resolution and finite clause space |
| `Implementation/Propagation/` | Watch links, replacement scans, propagation closure and retained reasons |
| `Implementation/Analysis/` | Reason graphs, conflict resolution, minimization, backjumping, assertion and learned-clause freshness |
| `Implementation/Reduction/` | Clause retention, arena compaction, reason relocation and watch rebuilding |
| `Implementation/Search/` | Four-phase logical refinement; `Concrete/` contains concrete search certificates, preservation and rank proofs |
| `Implementation/Bridge/` | Logical views and refinement between abstract semantic facts and concrete algorithm certificates |

The operation proofs originated in `Tim-dev-verification` at `9aea98c` and are
integrated by responsibility; there is no parallel legacy proof tree. CNF views,
input bounds, model semantics and the result predicate have one definition in
`Specification`. `Model` uses the canonical storage predicates from
`Implementation/Representation/Types.lean`, and both proof layers use the same
rank from `Progress/Rank.lean`. There are no clause-entry conversion functions
or identity maps between duplicate storage types. Abstract logical trails and
concrete reason graphs remain distinct because they express different facts.

Unused historical theorem variants and the old execution/termination composition
were removed. Small public-only modules with one consumer are grouped with that
consumer, while the eight obligation entry points remain separate and reviewable.

The watch and choice proofs produce actual `LogicalExecution` witnesses;
semantic validity is derived by the generic composition. They also preserve
the separate representation, control/history and progress facts. Learned
freshness, finite scan bounds, saved-prefix recovery and reason relocation are
proved from the implementation. The watch phase requires a real nonroot level
when its root flag is false; only an idle next-literal phase admits an empty
nonroot suffix.

`step_correct_with` proves that each step preserves the invariant or returns a
valid result. `run_correct` follows `CDCL.run` directly by well-founded induction
on the same rank used to justify its recursion. `solvePure_correct` combines
this result with initialization, and `CDCL.solve_correct` provides the theorem
for the public IO wrapper. `runFor` is a bounded test helper outside this proof
chain. The solver theorems live in `Verification/Correctness`, so callers
needing proofs import `MicrosatLean.Verification`; executable callers can import
only `MicrosatLean.Solver`. Proofs and the termination rank erase from runtime
code. The boundary starts at bounded `Formula`; DIMACS parsing, filesystem IO,
printing and equivalence to the C implementation remain outside the proof.

Build and audit the full proof graph:

```sh
lake build MicrosatLean.Verification
lake env lean tests/Verification.lean
```

The audit checks all imported verification and CDCL declarations, including
private/generated helpers, the total runner and the public IO correctness
theorem. It permits only Lean's standard `propext`, `Classical.choice` and `Quot.sound`; any `sorryAx`
dependency or additional axiom fails the check.

The [DIMACS CNF test corpus](tests/cnf/README.md) contains 128 boundary,
structured and SATLIB fixtures with expected SAT/UNSAT results. Validate it with:

```sh
python -B tools/check_cnf_corpus.py
```
