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
| `Solver` | Input-bound precheck, initialization and standalone IO execution driver |

The `Formula` and `CDCL` modules are copied unchanged from
`Tim-dev-verification` at `9aea98c`. This branch has a new, independently
organized verification scaffold described below. `Solver` keeps the same
input-bound precheck and uses a partial IO driver over the copied `runFor` and
`step` definitions; it does not execute the admitted scaffold.

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
1.994 seconds under a three-second limit on the development machine. The Lean
regressions also pass. Differential checks against a C reference matched all
96 structured/SATLIB statuses and conflict counts after applying the same input
normalization; the reference changed only the original four-GiB arena reserve
to 16 MiB for these tests. The checked-in C source remains unchanged.

## Verification status

The production solver remains executable, tested code with a partial outer IO
driver. Its storage operations, conflict analysis, `step` and `runFor` are total
Lean definitions. Fuel exhaustion returns a resumable machine, never SAT/UNSAT.
The new verification subtree is a **scaffold with eight explicit `sorry`
obligations**, not a completed correctness or termination proof. No new axioms
are declared. The original C source and the production solver are unchanged.

Read the public framework in this order:

| Module under `MicrosatLean/Verification/` | Reviewable interface |
| --- | --- |
| [`Specification`](MicrosatLean/Verification/Specification.lean) | Input bounds, standard CNF views, evaluation/model bridge, and SAT/UNSAT result specification |
| [`Model`](MicrosatLean/Verification/Model.lean) | True-literal logical trail and its relation to the real packed arena, false-literal trail, reasons, watches and variable order |
| [`Invariant`](MicrosatLean/Verification/Invariant.lean) | Present-state semantic, control/history and canonical-progress predicates |
| [`Transitions`](MicrosatLean/Verification/Transitions.lean) | Admissible logical moves and terminal gates; a real step may implement several moves or logical stuttering |
| [`Progress`](MicrosatLean/Verification/Progress.lean) | The `3^n` clause space and concrete lexicographic variant accounting for learning, reduction, restart and propagation |
| [`Contracts`](MicrosatLean/Verification/Contracts.lean) | Exact logical, initialization, four-phase and rank obligations for the actual solver |
| [`Correctness`](MicrosatLean/Verification/Correctness.lean) | Proved composition for finite `runFor`, a rank-based total runner and initialized solver results, conditional on those obligations |

All current admissions are named in
[`Implementation/Obligations.lean`](MicrosatLean/Verification/Implementation/Obligations.lean):
logical-move preservation, terminal soundness, initialization, the four real
search phases, and actual rank decrease. Replace these leaves with detailed
proofs without changing the public specifications. In particular, learned
freshness, sufficient scan bounds, saved-prefix recovery and reason relocation
must be derived from the actual implementation, not added as input assumptions.

The Std CNF bridge and the generic composition proofs contain no admissions.
`solveScaffold_correct` and `initialized_search_terminates` specialize that
composition to the admitted leaves and therefore **still depend on `sorryAx`**.
`solveScaffold` is an opt-in experimental value; `Main` and `CDCL.solve` do not
import or use it. Connecting a completed proof to the public IO entry is future
work. The proof boundary starts at bounded `Formula`; DIMACS parsing, filesystem
IO, printing and equivalence to the C implementation are outside this scaffold.

Build and inspect the scaffold separately from the native executable:

```sh
lake build MicrosatLean.Verification
lake env lean tests/Verification.lean
```

The audit checks every imported verification declaration, including private
helpers. It accepts exactly the eight named direct admissions, rejects admitted
definitions/statements and extra axioms, confirms that generic bridge/composition
has no `sorryAx` dependency, and prints the specialized theorem's dependencies.
The build intentionally reports warnings for the outstanding proofs.

The [DIMACS CNF test corpus](tests/cnf/README.md) contains 128 boundary,
structured and SATLIB fixtures with expected SAT/UNSAT results. Validate it with:

```sh
python -B tools/check_cnf_corpus.py
```
