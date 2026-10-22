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
1.845 seconds under a three-second limit on the development machine. The Lean
regressions also pass. Differential checks against a C reference matched all
96 structured/SATLIB statuses and conflict counts after applying the same input
normalization; the reference changed only the original four-GiB arena reserve
to 16 MiB for these tests. The checked-in C source remains unchanged.

## Verification status

End-to-end solver correctness and search termination have not yet been formally
proved. There are no added axioms, `sorry` proofs, or unsafe implementations.
The parser, storage operations, conflict analysis, `step` and `runFor` are total
Lean definitions. Only the thin unbounded IO execution driver is `partial`.
`runFor` returns a resumable machine on fuel exhaustion, never a SAT/UNSAT answer.
An axiom audit of the CDCL core lists only Lean's standard `propext` and
`Quot.sound`; parser diagnostics additionally depend on `Classical.choice`.

The independent `MicrosatLean/Verification/` subtree uses the pinned toolchain's
`Std.Sat.CNF` API. Its checked results currently cover:

| Area | Proved scope |
| --- | --- |
| `Specification` | Evaluation agreement and satisfiability/UNSAT equivalence between executable formulas and standard CNFs |
| `Logic` | Resolution soundness, ordered clause minimization, model-preserving learning rules, and a canonical clause space of size `3^n` |
| `Representation` | Bounds, actual clause allocation, assignment/trail/phase updates, root-preserving restart, move-to-front order preservation, and semantic reason rules |
| `Propagation` | Actual replacement-scan correctness, unit-assignment semantics, and the SAT rule under assignment coverage and propagation closure |
| `Analysis` | The actual minimizer changes only mark values; exact bounded/cache/decision cases |
| `Search` | Actual decision-scan completeness and assumptions, equivalence to its previous loop, runner composition, arithmetic progress, and termination lifting from a decreasing reachable-state rank |

Check the proof modules and audit all their declarations, including private
helpers, with:

```sh
lake build MicrosatLean.Verification
lake env lean tests/Verification.lean
```

The audit permits only Lean's standard `propext`, `Classical.choice`, and
`Quot.sound` axioms. Conditional preservation and termination-lifting theorems
still require their hypotheses to be proved for the actual search. In
particular, linked-watch coverage and propagation closure, first-UIP and
recursive minimization soundness, asserting-clause freshness, initialization
and database-reduction invariants, and a decreasing global rank remain open.
The partial IO driver has not yet been replaced by a verified total runner.

The [DIMACS CNF test corpus](tests/cnf/README.md) contains 128 boundary,
structured and SATLIB fixtures with expected SAT/UNSAT results. Validate it with:

```sh
python -B tools/check_cnf_corpus.py
```
