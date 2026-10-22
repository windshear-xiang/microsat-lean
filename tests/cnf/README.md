# DIMACS CNF test corpus

128 small, uncompressed `.cnf` files for developing and testing the Lean Microsat
port: **70 SAT and 58 UNSAT**, totaling 525,620 bytes. Every file uses a `p cnf`
header and zero-terminated clauses. No solver-specific extensions or malformed
negative-test inputs are included.

| Directory | Instances | SAT | UNSAT | Coverage |
| --- | ---: | ---: | ---: | --- |
| `edge/` | 32 | 20 | 12 | Empty formulas/clauses, units, duplicates, tautologies, pure literals, sparse numbering, long clauses, propagation and legal whitespace layouts |
| `structured/` | 48 | 26 | 22 | Pigeonhole, graph coloring, N-queens, graph-based Tseitin parity, implication chains |
| `satlib/` | 48 | 24 | 24 | Published random 3-SAT, AIM, graph coloring, pigeonhole and circuit-fault benchmarks |

The largest input has 2,180 declared variables and 6,778 clauses. Sparse-numbering
cases intentionally leave unused variables. A zero-variable formula with no
clauses is SAT; a formula containing an empty clause is UNSAT. Those are valid
inputs that the future parser and solver should handle.

## Expected results and test tiers

[`manifest.json`](manifest.json) is the machine-readable inventory. Each entry
contains a path relative to this directory, `expected` (`SAT` or `UNSAT`),
`variables`, `clauses`, `sha256`, `family`, `tier`, a description and a
`status_basis`. Generated cases also identify their generator. Downloaded cases
record archive URL and hash, exact member name, original member hash, output
hash and any transformations.

| Tier | Instances | Intended use |
| --- | ---: | --- |
| `smoke` | 47 | Boundary behavior and small structured formulas |
| `regression` | 63 | Routine solver development with varied encodings |
| `stress` | 18 | Moderately challenging inputs: hole6/hole7, UF/UUF150 and larger parity/pigeonhole cases |

The selection targets decisions within a few seconds on the development machine,
including the stress tier. Difficulty still depends on the solver: the two
circuit-fault cases mainly exercise size and mixed clause lengths, and AIM is
often easy after preprocessing. A future Lean implementation may have different
performance. A timeout is an inconclusive run, never evidence of UNSAT.

The complete selection passed 256 status/model checks with Python 3.12 and
`python-sat` 1.9.dev15: 128/128 with CaDiCaL 1.9.5 and 128/128 with Glucose 4,
using a three-second per-instance limit. The slowest observed case was the odd
5-by-5 torus Tseitin formula: 0.421 seconds with CaDiCaL and 0.454 seconds with
Glucose, including worker startup. These are measurements, not portable runtime
guarantees.

The native Lean solver runner uses this manifest to check every decision and
complete SAT model against the original input:

```sh
python -B tools/test_solver.py
```

All 128 native solver cases passed a three-second limit on the development
machine; the slowest observed case took 1.994 seconds. These are test results,
not Lean proofs of satisfiability, unsatisfiability, or solver correctness.

## Validation

From the repository root, Python 3.10 or later is sufficient for an offline
format/integrity check. No third-party Python package or downloaded archive is
needed:

```sh
python -B tools/check_cnf_corpus.py
```

This parses every file, checks literal bounds and declared clause counts,
compares SHA-256 hashes and metadata, rejects duplicate fixture bytes, and checks
that the manifest covers exactly the `.cnf` files. It accepts all intentional
layout variants, including split clauses, multiple clauses per line, CRLF and
EOF without a final newline. `.gitattributes` preserves these bytes across Git
checkouts.

For optional independent status checks, install `python-sat` in a separate Python
environment and run:

```sh
python -B tools/check_cnf_corpus.py --pysat cadical195 glucose4 --timeout 3
python -B tools/check_cnf_corpus.py --tier smoke --pysat cadical195
```

Each selected instance runs in a separate solver process with a per-instance
time limit. SAT models are also checked against every original clause. A wrong
answer, solver failure or timeout gives a nonzero exit status. The default
per-instance limit is five seconds. The format check always covers all fixtures,
even with `--tier`. Add `--timings .agent-memory/cnf-timings.json` to save a timing
report; times include Python worker startup and model checking. On Windows,
backend failures are reported through the child exit code without crash dialogs.

Generated statuses have explicit mathematical reasons or witnesses. SATLIB
statuses come from the source descriptions. Independent solver agreement is an
additional executable check; no UNSAT certificates or formally checked proofs
are included.

## Reproduction and provenance

The 80 generated cases are deterministic and use only Python's standard library:

```sh
python -B tools/generate_edge_cnf.py --check
python -B tools/generate_structured_cnf.py --check
```

Omit `--check` to regenerate their files. No random seed or network is involved.

The 48 downloaded cases come from the
[SATLIB benchmark collection](https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html):

| Source family | Instances | Source description |
| --- | ---: | --- |
| UF/UUF50, UF/UUF100, UF/UUF150 | 32 | [Unforced filtered random 3-SAT near the phase transition](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/RND3SAT/descr.html) |
| Flat100 | 4 | [Flat graph coloring](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/GCP/descr.html) |
| AIM | 8 | [Artificial formulas with controlled satisfiability](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/AIM/descr.html) |
| PHOLE | 2 | [Pigeonhole formulas](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/PHOLE/descr.html) |
| BF | 2 | [Circuit bridge-fault analysis](https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/DIMACS/BF/descr.html) |

The source archives and exact member selection are pinned in
[`../../tools/fetch_satlib_cnf.py`](../../tools/fetch_satlib_cnf.py). Downloads
are cached only in the ignored `.agent-memory/satlib-cache/` directory. The tool
reads named regular archive members directly without extracting paths.

```sh
python -B tools/fetch_satlib_cnf.py
python -B tools/fetch_satlib_cnf.py --check --offline
python -B tools/update_cnf_manifest.py --check --offline
```

The first command can download the pinned archives when the cache is absent;
the offline commands require that cache. To intentionally update the manifest,
omit its `--check` flag. The normal corpus validator needs no cache.

The 32 random 3-SAT source members end with the legacy bytes `%\n0\n\n` after
their declared clauses. Only this exact suffix is removed to obtain standard
CNF. All other bytes, including source comments and missing final newlines, are
preserved. The other 16 source members are unchanged. Original PHOLE comments
reverse the pigeon/hole counts; the manifest follows the actual encoding and
the SATLIB description (hole6: 7 pigeons into 6 holes; hole7: 8 into 7).

SATLIB makes these benchmarks publicly downloadable; the inspected source pages
do not state an explicit license. Source acknowledgements remain in the files.
The separate license for `upstream/microsat.c` does not establish a license for
third-party benchmark data.
