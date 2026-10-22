#!/usr/bin/env python3
"""Test the native Lean solver against all fixtures and small exhaustive oracles."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import itertools
import json
from pathlib import Path
import random
import subprocess
import sys
import time

sys.dont_write_bytecode = True
from check_cnf_corpus import CORPUS, ROOT, load_corpus, parse_dimacs

STAT_KEYS = ("conflicts", "decisions", "propagations", "restarts", "reductions", "removed_learned")


def decision_and_model(result: subprocess.CompletedProcess[str], variables: int,
                       clauses: list[list[int]], *, require_stats: bool = False) -> tuple[str, dict[str, int]]:
    statuses = set()
    literals = []
    stats = {}
    for line in result.stdout.splitlines():
        fields = line.split()
        if fields == ["s", "SATISFIABLE"]:
            statuses.add("SAT")
        elif fields == ["s", "UNSATISFIABLE"]:
            statuses.add("UNSAT")
        elif fields and fields[0] == "v":
            literals.extend(int(token) for token in fields[1:])
        elif fields and fields[0] == "c":
            for field in fields[1:]:
                if "=" in field:
                    key, value = field.split("=", 1)
                    stats[key] = int(value)
    status = {10: "SAT", 20: "UNSAT"}.get(result.returncode)
    if status is None or statuses != {status}:
        raise ValueError(f"invalid exit/status: {result.returncode}, {statuses}; "
                         f"stderr={result.stderr[-400:]!r}")
    if status == "SAT":
        if not literals or literals[-1] != 0 or 0 in literals[:-1]:
            raise ValueError("SAT model must have exactly one final zero")
        values = {}
        for literal in literals[:-1]:
            variable = abs(literal)
            if not 1 <= variable <= variables:
                raise ValueError("model literal outside declared range")
            if variable in values:
                raise ValueError("model assigns a variable more than once")
            values[variable] = literal > 0
        if len(values) != variables:
            raise ValueError("model is incomplete")
        if not all(any(values[abs(lit)] == (lit > 0) for lit in clause) for clause in clauses):
            raise ValueError("returned model falsifies an original clause")
    elif literals:
        raise ValueError("UNSAT output unexpectedly contains a model")
    if require_stats:
        missing = [key for key in STAT_KEYS if key not in stats]
        if missing:
            raise ValueError(f"missing requested statistics: {', '.join(missing)}")
        if any(stats[key] < 0 for key in STAT_KEYS):
            raise ValueError("solver statistics must be nonnegative")
    return status, stats


def brute_force(variables: int, clauses: list[list[int]]) -> str:
    for values in itertools.product((False, True), repeat=variables):
        if all(any(values[abs(lit) - 1] == (lit > 0) for lit in clause) for clause in clauses):
            return "SAT"
    return "UNSAT"


def fuzz_formulas(count: int):
    rng = random.Random(20261022)
    for case in range(count):
        variables = rng.randrange(9)
        clauses = []
        for _ in range(rng.randrange(5 * variables + 1)):
            width = rng.choice((1, 2, 3, 3, 3, 4))
            clause = [rng.choice((-1, 1)) * rng.randint(1, variables) for _ in range(width)]
            clauses.append(clause)
        if case % 31 == 0:
            clauses.append([])
        yield variables, clauses


def encode(variables: int, clauses: list[list[int]]) -> bytes:
    lines = [f"p cnf {variables} {len(clauses)}"]
    lines += [" ".join(map(str, clause + [0])) for clause in clauses]
    return ("\n".join(lines) + "\n").encode("ascii")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--executable", type=Path,
                        default=ROOT / ".lake" / "build" / "bin" / ("microsat-lean.exe" if sys.platform == "win32" else "microsat-lean"))
    parser.add_argument("--timeout", type=float, default=3)
    parser.add_argument("--fuzz", type=int, default=512,
                        help="deterministic small formulas checked by exhaustive truth tables")
    parser.add_argument("--report", type=Path, default=ROOT / ".agent-memory" / "lean-tests.json")
    args = parser.parse_args()
    if args.timeout <= 0 or args.fuzz < 0:
        parser.error("timeout must be positive and fuzz count nonnegative")
    executable = args.executable.resolve()
    if not executable.is_file():
        parser.error(f"solver not found: {executable}; run lake build first")
    executable_sha256 = hashlib.sha256(executable.read_bytes()).hexdigest()
    entries = load_corpus()
    scratch = ROOT / ".agent-memory" / "test-solver"
    scratch.mkdir(parents=True, exist_ok=True)
    records = []

    def check(name: str, path: Path, expected: str, variables: int,
              clauses: list[list[int]]) -> None:
        started = time.perf_counter()
        record = {"path": name, "expected": expected}
        try:
            result = subprocess.run([str(executable), "--stats", str(path)],
                                    capture_output=True, text=True, timeout=args.timeout,
                                    creationflags=subprocess.CREATE_NO_WINDOW if sys.platform == "win32" else 0)
            actual, stats = decision_and_model(result, variables, clauses, require_stats=True)
            if actual != expected:
                raise ValueError(f"expected {expected}, got {actual}")
            record.update(outcome="passed", actual=actual, stats=stats)
        except (ValueError, OSError, subprocess.TimeoutExpired) as error:
            record.update(outcome="timeout" if isinstance(error, subprocess.TimeoutExpired) else "failed",
                          error=str(error))
            print(f"FAIL {name}: {error}", flush=True)
        record["seconds"] = round(time.perf_counter() - started, 6)
        records.append(record)

    for entry in entries:
        path = CORPUS / entry["path"]
        variables, clauses = parse_dimacs(path.read_bytes())
        check(entry["path"], path, entry["expected"], variables, clauses)
    corpus_failures = sum(r["outcome"] != "passed" for r in records)
    print(f"Corpus: {len(entries) - corpus_failures}/{len(entries)} passed.", flush=True)

    fuzz_path = scratch / "fuzz.cnf"
    for index, (variables, clauses) in enumerate(fuzz_formulas(args.fuzz)):
        fuzz_path.write_bytes(encode(variables, clauses))
        check(f"fuzz/{index}", fuzz_path, brute_force(variables, clauses), variables, clauses)

    malformed = [
        b"", b"1 0\n", b"p wcnf 1 1\n1 0\n", b"p cnf -1 0\n",
        b"p cnf 1 -1\n", b"p cnf\n1 1\n1 0\n", b"p cnf 1 1\n2 0\n",
        b"p cnf 1 1\n1", b"p cnf 1 2\n1 0\n", b"p cnf 1 0\n0\n",
        b"p cnf 1 1\n-0\n", b"p cnf 1 1\n-00\n", b"p cnf 1 1\n+1 0\n",
        b"p cnf 1 1\n1 c inline\n0\n", b"p cnf 0 0\n%\n0\n",
        b"p cnf 0 0\np cnf 0 0\n", b"p cnf 1 1\n\xff 0\n",
    ]
    invalid_path = scratch / "invalid.cnf"
    for index, data in enumerate(malformed):
        invalid_path.write_bytes(data)
        try:
            result = subprocess.run([str(executable), str(invalid_path)],
                                    capture_output=True, timeout=args.timeout,
                                    creationflags=subprocess.CREATE_NO_WINDOW if sys.platform == "win32" else 0)
            if result.returncode != 1 or not result.stderr or b"s SATISFIABLE" in result.stdout or b"s UNSATISFIABLE" in result.stdout:
                raise ValueError("malformed input was not rejected as an input error")
            records.append({"path": f"malformed/{index}", "outcome": "passed"})
        except (ValueError, OSError, subprocess.TimeoutExpired) as error:
            records.append({"path": f"malformed/{index}", "outcome": "failed", "error": str(error)})
            print(f"FAIL malformed/{index}: {error}", flush=True)

    executable_sha256_after = None
    try:
        executable_sha256_after = hashlib.sha256(executable.read_bytes()).hexdigest()
        if executable_sha256_after != executable_sha256:
            raise ValueError("solver executable changed during the test run")
    except (ValueError, OSError) as error:
        records.append({"path": "executable-integrity", "outcome": "failed", "error": str(error)})
        print(f"FAIL executable-integrity: {error}", flush=True)

    counts = Counter(r["outcome"] for r in records)
    print(f"Total: {counts['passed']}/{len(records)} passed (including {args.fuzz} brute-force cases "
          f"and {len(malformed)} malformed inputs).", flush=True)
    measured = [r for r in records if "seconds" in r]
    slowest = max(measured, key=lambda r: r["seconds"])
    print(f"Slowest: {slowest['path']} ({slowest['seconds']:.3f}s).", flush=True)
    args.report.parent.mkdir(parents=True, exist_ok=True)
    args.report.write_text(json.dumps({"executable": str(executable), "executable_sha256": executable_sha256,
                                       "executable_sha256_after": executable_sha256_after, "timeout_seconds": args.timeout,
                                       "results": records}, indent=2) + "\n", encoding="utf-8")
    return 0 if counts["passed"] == len(records) else 1


if __name__ == "__main__":
    sys.exit(main())
