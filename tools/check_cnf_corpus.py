#!/usr/bin/env python3
"""Validate the DIMACS corpus and optionally compare a solver with its oracle."""

from __future__ import annotations

import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
CORPUS = ROOT / "tests" / "cnf"
TIERS = ("smoke", "regression", "stress")


def parse_dimacs(data: bytes) -> tuple[int, list[list[int]]]:
    """Read full-line comments and whitespace-separated, zero-terminated clauses.

    Empty formulas, empty clauses, repeated literals, tautologies, unused
    variables, CRLF, split clauses, and EOF without a newline are all legal.
    Legacy percent/end markers and malformed headers are deliberately rejected.
    """
    header: tuple[int, int] | None = None
    clauses: list[list[int]] = []
    pending: list[int] = []
    for line_number, line in enumerate(data.decode("ascii").splitlines(), 1):
        stripped = line.strip()
        if not stripped or stripped.startswith("c"):
            continue
        fields = stripped.split()
        if fields[0] == "p":
            if header is not None:
                raise ValueError(f"line {line_number}: duplicate header")
            if (len(fields) != 4 or fields[1] != "cnf"
                    or any(re.fullmatch(r"[0-9]+", s) is None for s in fields[2:])):
                raise ValueError(f"line {line_number}: expected p cnf <vars> <clauses>")
            header = (int(fields[2]), int(fields[3]))
            continue
        if header is None:
            raise ValueError(f"line {line_number}: clause before header")
        for field in fields:
            if re.fullmatch(r"-?[0-9]+", field) is None:
                raise ValueError(f"line {line_number}: invalid literal {field!r}")
            literal = int(field)
            if literal == 0 and field.startswith("-"):
                raise ValueError(f"line {line_number}: negative zero is not a literal")
            if abs(literal) > header[0]:
                raise ValueError(f"line {line_number}: literal exceeds variable bound")
            if literal == 0:
                clauses.append(pending)
                pending = []
                if len(clauses) > header[1]:
                    raise ValueError(f"line {line_number}: too many clauses")
            else:
                pending.append(literal)
    if header is None:
        raise ValueError("missing header")
    if pending:
        raise ValueError("unterminated clause at EOF")
    if len(clauses) != header[1]:
        raise ValueError(f"declared {header[1]} clauses, found {len(clauses)}")
    return header[0], clauses


def load_corpus() -> list[dict]:
    """Check every entry and ensure the manifest covers exactly the CNF files."""
    manifest = json.loads((CORPUS / "manifest.json").read_text(encoding="utf-8"))
    if manifest.get("schema_version") != 1 or manifest.get("format") != "DIMACS CNF":
        raise ValueError("unsupported manifest schema or format")
    entries = manifest["instances"]
    paths: set[str] = set()
    hashes: set[str] = set()
    for entry in entries:
        relative = entry["path"]
        if not isinstance(relative, str):
            raise ValueError(f"fixture path must be a string: {relative!r}")
        path = CORPUS / relative
        if ("\\" in relative
                or Path(relative).is_absolute() or ".." in Path(relative).parts
                or not path.resolve().is_relative_to(CORPUS.resolve())
                or path.suffix != ".cnf"):
            raise ValueError(f"unsafe fixture path: {relative!r}")
        if relative in paths:
            raise ValueError(f"duplicate manifest path: {relative}")
        paths.add(relative)
        data = path.read_bytes()
        digest = hashlib.sha256(data).hexdigest()
        if digest != entry["sha256"]:
            raise ValueError(f"{relative}: SHA-256 mismatch")
        if digest in hashes:
            raise ValueError(f"{relative}: byte-identical duplicate fixture")
        hashes.add(digest)
        variables, clauses = parse_dimacs(data)
        if variables != entry["variables"] or len(clauses) != entry["clauses"]:
            raise ValueError(f"{relative}: manifest/header size mismatch")
        if entry["expected"] not in ("SAT", "UNSAT") or entry["tier"] not in TIERS:
            raise ValueError(f"{relative}: invalid expected status or tier")
        for key in ("family", "description", "origin", "status_basis"):
            if not entry.get(key):
                raise ValueError(f"{relative}: missing {key}")
        if entry["origin"] == "satlib":
            for key in ("source_url", "source_member", "source_sha256", "transformations"):
                if key not in entry:
                    raise ValueError(f"{relative}: missing source provenance {key}")
        elif entry["origin"] == "generated":
            if not entry.get("generator"):
                raise ValueError(f"{relative}: missing generator")
        else:
            raise ValueError(f"{relative}: unknown origin")
    actual = {p.relative_to(CORPUS).as_posix() for p in CORPUS.rglob("*.cnf")}
    if actual != paths:
        raise ValueError(f"manifest coverage: missing={sorted(actual - paths)}, "
                         f"absent={sorted(paths - actual)}")
    return entries


def pysat_worker(name: str, path: Path) -> None:
    """Run in a child process so even native solver calls have a time limit."""
    if sys.platform == "win32":
        import ctypes

        # Report a native backend failure through the exit code, without an
        # interactive Windows crash dialog blocking an automated test run.
        ctypes.windll.kernel32.SetErrorMode(0x0001 | 0x0002 | 0x8000)
    from pysat.solvers import Solver

    _, clauses = parse_dimacs(path.read_bytes())
    # Add clauses explicitly: some python-sat versions inspect clause[0] in
    # bootstrap_with and fail on a legal empty clause.
    with Solver(name=name) as solver:
        for clause in clauses:
            solver.add_clause(clause)
        satisfiable = solver.solve()
        if satisfiable:
            model = set(solver.get_model() or [])
            if any(-lit in model for lit in model):
                raise ValueError("solver returned a contradictory model")
            if not all(any(lit in model for lit in clause) for clause in clauses):
                raise ValueError("solver model does not satisfy the original clauses")
        print(json.dumps({"status": "SAT" if satisfiable else "UNSAT"}))


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--tier", choices=TIERS, action="append",
                        help="select tiers to solve (repeatable); format-check all files")
    parser.add_argument("--timeout", type=float, default=5,
                        help="per-instance, per-solver time limit in seconds (default: 5)")
    parser.add_argument("--pysat", nargs="+", metavar="NAME",
                        help="optional python-sat backends, e.g. cadical195 glucose4")
    parser.add_argument("--timings", type=Path,
                        help="optional JSON results with per-instance wall times")
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("--timeout must be positive")
    entries = load_corpus()
    counts = Counter(entry["expected"] for entry in entries)
    print(f"Validated {len(entries)} DIMACS files, headers, hashes, provenance, "
          f"and manifest coverage ({counts['SAT']} SAT, {counts['UNSAT']} UNSAT).", flush=True)
    selected = [e for e in entries if not args.tier or e["tier"] in args.tier]
    solvers = [(name, [sys.executable, "-B", str(Path(__file__).resolve()),
                       "--worker-pysat", name]) for name in args.pysat or []]
    failures = 0
    timings = []
    for name, command in solvers:
        started = time.monotonic()
        passed = 0
        for entry in selected:
            case_started = time.monotonic()
            record = {"solver": name, "path": entry["path"], "expected": entry["expected"]}
            try:
                result = subprocess.run(command + [str(CORPUS / entry["path"])],
                                        capture_output=True, text=True, timeout=args.timeout,
                                        creationflags=subprocess.CREATE_NO_WINDOW if sys.platform == "win32" else 0)
                if result.returncode != 0:
                    raise ValueError(result.stderr[-500:])
                actual = json.loads(result.stdout)["status"]
                if actual != entry["expected"]:
                    raise ValueError(f"expected {entry['expected']}, got {actual}")
                passed += 1
                record.update(actual=actual, outcome="passed")
            except (ValueError, OSError, subprocess.TimeoutExpired) as error:
                failures += 1
                record.update(outcome="timeout" if isinstance(error, subprocess.TimeoutExpired) else "failed",
                              error=str(error))
                print(f"FAIL {name} {entry['path']}: {error}", flush=True)
            record["seconds"] = round(time.monotonic() - case_started, 6)
            timings.append(record)
        print(f"{name}: {passed}/{len(selected)} matched "
              f"in {time.monotonic() - started:.2f}s.", flush=True)
        slowest = max((r for r in timings if r["solver"] == name),
                      key=lambda r: r["seconds"], default=None)
        if slowest:
            print(f"Slowest: {slowest['path']} ({slowest['seconds']:.3f}s).", flush=True)
    if args.timings:
        args.timings.parent.mkdir(parents=True, exist_ok=True)
        args.timings.write_text(json.dumps({"timeout_seconds": args.timeout, "results": timings}, indent=2)
                               + "\n", encoding="utf-8")
    return 1 if failures else 0


if __name__ == "__main__":
    try:
        if len(sys.argv) == 4 and sys.argv[1] == "--worker-pysat":
            pysat_worker(sys.argv[2], Path(sys.argv[3]))
            sys.exit(0)
        sys.exit(main())
    except (ValueError, OSError, KeyError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
