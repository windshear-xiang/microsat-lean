#!/usr/bin/env python3
"""Differential test: faithful Lean port (microsat-faithful) vs upstream C.

Both programs print the status, the model, C's statistics line (mem_used,
conflicts, max_lemmas) and a hash of DB[0..mem_used) after parse and at the end
(see tools/microsat_ref.c and FaithfulMain.lean). The outputs must be identical.

Inputs: the CNF corpus under tests/cnf, plus seeded random 3-SAT instances near
the phase transition, which reach restarts and reduceDB (>= 2000 lemmas).
"""

from __future__ import annotations

import argparse
from pathlib import Path
import random
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parent.parent
REF_SRC = ROOT / "tools" / "microsat_ref.c"
REF_BIN = ROOT / ".lake" / "build" / "bin" / "microsat-ref"
LEAN_BIN = ROOT / ".lake" / "build" / "bin" / "microsat-faithful"


def build() -> None:
    subprocess.run(["lake", "build", "microsat-faithful"], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)
    REF_BIN.parent.mkdir(parents=True, exist_ok=True)
    subprocess.run(["gcc", "-O2", "-std=gnu99", "-w", str(REF_SRC), "-o", str(REF_BIN)],
                   check=True)


def random_3sat(path: Path, n: int, ratio: float, rng: random.Random) -> None:
    m = round(n * ratio)
    lines = [f"p cnf {n} {m}"]
    for _ in range(m):
        vs = rng.sample(range(1, n + 1), 3)
        lines.append(" ".join(str(v if rng.random() < 0.5 else -v) for v in vs) + " 0")
    path.write_text("\n".join(lines) + "\n")


def run(binary: Path, cnf: Path, timeout: float) -> str:
    return subprocess.run([str(binary), str(cnf)], capture_output=True, text=True,
                          timeout=timeout, check=True).stdout


def stat(output: str, key: str) -> str:
    for line in output.splitlines():
        if line.startswith("c statistics"):
            fields = line.split()
            return fields[fields.index(key + ":") + 1]
    return "?"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("paths", nargs="*", type=Path,
                        help="CNF files or directories (default: tests/cnf)")
    parser.add_argument("--random", type=int, default=20, help="random 3-SAT instances")
    parser.add_argument("--seed", type=int, default=20261104)
    parser.add_argument("--min-vars", type=int, default=150)
    parser.add_argument("--max-vars", type=int, default=210)
    parser.add_argument("--timeout", type=float, default=600.0)
    parser.add_argument("--no-build", action="store_true")
    args = parser.parse_args()

    if not args.no_build:
        build()

    roots = args.paths or [ROOT / "tests" / "cnf"]
    files: list[Path] = []
    for root in roots:
        files.extend(sorted(root.rglob("*.cnf")) if root.is_dir() else [root])

    failures = 0
    totals = {"conflicts": 0, "reductions": 0}
    with tempfile.TemporaryDirectory() as tmp:
        rng = random.Random(args.seed)
        for k in range(args.random):
            n = rng.randint(args.min_vars, args.max_vars)
            path = Path(tmp) / f"random-{k:03d}-n{n}.cnf"
            random_3sat(path, n, 4.26, rng)
            files.append(path)

        for cnf in files:
            try:
                expected = run(REF_BIN, cnf, args.timeout)
                actual = run(LEAN_BIN, cnf, args.timeout)
            except subprocess.TimeoutExpired:
                print(f"TIMEOUT {cnf}")
                failures += 1
                continue
            except subprocess.CalledProcessError as error:
                print(f"ERROR   {cnf}: {error}")
                failures += 1
                continue
            name = cnf.name if cnf.is_relative_to(tmp) else cnf.relative_to(ROOT)
            conflicts = stat(expected, "conflicts")
            max_lemmas = stat(expected, "max_lemmas")
            if expected == actual:
                totals["conflicts"] += int(conflicts)
                totals["reductions"] += max_lemmas != "2000"
                print(f"same    {name}  conflicts={conflicts} max_lemmas={max_lemmas}")
            else:
                failures += 1
                exp, act = expected.splitlines(), actual.splitlines()
                first = next((i for i, (a, b) in enumerate(zip(exp, act)) if a != b),
                             min(len(exp), len(act)))
                print(f"DIFF    {name}")
                print(f"  C:    {exp[first][:200] if first < len(exp) else '<end>'}")
                print(f"  Lean: {act[first][:200] if first < len(act) else '<end>'}")

    print(f"\n{len(files) - failures}/{len(files)} identical; "
          f"{totals['conflicts']} conflicts in total; "
          f"{totals['reductions']} instances reached reduceDB")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
