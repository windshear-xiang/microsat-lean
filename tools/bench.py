#!/usr/bin/env python3
"""Benchmark upstream C microsat against the two Lean versions.

  fetch: download a benchmark track from the SAT competition's Global Benchmark
         Database (GBD, https://benchmark-database.de) into bench/<track>/.
         The 2016 Agile track (`agile_2016`, 1579 instances, 60 s limit) is
         the default: many small-to-medium bit-blasted SMT instances.
  run:   solve every CNF with each solver under a timeout, write a CSV, and
         summarize solved counts, PAR-2 and speed relative to C.

Faithfulness: on instances solved by C and a Lean version, the conflict counts
must agree. For the faithful port the DB hashes printed by tools/microsat_ref.c
and FaithfulMain.lean must agree as well. The existing port normalizes clauses
(removes duplicate literals and tautologies), so it may legitimately differ on
instances that contain them.

Examples:
  tools/bench.py fetch agile_2016 --limit 100
  tools/bench.py run bench/agile_2016 --timeout 60 --jobs 8
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import csv
import lzma
from pathlib import Path
import random
import subprocess
import sys
import time
import urllib.request

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / ".lake" / "build" / "bin"
GBD = "https://benchmark-database.de"

# name -> command prefix; the CNF path is appended.
SOLVERS = {
    "c": [str(BIN / "microsat-ref")],
    "faithful": [str(BIN / "microsat-faithful")],
    "port": [str(BIN / "microsat-lean"), "--stats", "--no-model"],
}


def fetch(args: argparse.Namespace) -> int:
    query = urllib.parse.quote(f"track={args.track}")
    with urllib.request.urlopen(f"{GBD}/getinstances?query={query}&context=cnf", timeout=120) as r:
        uris = [line.strip().replace("http://", "https://", 1)
                for line in r.read().decode().splitlines() if line.strip()]
    if not uris:
        print(f"no instances for track {args.track!r}", file=sys.stderr)
        return 1
    if args.limit and args.limit < len(uris):
        uris = sorted(random.Random(args.seed).sample(uris, args.limit))
    out = ROOT / "bench" / args.track
    out.mkdir(parents=True, exist_ok=True)

    def get(uri: str) -> str:
        target = out / (uri.rsplit("/", 1)[-1] + ".cnf")
        if target.exists():
            return "cached"
        with urllib.request.urlopen(uri, timeout=300) as r:
            data = r.read()
        target.write_bytes(lzma.decompress(data) if data[:6] == b"\xfd7zXZ\x00" else data)
        return "ok"

    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        results = list(pool.map(get, uris))
    print(f"{args.track}: {results.count('ok')} downloaded, {results.count('cached')} cached -> {out}")
    return 0


def parse_output(solver: str, stdout: str) -> tuple[str, int | None, str]:
    status, conflicts, hashes = "?", None, []
    for line in stdout.splitlines():
        if line.startswith("s "):
            status = "UNSAT" if "UNSAT" in line else "SAT"
        elif line.startswith("c statistics"):
            fields = line.split()
            conflicts = int(fields[fields.index("conflicts:") + 1])
        elif line.startswith("c conflicts="):
            conflicts = int(line.split()[1].split("=")[1])
        elif line.startswith("c db "):
            hashes.append(line.split()[-1])
    return status, conflicts, "/".join(hashes)


def solve_one(solver: str, cnf: Path, timeout: float) -> dict:
    start = time.perf_counter()
    try:
        done = subprocess.run(SOLVERS[solver] + [str(cnf)], capture_output=True, text=True,
                              timeout=timeout)
        elapsed = time.perf_counter() - start
        status, conflicts, hashes = parse_output(solver, done.stdout)
        if status == "?":
            status = "ERROR"
    except subprocess.TimeoutExpired:
        elapsed, status, conflicts, hashes = timeout, "TIMEOUT", None, ""
    return {"instance": cnf.name, "solver": solver, "status": status,
            "time": round(elapsed, 3), "conflicts": conflicts, "hashes": hashes}


def run(args: argparse.Namespace) -> int:
    if not args.no_build:
        subprocess.run(["lake", "build", "microsat-faithful", "microsat-lean"], cwd=ROOT,
                       check=True, stdout=subprocess.DEVNULL)
        subprocess.run(["gcc", "-O2", "-std=gnu99", "-w", str(ROOT / "tools" / "microsat_ref.c"),
                        "-o", str(BIN / "microsat-ref")], check=True)
    files = sorted(p for d in args.paths for p in (d.rglob("*.cnf") if d.is_dir() else [d]))
    solvers = args.solvers.split(",")
    jobs = [(s, f) for f in files for s in solvers]
    with ThreadPoolExecutor(max_workers=args.jobs) as pool:
        rows = list(pool.map(lambda job: solve_one(job[0], job[1], args.timeout), jobs))

    out = args.csv or ROOT / "bench" / "results.csv"
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(rows[0]))
        writer.writeheader()
        writer.writerows(rows)

    by = {(r["solver"], r["instance"]): r for r in rows}
    names = [f.name for f in files]
    solved = lambda r: r["status"] in ("SAT", "UNSAT")
    print(f"{len(files)} instances, timeout {args.timeout:g}s, {args.jobs} jobs -> {out}\n")
    print(f"{'solver':<10}{'solved':>8}{'SAT':>6}{'UNSAT':>7}{'PAR-2 (s)':>12}")
    for s in solvers:
        rs = [by[(s, n)] for n in names]
        par2 = sum(r["time"] if solved(r) else 2 * args.timeout for r in rs)
        print(f"{s:<10}{sum(map(solved, rs)):>8}{sum(r['status'] == 'SAT' for r in rs):>6}"
              f"{sum(r['status'] == 'UNSAT' for r in rs):>7}{par2:>12.1f}")

    if "c" in solvers:
        print()
        for s in solvers:
            if s == "c":
                continue
            both = [n for n in names if solved(by[("c", n)]) and solved(by[(s, n)])]
            wrong = [n for n in both if by[("c", n)]["status"] != by[(s, n)]["status"]]
            diff = [n for n in both if by[("c", n)]["conflicts"] != by[(s, n)]["conflicts"]]
            c_time = sum(by[("c", n)]["time"] for n in both)
            s_time = sum(by[(s, n)]["time"] for n in both)
            ratio = f"{s_time / c_time:.1f}x C" if c_time > 0 else "n/a"
            line = (f"{s}: {len(both)} solved by both; time {s_time:.1f}s vs C {c_time:.1f}s "
                    f"({ratio}); conflicts differ on {len(diff)}; status differs on {len(wrong)}")
            if s == "faithful":
                hdiff = [n for n in both if by[("c", n)]["hashes"] != by[(s, n)]["hashes"]]
                line += f"; DB hashes differ on {len(hdiff)}"
            print(line)
            for n in (wrong + diff)[:10]:
                print(f"  {n}: C {by[('c', n)]['status']} {by[('c', n)]['conflicts']} conflicts, "
                      f"{s} {by[(s, n)]['status']} {by[(s, n)]['conflicts']} conflicts")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    f = sub.add_parser("fetch", help="download a GBD track")
    f.add_argument("track", nargs="?", default="agile_2016")
    f.add_argument("--limit", type=int, default=0, help="random sample size (0 = all)")
    f.add_argument("--seed", type=int, default=20261104)
    f.add_argument("--jobs", type=int, default=8)
    r = sub.add_parser("run", help="run the solvers")
    r.add_argument("paths", nargs="+", type=Path)
    r.add_argument("--timeout", type=float, default=60.0)
    r.add_argument("--jobs", type=int, default=1)
    r.add_argument("--solvers", default="c,faithful,port")
    r.add_argument("--csv", type=Path)
    r.add_argument("--no-build", action="store_true")
    args = parser.parse_args()
    return fetch(args) if args.command == "fetch" else run(args)


if __name__ == "__main__":
    import urllib.parse  # noqa: E402  (used by fetch)
    sys.exit(main())
