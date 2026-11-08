#!/usr/bin/env python3
"""Cluster benchmark: upstream C vs the faithful Lean port vs the existing Lean port.

Runs on Babel under Slurm (partition `preempt`, QoS `preempt_cpu_qos`, CPU only).
For each instance, one task runs, on one core, one after another:

  1. C, with limit --c-timeout (default 5000 s);
  2. only if C solved it: the faithful port, then the existing port, each with the
     limit clamp(--factor * C's CPU time, --min, --max) (default 100x, 600 s, 24 h).

Jobs are resumable: a result line is appended (and fsynced) per finished instance,
and a requeued or resubmitted job skips instances that are already done. A task
cut off by preemption is rerun from the start.

  prepare RUN      build the three binaries and freeze them in bench/runs/RUN/bin,
                   record the git state, list the instances and check them against
                   ASSUMPTIONS.md section 1, write the task list
  shard RUN I N    run shard I of N (this is what the sbatch job calls)
  status RUN       progress
  report RUN       summary and bench/runs/RUN/results.csv

Times are CPU times (user + system, from wait4) of the solver process; wall time,
peak memory, host and CPU model are recorded too.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import random
import shutil
import socket
import statistics
import subprocess
import sys
import tempfile
import threading
import time

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parent.parent
RUNS = ROOT / "bench" / "runs"
SOLVERS = {
    "c": ["microsat-ref"],
    "faithful": ["microsat-faithful"],
    "port": ["microsat-lean", "--stats", "--no-model"],
}
LEAN = ("faithful", "port")
SOLVED = ("SAT", "UNSAT")


# ---------------------------------------------------------------- helpers

def cpu_model() -> str:
    for line in Path("/proc/cpuinfo").read_text().splitlines():
        if line.startswith("model name"):
            return line.split(":", 1)[1].strip()
    return "?"


def set_name(path: str) -> str:
    return "corpus" if path.startswith("tests/cnf") else Path(path).parent.name


def check_valid(path: Path) -> list[str]:
    """Which conditions of ASSUMPTIONS.md section 1 (V1-V3) the file violates."""
    violations: set[str] = set()
    n = m = None
    count, clause = 0, []
    for line in path.open():
        tokens = line.split()
        if not tokens or tokens[0] == "c":
            continue
        if tokens[0] == "p":
            n, m = int(tokens[2]), int(tokens[3])
            continue
        for token in tokens:
            lit = int(token)
            if lit != 0:
                if n is None or abs(lit) > n:
                    violations.add("V1")
                clause.append(lit)
                continue
            count += 1
            if len(set(clause)) < len(clause):
                violations.add("V2")
            if n is not None and len(clause) > n:
                violations.add("V3")
            clause = []
    if n is None or n < 0 or clause or count != m:
        violations.add("V1")
    return sorted(violations)


def parse_output(text: str) -> tuple[str, int | None, str]:
    status, conflicts, hashes = "?", None, []
    for line in text.splitlines():
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


def read_jsonl(path: Path) -> list[dict]:
    rows = []
    if path.exists():
        for line in path.read_text().splitlines():
            try:
                rows.append(json.loads(line))
            except json.JSONDecodeError:
                pass  # a line cut short by preemption
    return rows


def all_results(run: Path) -> dict[str, dict]:
    results = {}
    for path in sorted(run.glob("results-*.jsonl")):
        for row in read_jsonl(path):
            results[row["id"]] = row
    return results


def run_solver(bindir: Path, solver: str, cnf: Path, timeout: float) -> dict:
    cmd = [str(bindir / SOLVERS[solver][0])] + SOLVERS[solver][1:] + [str(cnf)]
    # Output goes to a file, not a pipe: a model line can exceed the pipe buffer.
    with tempfile.TemporaryFile(mode="w+") as out:
        start = time.perf_counter()
        proc = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT)
        timed_out = threading.Event()

        def kill() -> None:
            timed_out.set()
            proc.kill()

        timer = threading.Timer(timeout, kill)
        timer.start()
        _, wait_status, usage = os.wait4(proc.pid, 0)
        timer.cancel()
        wall = time.perf_counter() - start
        proc.returncode = os.waitstatus_to_exitcode(wait_status)
        out.seek(0)
        text = out.read()
    status, conflicts, hashes = parse_output(text)
    if timed_out.is_set():
        status = "TIMEOUT"
    elif status == "?":
        status = "ERROR"
    row = {"solver": solver, "status": status, "limit": round(timeout, 1),
           "cpu": round(usage.ru_utime + usage.ru_stime, 3), "wall": round(wall, 3),
           "maxrss_kb": usage.ru_maxrss, "exit": proc.returncode, "conflicts": conflicts,
           "hashes": hashes}
    if status == "ERROR":
        row["tail"] = text[-400:]
    return row


# ---------------------------------------------------------------- commands

def prepare(args: argparse.Namespace) -> int:
    run = RUNS / args.run
    if (run / "bin").exists() and not args.force:
        print(f"{run}/bin exists; use --force to rebuild", file=sys.stderr)
        return 1
    if any(run.glob("results-*.jsonl")) and not args.force:
        print(f"{run} already has results; use --force to replace its setup", file=sys.stderr)
        return 1
    (run / "bin").mkdir(parents=True, exist_ok=True)
    subprocess.run(["lake", "build", "microsat-faithful", "microsat-lean"], cwd=ROOT, check=True,
                   stdout=subprocess.DEVNULL)
    subprocess.run(["gcc", "-O2", "-std=gnu99", "-w", "tools/microsat_ref.c", "-o",
                    str(run / "bin" / "microsat-ref")], cwd=ROOT, check=True)
    for name in ("microsat-faithful", "microsat-lean"):
        shutil.copy2(ROOT / ".lake" / "build" / "bin" / name, run / "bin" / name)

    instances = []
    for s in args.sets:
        base = ROOT / s
        if not base.is_dir():
            print(f"missing instance set {s}", file=sys.stderr)
            return 1
        instances += sorted(str(p.relative_to(ROOT)) for p in base.rglob("*.cnf"))
    invalid = {i: v for i in instances if (v := check_valid(ROOT / i))}

    git = lambda *a: subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True).stdout
    meta = {
        "created": time.strftime("%Y-%m-%d %H:%M:%S"), "host": socket.gethostname(),
        "cpu": cpu_model(), "commit": git("rev-parse", "HEAD").strip(),
        "dirty_files": git("status", "--porcelain").splitlines(),
        "diff_sha256": hashlib.sha256(git("diff", "HEAD").encode()).hexdigest(),
        "lean": (ROOT / "lean-toolchain").read_text().strip(),
        "gcc": subprocess.run(["gcc", "--version"], capture_output=True, text=True).stdout.splitlines()[0],
        "binaries": {p.name: hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted((run / "bin").iterdir())},
        "limits": {"c_timeout": args.c_timeout, "factor": args.factor, "min": args.min, "max": args.max},
        "instances": {name: sum(set_name(i) == name for i in instances)
                      for name in sorted({set_name(i) for i in instances})},
        "invalid_inputs": invalid,   # ASSUMPTIONS.md section 1
    }
    (run / "meta.json").write_text(json.dumps(meta, indent=2) + "\n")
    tasks = [{"id": i, "set": set_name(i), "cost": (ROOT / i).stat().st_size} for i in instances]
    (run / "tasks.jsonl").write_text("".join(json.dumps(t) + "\n" for t in tasks))
    print(f"{len(instances)} instances ({len(instances) - len(invalid)} valid inputs, V1-V3); "
          f"C limit {args.c_timeout:g} s; Lean limit clamp({args.factor:g} x C, {args.min:g} s, "
          f"{args.max:g} s); frozen binaries in {run / 'bin'}")
    return 0


def shard(args: argparse.Namespace) -> int:
    run = RUNS / args.run
    limits = json.loads((run / "meta.json").read_text())["limits"]
    tasks = read_jsonl(run / "tasks.jsonl")
    tasks.sort(key=lambda t: (t["cost"], t["id"]))     # round-robin over size spreads the load
    mine = tasks[args.shard::args.shards]
    out = run / f"results-{args.shard}.jsonl"
    if out.exists():                                   # drop a line cut short by preemption
        text = out.read_text()
        if text and not text.endswith("\n"):
            out.write_text(text[: text.rfind("\n") + 1])
    done = {row["id"] for row in read_jsonl(out)}
    todo = [t for t in mine if t["id"] not in done]
    host, cpu, job = socket.gethostname(), cpu_model(), os.environ.get("SLURM_JOB_ID", "")
    print(f"[{time.strftime('%F %T')}] shard {args.shard}/{args.shards} on {host} ({cpu}), job {job}: "
          f"{len(mine)} instances, {len(done)} done, {len(todo)} to run, {args.workers} in parallel",
          flush=True)
    lock = threading.Lock()
    counter = [len(done)]

    def work(task: dict) -> None:
        cnf = ROOT / task["id"]
        runs = [run_solver(run / "bin", "c", cnf, limits["c_timeout"])]
        if runs[0]["status"] in SOLVED:
            limit = min(max(limits["factor"] * runs[0]["cpu"], limits["min"]), limits["max"])
            runs += [run_solver(run / "bin", s, cnf, limit) for s in LEAN]
        row = {"id": task["id"], "set": task["set"], "host": host, "cpu_model": cpu, "job": job,
               "finished": time.strftime("%F %T"), "runs": runs}
        with lock:
            with out.open("a") as handle:
                handle.write(json.dumps(row) + "\n")
                handle.flush()
                os.fsync(handle.fileno())
            counter[0] += 1
            summary = " ".join(f"{r['solver']}={r['status']}/{r['cpu']:.1f}s" for r in runs)
            print(f"[{time.strftime('%F %T')}] {counter[0]}/{len(mine)} {task['id']} {summary}", flush=True)

    with ThreadPoolExecutor(max_workers=args.workers) as pool:
        for future in [pool.submit(work, t) for t in todo]:
            future.result()
    print(f"[{time.strftime('%F %T')}] shard {args.shard} complete", flush=True)
    return 0


def status(args: argparse.Namespace) -> int:
    run = RUNS / args.run
    tasks = read_jsonl(run / "tasks.jsonl")
    results = all_results(run)
    print(f"{len(results)}/{len(tasks)} instances done")
    counts: dict[str, int] = {}
    for row in results.values():
        for r in row["runs"]:
            key = f"{r['solver']}:{r['status']}"
            counts[key] = counts.get(key, 0) + 1
    print("  ".join(f"{k}={v}" for k, v in sorted(counts.items())))
    return 0


def quantile(xs: list[float], q: float) -> float:
    xs = sorted(xs)
    return xs[min(len(xs) - 1, max(0, round(q * (len(xs) - 1))))]


def report(args: argparse.Namespace) -> int:
    run = RUNS / args.run
    meta = json.loads((run / "meta.json").read_text())
    invalid = meta.get("invalid_inputs", {})
    results = all_results(run)
    if not results:
        print("no results yet")
        return 0
    table = []
    for row in results.values():
        runs = {r["solver"]: r for r in row["runs"]}
        rec = {"set": row["set"], "instance": row["id"], "valid": row["id"] not in invalid,
               "host": row["host"], "cpu_model": row["cpu_model"]}
        for s in SOLVERS:
            r = runs.get(s, {})
            for field in ("status", "limit", "cpu", "wall", "conflicts", "maxrss_kb"):
                rec[f"{s}_{field}"] = r.get(field)
        rec["faithful_hashes_match"] = (runs["faithful"]["hashes"] == runs["c"]["hashes"]
                                        if "faithful" in runs else None)
        table.append(rec)
    with (run / "results.csv").open("w", newline="") as handle:
        writer = csv.DictWriter(handle, fieldnames=list(table[0]))
        writer.writeheader()
        writer.writerows(sorted(table, key=lambda r: r["instance"]))

    print(f"{len(table)}/{meta and sum(meta['instances'].values())} instances done; "
          f"{len(invalid)} invalid inputs (ASSUMPTIONS.md section 1); limits {meta['limits']}")
    for name in sorted({r["set"] for r in table}):
        rows = [r for r in table if r["set"] == name]
        c_ok = [r for r in rows if r["c_status"] in SOLVED]
        print(f"\n{name}: {len(rows)} instances; C: SAT {sum(r['c_status'] == 'SAT' for r in rows)}, "
              f"UNSAT {sum(r['c_status'] == 'UNSAT' for r in rows)}, "
              f"timeout {sum(r['c_status'] == 'TIMEOUT' for r in rows)}")
        for s in LEAN:
            fin = [r for r in c_ok if r[f"{s}_status"] in SOLVED]
            tout = sum(r[f"{s}_status"] == "TIMEOUT" for r in c_ok)
            agree = sum(r[f"{s}_conflicts"] == r["c_conflicts"] and r[f"{s}_status"] == r["c_status"] for r in fin)
            line = (f"  {s:<9} of {len(c_ok)} solved by C: finished {len(fin)}, timeout {tout}; "
                    f"same status+conflicts as C {agree}/{len(fin)}")
            if s == "faithful":
                line += f"; DB hashes match {sum(bool(r['faithful_hashes_match']) for r in fin)}/{len(fin)}"
            print(line)
            ratios = [r[f"{s}_cpu"] / r["c_cpu"] for r in fin if r["c_cpu"] >= args.min_c]
            if ratios:
                geo = math.exp(statistics.fmean(math.log(x) for x in ratios))
                print(f"            CPU time / C's (n={len(ratios)}, C >= {args.min_c:g} s): "
                      f"median {statistics.median(ratios):.1f}, geomean {geo:.1f}, "
                      f"p10 {quantile(ratios, 0.1):.1f}, p90 {quantile(ratios, 0.9):.1f}, "
                      f"max {max(ratios):.1f}; total {sum(r[f'{s}_cpu'] for r in fin) / 3600:.2f} h "
                      f"vs C {sum(r['c_cpu'] for r in fin) / 3600:.2f} h")
    models: dict[str, int] = {}
    for r in table:
        models[r["cpu_model"]] = models.get(r["cpu_model"], 0) + 1
    print("\nCPU models:", "; ".join(f"{m}: {n}" for m, n in sorted(models.items())))
    print(f"Per-instance table: {run / 'results.csv'}")
    return 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = parser.add_subparsers(dest="command", required=True)
    p = sub.add_parser("prepare")
    p.add_argument("run")
    p.add_argument("--sets", nargs="+", required=True, help="directories of .cnf files")
    p.add_argument("--c-timeout", type=float, default=5000.0, help="limit for C (s)")
    p.add_argument("--factor", type=float, default=100.0, help="Lean limit = factor x C's CPU time ...")
    p.add_argument("--min", type=float, default=600.0, help="... but at least this (s)")
    p.add_argument("--max", type=float, default=86400.0, help="... and at most this (s)")
    p.add_argument("--force", action="store_true")
    p = sub.add_parser("shard")
    p.add_argument("run")
    p.add_argument("shard", type=int)
    p.add_argument("shards", type=int)
    p.add_argument("--workers", type=int, default=int(os.environ.get("SLURM_CPUS_PER_TASK", "1")))
    p = sub.add_parser("status")
    p.add_argument("run")
    p = sub.add_parser("report")
    p.add_argument("run")
    p.add_argument("--min-c", type=float, default=0.1, help="ratios only where C took at least this (s)")
    args = parser.parse_args()
    return {"prepare": prepare, "shard": shard, "status": status, "report": report}[args.command](args)


if __name__ == "__main__":
    sys.exit(main())
