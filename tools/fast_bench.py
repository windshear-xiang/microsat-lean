#!/usr/bin/env python3
"""Quick timing of the fast Lean port against upstream C on a fixed subset.

For each instance, runs C (`microsat-ref`) and the fast port (`microsat-fast`) one
after the other, checks that their whole outputs are identical (status, model,
statistics, DB hashes), and reports CPU times and the ratio. The default subset is 14
UNSAT agile instances where C takes 0.3-2.4 s plus one SAT instance (C: about 21 s);
`--sat` adds three longer SAT instances.

Usage: python3 -B tools/fast_bench.py [--sat] [--faithful] [--bin NAME]
"""

from __future__ import annotations

import argparse
import math
import os
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
BIN = ROOT / ".lake" / "build" / "bin"
AGILE = ROOT / "bench" / "agile_2016_sample100"

QUICK = """49d4fb0953101e60f313e02a1f798201 974a99df77a6233499b6af28939ba823
b35f855c945b148c47781e21ef166f64 3510c53d2fb2536b9b83a5180694ad3e 22ce40fa38afbded33c97a7d9dfa5c74
693e3525b177bd3e0daf0eeba79f9617 9acb213a150c02cdd2131bd828e5d38a f7f41dcc4b4522a57da26826426b2b33
01d7029fd605b0f8aa31ce2260b9f874 c9fa883d0076cc131780d5cd67448008 b1160f4177e44acc9e06405086aac8c0
b205771b224dcb73e48ee717cad6896d eeff7301f523418f8d8320904767c8ec cb3a2be54cf83d68862a7cf01aa2445f
aee20862""".split()
SAT = "ff852713 d9caf7ae a6d5c1d5".split()


def resolve(prefix: str) -> Path:
    matches = sorted(AGILE.glob(prefix + "*.cnf"))
    if len(matches) != 1:
        sys.exit(f"instance prefix {prefix}: {len(matches)} matches")
    return matches[0]


def timed(cmd: list[str]) -> tuple[float, str]:
    with tempfile.TemporaryFile() as out:
        proc = subprocess.Popen(cmd, stdout=out, stderr=subprocess.STDOUT)
        _, status, usage = os.wait4(proc.pid, 0)
        out.seek(0)
        return usage.ru_utime + usage.ru_stime, out.read().decode()


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__,
                                     formatter_class=argparse.RawDescriptionHelpFormatter)
    parser.add_argument("--sat", action="store_true", help="add three longer SAT instances")
    parser.add_argument("--faithful", action="store_true", help="also time microsat-faithful")
    parser.add_argument("--bin", default="microsat-fast")
    args = parser.parse_args()

    names = QUICK + (SAT if args.sat else [])
    files = [resolve(n) for n in names]
    solvers = [("C", "microsat-ref"), ("fast", args.bin)] + (
        [("faithful", "microsat-faithful")] if args.faithful else [])
    totals = {k: 0.0 for k, _ in solvers}
    logs = {k: 0.0 for k, _ in solvers if k != "C"}
    bad = 0
    print(f"{'instance':10} {'status':6} " + " ".join(f"{k:>9}" for k, _ in solvers) +
          " " + " ".join(f"{k + '/C':>11}" for k, _ in solvers if k != "C"))
    for f in files:
        times, outs = {}, {}
        for k, b in solvers:
            times[k], outs[k] = timed([str(BIN / b), str(f)])
            totals[k] += times[k]
        status = "SAT" if "s SATISFIABLE" in outs["C"] else "UNSAT"
        same = all(outs[k] == outs["C"] for k, _ in solvers)
        bad += not same
        ratios = []
        for k, _ in solvers:
            if k == "C":
                continue
            ratio = times[k] / max(times["C"], 1e-3)
            logs[k] += math.log(ratio)
            ratios.append(f"{ratio:11.2f}")
        print(f"{f.name[:8]:10} {status:6} " + " ".join(f"{times[k]:9.2f}" for k, _ in solvers) +
              " " + " ".join(ratios) + ("" if same else "   OUTPUT DIFFERS"))
    print(f"{'total':10} {'':6} " + " ".join(f"{totals[k]:9.2f}" for k, _ in solvers) + " " +
          " ".join(f"{totals[k] / totals['C']:11.2f}" for k, _ in solvers if k != "C"))
    print("geomean ratio: " + ", ".join(f"{k} {math.exp(logs[k] / len(files)):.2f}" for k in logs))
    print("all outputs identical to C" if not bad else f"{bad} outputs differ from C")
    return 1 if bad else 0


if __name__ == "__main__":
    sys.exit(main())
