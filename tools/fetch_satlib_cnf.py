#!/usr/bin/env python3
"""Reproduce the 48 selected SATLIB fixtures with Python's standard library.

Downloads are cached in .agent-memory/satlib-cache. Archive SHA-256 pins ensure
that a source update cannot silently replace the corpus. Only explicitly named
regular archive members are read; archive paths are never extracted.

Examples:
    python tools/fetch_satlib_cnf.py
    python tools/fetch_satlib_cnf.py --check --offline
    python tools/fetch_satlib_cnf.py --metadata .agent-memory/satlib.json
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import tarfile
import urllib.request


ROOT = Path(__file__).resolve().parents[1]
BASE = "https://www.cs.ubc.ca/~hoos/SATLIB/Benchmarks/SAT/"
OVERVIEW = "https://www.cs.ubc.ca/~hoos/SATLIB/benchm.html"
DEFAULT_CACHE = ROOT / ".agent-memory" / "satlib-cache"
DEFAULT_OUTPUT = ROOT / "tests" / "cnf" / "satlib"

# Values pin the actual compressed download, including the archive's metadata.
ARCHIVES: dict[str, str] = {
    "RND3SAT/uf50-218.tar.gz":
        "a40862e52dfdce78620b037254579a02dbda8182d2879433658a4c15cb00327c",
    "RND3SAT/uuf50-218.tar.gz":
        "24cc9f492673e0f975fecc56b3a4d8ac21c385cc46205d83b7491a787f43e13d",
    "RND3SAT/uf100-430.tar.gz":
        "7f691acb8c45790ef8178dd01bb362cf50da608d478be9965599131f0a763e59",
    "RND3SAT/uuf100-430.tar.gz":
        "736c6f94fecae346a00501b197c482e146b1c6ab05fb6d2e4666e520b8e8508a",
    "RND3SAT/uf150-645.tar.gz":
        "4db94fd110acdae8ade1abd1fb0d484e88e4cff21e94ab7db96c7d29860e6080",
    "RND3SAT/uuf150-645.tar.gz":
        "287ff28ee3f6ab21627d3f758fc3d71d0dd7b64ab3a5bd0edcb663dc47666512",
    "GCP/flat100-239.tar.gz":
        "e3ec726e197ca40c4fe34db8f6caf35cbb9e8b3e6aa1d0bde9619111397e4482",
    "DIMACS/AIM/aim.tar.gz":
        "7e4e0076fdd840ed7bcc80c475509ed7726608b010cd3f181d503fe337473c85",
    "DIMACS/BF/bf.tar.gz":
        "8a100ce6753ec4da9068f3915e63b7b95719c468c46cd78b0c9140d7acda5b4d",
    "DIMACS/PHOLE/pigeon-hole.tar.gz":
        "092c4682d1a9d25451e8661af0afa3635943173b07164db495f4f0e11e806ee0",
}


def definitions() -> list[dict[str, str]]:
    """Return the exact selection and source-backed expected statuses."""
    result: list[dict[str, str]] = []

    def add(archive: str, member: str, expected: str, family: str, tier: str,
            description: str, status_basis: str = OVERVIEW) -> None:
        result.append({
            "path": "satlib/" + Path(member).name,
            "expected": expected,
            "family": family,
            "tier": tier,
            "description": description,
            "origin": "satlib",
            "source_url": BASE + archive,
            "source_member": member,
            "archive_sha256": ARCHIVES[archive],
            "status_basis": status_basis,
        })

    for size, count, indices in (
        (50, 218, (1, 2, 3, 10, 25, 100, 500, 1000)),
        (100, 430, (1, 10, 100, 1000)),
        (150, 645, (1, 10, 50, 100)),
    ):
        for prefix, expected in (("uf", "SAT"), ("uuf", "UNSAT")):
            archive = f"RND3SAT/{prefix}{size}-{count}.tar.gz"
            if prefix == "uuf":
                directory = f"UUF{size}.{count}.{100 if size == 150 else 1000}/"
            elif size == 150:
                directory = "ai/hoos/Research/SAT/Formulae/UF150.645.100/"
            else:
                directory = ""
            for index in indices:
                filename = f"{prefix}{size}-0{index}.cnf"
                add(archive, directory + filename, expected, "random-3sat",
                    "stress" if size == 150 else "regression",
                    f"Unforced filtered phase-transition random 3-SAT; "
                    f"{size} variables, {count} clauses, source instance {index}.")

    for index in (1, 10, 50, 100):
        add("GCP/flat100-239.tar.gz", f"flat100-{index}.cnf", "SAT",
            "graph-coloring", "regression",
            f"Three-colorable flat graph with 100 vertices and 239 edges; "
            f"source instance {index}.")

    aim = (
        (50, "1_6", "no"), (100, "1_6", "no"),
        (100, "2_0", "no"), (200, "2_0", "no"),
        (50, "1_6", "yes1"), (100, "2_0", "yes1"),
        (200, "3_4", "yes1"), (200, "6_0", "yes1"),
    )
    for size, ratio, kind in aim:
        add("DIMACS/AIM/aim.tar.gz", f"aim-{size}-{ratio}-{kind}-1.cnf",
            "SAT" if kind == "yes1" else "UNSAT", "aim", "regression",
            f"AIM controlled-status 3-SAT; {size} variables, "
            f"clause/variable ratio {ratio.replace('_', '.')}; "
            + ("unique satisfying assignment." if kind == "yes1"
               else "unsatisfiable at a low clause/variable ratio."),
            BASE + "DIMACS/AIM/descr.html")

    for holes in (6, 7):
        add("DIMACS/PHOLE/pigeon-hole.tar.gz", f"hole{holes}.cnf", "UNSAT",
            "pigeonhole", "stress",
            f"Place {holes + 1} pigeons in {holes} holes with no collisions.",
            BASE + "DIMACS/PHOLE/descr.html")

    for filename in ("bf0432-007.cnf", "bf1355-075.cnf"):
        add("DIMACS/BF/bf.tar.gz", filename, "UNSAT", "circuit-fault",
            "stress", "Nemesis circuit bridge-fault analysis; large variable "
            "count and mixed clause lengths from one through six.",
            BASE + "DIMACS/BF/descr.html")

    assert len(result) == 48
    assert len({entry["path"] for entry in result}) == 48
    return sorted(result, key=lambda entry: entry["path"])


def sha256(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def cached_archive(archive: str, cache_dir: Path, *, offline: bool) -> Path:
    path = cache_dir / Path(archive).name
    if not path.exists():
        if offline:
            raise FileNotFoundError(f"Archive is not cached: {path}")
        cache_dir.mkdir(parents=True, exist_ok=True)
        request = urllib.request.Request(
            BASE + archive, headers={"User-Agent": "microsat-lean-fixtures/1"})
        with urllib.request.urlopen(request, timeout=90) as response:
            data = response.read(32 * 1024 * 1024 + 1)
        if len(data) > 32 * 1024 * 1024:
            raise ValueError(f"Archive exceeds download size limit: {archive}")
        if sha256(data) != ARCHIVES[archive]:
            raise ValueError(f"Downloaded archive SHA-256 mismatch: {archive}")
        partial = path.with_suffix(path.suffix + ".part")
        partial.write_bytes(data)
        partial.replace(path)
    if sha256(path.read_bytes()) != ARCHIVES[archive]:
        raise ValueError(f"Cached archive SHA-256 mismatch: {path}")
    return path


def normalize_member(raw: bytes) -> tuple[bytes, list[str]]:
    """Remove only SATLIB's exact legacy random-CNF end marker."""
    suffix = b"%\n0\n\n"
    if raw.endswith(suffix):
        # The preceding clause already ends in LF. Keeping that LF preserves
        # all source comments, the header, literals, and clause terminators.
        return raw[:-len(suffix)], [
            "Removed exact trailing legacy SATLIB end marker bytes %\\n0\\n\\n."
        ]
    return raw, []


def collect(*, check: bool = False, offline: bool = False,
            cache_dir: Path = DEFAULT_CACHE,
            output_dir: Path = DEFAULT_OUTPUT) -> list[dict]:
    """Write or check selected fixtures and return reproducible metadata.

    Metadata generation has no dependency on private working-memory files.
    --check compares every selected fixture byte-for-byte with its pinned
    source after the documented normalization. Missing files are failures.
    """
    entries = definitions()
    for archive in ARCHIVES:
        selected = [entry for entry in entries
                    if entry["source_url"] == BASE + archive]
        path = cached_archive(archive, cache_dir, offline=offline)
        with tarfile.open(path, mode="r:gz") as source:
            for entry in selected:
                member = source.getmember(entry["source_member"])
                if not member.isfile():
                    raise ValueError(f"Not a regular archive member: {member.name}")
                if member.size > 4 * 1024 * 1024:
                    raise ValueError(f"Archive member too large: {member.name}")
                stream = source.extractfile(member)
                if stream is None:
                    raise ValueError(f"Cannot read archive member: {member.name}")
                with stream:
                    raw = stream.read()
                data, transformations = normalize_member(raw)
                target = output_dir / Path(entry["path"]).name
                if check:
                    if not target.is_file() or target.read_bytes() != data:
                        raise ValueError(f"Fixture does not match pinned source: {target}")
                else:
                    output_dir.mkdir(parents=True, exist_ok=True)
                    target.write_bytes(data)
                entry.update({
                    "source_sha256": sha256(raw),
                    "sha256": sha256(data),
                    "transformations": transformations,
                    "source_rights": "Public benchmark download; no explicit "
                                     "license stated on inspected SATLIB pages. "
                                     "Original source comments retained.",
                })
    return entries


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true",
                        help="Compare fixture bytes without modifying fixtures.")
    parser.add_argument("--offline", action="store_true",
                        help="Require all pinned archives in the private cache.")
    parser.add_argument("--metadata", type=Path,
                        help="Optionally write collected metadata as JSON.")
    args = parser.parse_args()
    entries = collect(check=args.check, offline=args.offline)
    if args.metadata:
        args.metadata.parent.mkdir(parents=True, exist_ok=True)
        args.metadata.write_text(json.dumps(entries, indent=2) + "\n",
                                 encoding="utf-8")
    action = "Verified" if args.check else "Wrote"
    print(f"{action} {len(entries)} SATLIB CNF fixtures from {len(ARCHIVES)} "
          "SHA-256-pinned archives.")


if __name__ == "__main__":
    main()
