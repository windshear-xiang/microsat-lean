#!/usr/bin/env python3
"""Generate legal DIMACS CNF boundary fixtures with byte-exact layout variants."""

from __future__ import annotations

import argparse
from dataclasses import dataclass
import json
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]


@dataclass(frozen=True)
class Fixture:
    name: str
    variables: int
    clauses: tuple[tuple[int, ...], ...]
    expected: str
    description: str
    reason: str
    layout: bytes | None = None

    def content(self) -> bytes:
        if self.layout is not None:
            return self.layout
        lines = [f"c {self.description}", f"p cnf {self.variables} {len(self.clauses)}"]
        lines.extend(" ".join(str(literal) for literal in (*clause, 0)) for clause in self.clauses)
        return ("\n".join(lines) + "\n").encode("ascii")

    def metadata(self) -> dict[str, str]:
        return {
            "path": f"edge/{self.name}.cnf",
            "expected": self.expected,
            "family": "edge",
            "tier": "smoke",
            "description": self.description,
            "origin": "generated",
            "generator": f"python tools/generate_edge_cnf.py --case {self.name}",
            "status_basis": self.reason,
        }


def fixtures() -> list[Fixture]:
    """Return deterministic formulas, preserving the syntax of custom layouts."""
    cases: list[Fixture] = []

    def add(
        name: str,
        variables: int,
        clauses: list[list[int]],
        expected: str,
        description: str,
        reason: str,
        layout: bytes | None = None,
    ) -> None:
        cases.append(Fixture(name, variables, tuple(map(tuple, clauses)), expected, description, reason, layout))

    add("01-empty-zero-variables", 0, [], "SAT", "Empty formula with zero variables.",
        "The empty conjunction is true.", b"p cnf 0 0\n")
    add("02-empty-unused-variables", 4, [], "SAT", "Empty formula with four unused declared variables.",
        "The empty conjunction is true for every assignment.")
    add("03-empty-clause-zero-variables", 0, [[]], "UNSAT", "One empty clause with zero variables.",
        "An empty disjunction is false.")
    add("04-empty-clause-with-variables", 3, [[]], "UNSAT", "One empty clause with unused declared variables.",
        "The empty clause is false independently of all declared variables.")
    add("05-positive-unit", 1, [[1]], "SAT", "A single positive unit clause.",
        "Setting variable 1 to true satisfies the clause.")
    add("06-negative-unit", 1, [[-1]], "SAT", "A single negative unit clause.",
        "Setting variable 1 to false satisfies the clause.")
    add("07-contradicting-units", 1, [[1], [-1]], "UNSAT", "Contradicting positive and negative units.",
        "The two units require opposite values of variable 1.")
    add("08-duplicate-literals", 2, [[1, 1, 1], [-1, 2, 2]], "SAT", "Repeated literals within clauses.",
        "Setting variables 1 and 2 to true satisfies both clauses.")
    add("09-tautological-clause", 1, [[1, -1]], "SAT", "One tautological clause.",
        "The clause contains a literal and its negation, so every assignment satisfies it.")
    add("10-duplicate-clauses", 2, [[1, 2], [1, 2], [-1, 2]], "SAT", "Repeated clauses with an additional binary clause.",
        "Setting variable 2 to true satisfies all clauses.")
    add("11-duplicate-empty-clauses", 0, [[], []], "UNSAT", "Repeated empty clauses with zero variables.",
        "Either empty clause alone is false.")
    add("12-tautology-with-conflicting-units", 2, [[1, -1], [2], [-2]], "UNSAT", "A tautology alongside contradicting units.",
        "The tautology does not resolve the opposing requirements on variable 2.")
    add("13-pure-positive-literals", 3, [[1, 2], [1, 3], [2, 3]], "SAT", "All variables occur only positively.",
        "Setting every variable to true satisfies all clauses.")
    add("14-pure-negative-literals", 3, [[-1, -2], [-1, -3], [-2, -3]], "SAT", "All variables occur only negatively.",
        "Setting every variable to false satisfies all clauses.")
    add("15-sparse-maximum-variable", 1024, [[1024], [-1, 1024]], "SAT", "Sparse numbering reaches declared variable 1024.",
        "Setting variable 1024 to true satisfies both clauses; other variables are unconstrained.")
    add("16-sparse-maximum-conflict", 1024, [[1024], [-1024]], "UNSAT", "Contradicting units at the declared maximum variable.",
        "The units require opposite values of variable 1024.")
    add("17-sparse-interior-variables", 1024, [[2, 513], [-513, 1024], [-2, -1024]], "SAT", "Sparse interior and maximum variables leave large numbering gaps.",
        "Variable 2 true, variable 513 false, and variable 1024 false satisfy all clauses.")
    add("18-long-clause-last-literal", 128, [list(range(1, 129))] + [[-i] for i in range(1, 128)], "SAT",
        "A 128-literal clause is satisfied only at its last literal after unit propagation.",
        "Variables 1 through 127 are false and variable 128 is true.")
    add("19-long-clause-conflict", 128, [list(range(1, 129))] + [[-i] for i in range(1, 129)], "UNSAT",
        "A 128-literal clause conflicts after every literal is forced false.",
        "All literals of the long clause are falsified by negative units.")
    chain = [[1]] + [[-i, i + 1] for i in range(1, 32)]
    add("20-unit-propagation-chain", 32, chain, "SAT", "A positive unit propagates through 31 binary implications.",
        "Setting all variables to true satisfies the initial unit and every implication.")
    add("21-unit-propagation-late-conflict", 32, chain + [[-32]], "UNSAT", "A binary implication chain ends in a contradicting unit.",
        "The initial unit and implications force variable 32 true, contradicting its negative unit.")
    add("22-watch-movement-satisfiable", 16, [list(range(1, 17))] + [[-i] for i in range(1, 15)] + [[16]], "SAT",
        "A long clause has its first fourteen literals forced false and its last true.",
        "Variable 16 true satisfies the long clause; variables 1 through 14 are false.")
    add("23-watch-movement-late-conflict", 16, [list(range(1, 17))] + [[-i] for i in range(1, 17)], "UNSAT",
        "A long clause is exhausted by sixteen negative unit assignments.",
        "Every literal of the long clause is forced false.")
    add("24-binary-implication-cycle", 3, [[-1, 2], [-2, 3], [-3, 1], [1]], "SAT",
        "A binary implication cycle is seeded by a positive unit.",
        "Setting all three variables to true satisfies the cycle and the unit.")
    add("25-all-binary-polarities", 2, [[1, 2], [1, -2], [-1, 2], [-1, -2]], "UNSAT",
        "All four binary clauses over two variables exclude every assignment.",
        "For each assignment, the clause containing both falsified literals is false.")
    add("26-comment-lines-before-header", 2, [[1, -2], [2]], "SAT", "Multiple comment lines precede the DIMACS header.",
        "Setting both variables to true satisfies the two clauses.",
        b"c Legal DIMACS comment before the header.\nc A second comment; tokens such as 0 are ignored here.\nc\np cnf 2 2\n1 -2 0\n2 0\n")
    add("27-blank-lines-and-tabs", 3, [[1, -2], [2, 3], [-3, 1]], "SAT", "Blank lines, leading spaces, and tabs separate legal tokens.",
        "Variables 1 and 2 true and variable 3 false satisfy all clauses.",
        b"\n\nc Whitespace layout fixture.\n\np\tcnf\t3\t3 \n\n\t1\t-2\t0\n 2  3 0 \n\n-3\t1\t0\n")
    add("28-clause-spans-lines", 3, [[1, 2, -3], [-1, 3]], "SAT", "Both clauses span physical lines before their zero terminators.",
        "Variables 1 and 3 true satisfy the first clause by 1 and the second by 3.",
        b"c A clause ends at zero rather than at a newline.\np cnf 3 2\n1\n2 -3\n0\n-1\n3\n0\n")
    add("29-unit-terminators-on-separate-lines", 1, [[1], [-1]], "UNSAT", "Unit literals and their zero terminators occupy separate lines.",
        "The two unit clauses require opposite values of variable 1.",
        b"p cnf 1 2\n1\n0\n-1\n0\n")
    add("30-multiple-clauses-one-line", 2, [[1, 2], [-1, 2], [1, -2]], "SAT", "Three complete clauses share a single physical line.",
        "Setting both variables to true satisfies all three clauses.",
        b"p cnf 2 3\n1 2 0 -1 2 0 1 -2 0\n")
    add("31-no-final-newline", 1, [[1], [-1]], "UNSAT", "The last clause terminator is followed immediately by end of file.",
        "The two unit clauses require opposite values of variable 1.",
        b"c No trailing newline is required.\np cnf 1 2\n1 0\n-1 0")
    add("32-crlf-line-endings", 2, [[1, 2], [-1, -2]], "SAT", "Every physical line uses CRLF line endings.",
        "Variable 1 true and variable 2 false satisfy both clauses.",
        b"c CRLF layout fixture.\r\np cnf 2 2\r\n1 2 0\r\n-1 -2 0\r\n")

    assert len(cases) == 32
    assert len({case.name for case in cases}) == len(cases)
    assert len({case.content() for case in cases}) == len(cases)
    for case in cases:
        validate_layout(case)
    return cases


def validate_layout(case: Fixture) -> None:
    """Check that byte-exact variants encode the same formula as their metadata."""
    lines = [line for line in case.content().decode("ascii").splitlines() if line.strip() and not line.startswith("c")]
    assert lines[0].split() == ["p", "cnf", str(case.variables), str(len(case.clauses))], case.name
    parsed: list[tuple[int, ...]] = []
    clause: list[int] = []
    for token in " ".join(lines[1:]).split():
        literal = int(token)
        if literal == 0:
            parsed.append(tuple(clause))
            clause = []
        else:
            assert abs(literal) <= case.variables, case.name
            clause.append(literal)
    assert not clause and tuple(parsed) == case.clauses, case.name


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output-dir", type=Path, default=ROOT / "tests" / "cnf" / "edge")
    parser.add_argument("--case", action="append", help="Generate only the named fixture (repeatable).")
    parser.add_argument("--check", action="store_true", help="Compare existing files without rewriting them.")
    parser.add_argument("--metadata", type=Path, help="Optionally write generated manifest entries as JSON.")
    args = parser.parse_args()
    cases = fixtures()
    if args.case:
        names = set(args.case)
        unknown = names - {case.name for case in cases}
        if unknown:
            parser.error("unknown cases: " + ", ".join(sorted(unknown)))
        cases = [case for case in cases if case.name in names]
    if not args.check:
        args.output_dir.mkdir(parents=True, exist_ok=True)
    for case in cases:
        path = args.output_dir / f"{case.name}.cnf"
        if args.check:
            if not path.is_file() or path.read_bytes() != case.content():
                parser.exit(1, f"Fixture is missing or differs: {path}\n")
        else:
            path.write_bytes(case.content())
    if args.metadata is not None:
        args.metadata.parent.mkdir(parents=True, exist_ok=True)
        args.metadata.write_text(json.dumps([case.metadata() for case in cases], indent=2) + "\n", encoding="utf-8")
    action = "Checked" if args.check else "Generated"
    print(f"{action} {len(cases)} edge fixtures in {args.output_dir}")


if __name__ == "__main__":
    main()
