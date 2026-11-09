# Assumptions for verifying `microsat.c`

Everything proved about the faithful port (`MicrosatLean/Faithful/`) holds under
the assumptions in this file and no others. Section 1 is about the input; section 2
is about the execution model.

## Rule for adding or changing an assumption

1. Add an entry here **before** any proof uses it: an ID, the exact condition, why
   it is needed (a concrete input or scenario where `microsat.c` misbehaves without
   it), where it is encoded in Lean, and the date.
2. An input condition is a new field of `Input.Valid`
   (`MicrosatLean/Faithful/Valid.lean`), added in the same change. Theorems take
   `input.Valid` as their only hypothesis about the input; no ad-hoc hypotheses.
3. Never weaken or strengthen an entry silently: record every change in the log at
   the end of this file.

## 1. Valid input (`Input.Valid`)

An input is the DIMACS header `p cnf nVars nClauses` and the clauses that follow.
It is **valid** when all of the following hold.

| ID | Condition | Lean field | Added |
|---|---|---|---|
| V1 | Well-formed DIMACS: `nVars ≥ 0`; exactly `nClauses` clauses, each ended by `0`; every literal is nonzero and `abs lit ≤ nVars` | `nVars_nonneg`, `nClauses_eq`, `lit_range` | 2026-11-08 |
| V2 | No literal occurs twice in one clause | `no_repeated_lit` | 2026-11-08 |
| V3 | Every clause has at most `nVars` literals | `clause_size_le` | 2026-11-08 |

V2 and V3 are independent: a clause with both `x` and `-x` for many variables
satisfies V2 but can have up to `2·nVars` literals, and `1 1` satisfies V3 when
`nVars ≥ 2`. Both are cheap for any producer of CNF to guarantee (remove repeated
literals; a clause with more than `nVars` literals must repeat a variable).

**Why V1.** C does not check literal bounds. With `abs lit > nVars`, `false[lit]`,
`reason[abs(lit)]`, `model[abs(lit)]` and `first[lit]` are read and written outside
their regions of `DB`. Fuzzing 200 small files with such literals made C hang on 39.
The existing Lean DIMACS reader rejects these files.

**Why V3 (and V2).** `buffer` has `nVars` cells (C:196) and `parse` stores each
literal with `S->buffer[size++] = lit` (C:241) without a bound. A longer clause
overwrites `reason[]` and then `falseStack[]` (the trail). Smallest example, valid
DIMACS, on which C and the faithful port both loop forever:

```
p cnf 1 2
1 0
1 1 1 1 0
```

The clause `1 1 1 1` is copied into `DB` cells 6–9 (`buffer[0]`, `reason[0..1]`,
`falseStack[0]`), so the trail says literal `1` is false while `false[1] = 0`.
`propagate` then picks `1` as the "non-false" replacement for a watch of `1`, moves
the watch onto the list it is scanning, and the loop at C:137 never ends.
(Clauses that exceed `nVars` only through complementary pairs overflow into
`reason[]` alone; 1268 fuzzed files of that kind did not hang, but V3 excludes them
so that proofs never reason about the overflow.)

## 2. Execution model

| ID | Assumption | Where it shows up |
|---|---|---|
| E1 | `DB` starts zeroed (a fresh `malloc` of `mem_max` cells comes from zero pages). C relies on it, e.g. C:133 reads `reason[abs(*processed)]` before any write, and C:204. | `solver.ld` returns 0 beyond the physical array; `solver.st` extends it with zeros |
| E2 | Integers do not overflow: `CInt` is `Int` (unbounded) while C's `int` is 32-bit. To be discharged later by switching `CInt` to `Int32` and bounding values (e.g. `fast += lbd << 15`). | `abbrev CInt` in `MicrosatLean/Faithful/Memory.lean` |
| E3 | Enough memory: the theorems hold when `mem_max` (C's constant `1 << 30`) is at least an explicit bound computed from the input (`memoryBound`, roughly the input clauses plus `3^nVars` lemmas). Below that bound C may print `c out of memory` and exit (the Lean port panics); the theorems say nothing about that case. | `initCDCL`/`parse` take `mem_max` as a parameter defaulting to `1 <<< 30`; `memoryBound` in `MicrosatLean/Faithful/Verification/Invariant.lean` |
| E4 | Character-level DIMACS reading (`fscanf("%i")`, comments, header search in C:216–233) is outside the model. `parse` starts from `Input.tokens` of a valid input. | `parse`, `FaithfulMain.lean` |

## Change log

- 2026-11-08: V1–V3 introduced (input validity decided by Henry: no repeated
  literals, at most `nVars` literals per clause, on top of well-formed DIMACS).
  E1–E4 carried over from `FAITHFUL_PORT_HANDOFF.md`.
- 2026-11-08: E3 made precise (decided by Henry): `mem_max` is a parameter of
  `initCDCL`/`parse` (default `1 <<< 30`, as in C), and the theorems assume
  `memoryBound input ≤ mem_max` instead of treating out of memory as an outcome.
- 2026-11-08: no new assumption while proving `parse`, `step`, `restart`, `reduceDB`,
  the decision and `propagate`. The facts added to the loop invariant (`false[0] = 0`,
  non-empty input records, same-level reason literals, record orientation, `Mode`) are
  all established by `parse` from V1–V3; V3 also bounds the literal scan of an input
  clause (`Core.record_length_le`).
- 2026-11-08: no new assumption while proving `analyze`, `implied` and `bump`, which
  closed the last gap: the whole development is `sorry`-free, and the main theorems
  (`Verification/Main.lean`) depend only on `propext`, `Classical.choice` and
  `Quot.sound`, under `input.Valid` (V1–V3) and E3.
