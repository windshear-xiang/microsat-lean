# microsat-lean

A Lean port and formal-verification project for Microsat.

The [DIMACS CNF test corpus](tests/cnf/README.md) contains 128 boundary,
structured and SATLIB fixtures with expected SAT/UNSAT results. Validate it with:

```sh
python -B tools/check_cnf_corpus.py
```
