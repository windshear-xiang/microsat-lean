/* Reference build of upstream/microsat.c for differential testing against the
   faithful Lean port (FaithfulMain.lean). The solver is included verbatim; only
   main is replaced, to also print the model and a hash of DB[0..mem_used) after
   parse and at the end. --dump prints every cell as well.

   Build: gcc -O2 -std=gnu99 -w tools/microsat_ref.c -o microsat-ref
   (-std=gnu99 because C23 makes `false` a keyword.) */
#include <stdint.h>
#include <string.h>

#define main microsat_upstream_main
#include "../upstream/microsat.c"
#undef main

static void report (struct solver* S, const char* tag, int dump) {
  uint64_t h = 14695981039346656037ULL;   /* FNV-1a over 32-bit cells */
  int i;
  for (i = 0; i < S->mem_used; i++) { h ^= (uint32_t) S->DB[i]; h *= 1099511628211ULL; }
  printf ("c db %s mem_used: %i hash: %llu\n", tag, S->mem_used, (unsigned long long) h);
  if (dump) for (i = 0; i < S->mem_used; i++) printf ("d %s %i %i\n", tag, i, S->DB[i]); }

int main (int argc, char** argv) {
  struct solver S;
  char* path = NULL; int dump = 0, i, result;
  for (i = 1; i < argc; i++) {
    if (!strcmp (argv[i], "--dump")) dump = 1;
    else if (!path) path = argv[i]; }
  if (!path) { printf ("no input file provided\n"); exit (0); }
  result = parse (&S, path);
  report (&S, "parse", dump);
  if (result != UNSAT) result = solve (&S);
  printf (result == UNSAT ? "s UNSATISFIABLE\n" : "s SATISFIABLE\n");
  if (result == SAT) {
    printf ("v");
    for (i = 1; i <= S.nVars; i++) printf (" %i", S.model[i] ? i : -i);
    printf (" 0\n"); }
  printf ("c statistics of %s: mem: %i conflicts: %i max_lemmas: %i\n", path, S.mem_used, S.nConflicts, S.maxLemmas);
  report (&S, "final", dump);
  return 0; }
