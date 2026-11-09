import MicrosatLean.Fast.Verification.Decide
import MicrosatLean.Faithful.Verification.Step

/-!
# Shared definitions of the fast port's proof

The fast state `s` (with its layout `L`) is related to the faithful state
`abs L s (memoryBound input) fa sl`:

* `memoryBound input` as the faithful `mem_max`, so that the faithful invariant's memory
  assumption (`Core.memory`) holds. The fast port has its own check against `memMax`,
  and running out is an outcome (`OOM`).
* `fa`, `sl` are free: the faithful invariants do not read `fast`/`slow`
  (`Settled.withStats`), and `Int32` wraps where the faithful `Int` does not.

`Bounds` holds the facts about a fast state that rule out `Int32` overflow and that the
faithful invariant does not give. Every component theorem keeps it.
-/

namespace MicrosatLean.Fast.Verification

open MicrosatLean.Faithful (solver Input)
open MicrosatLean.Faithful.Verification
open MicrosatLean.Fast

/-- The bounds of a fast state that the faithful invariant does not give. -/
structure Bounds (L : Lay) (s : St) : Prop where
  size : s.db.size ≤ 2 ^ 31
  nVars : NOk L.nVars
  memUsed : s.memUsed.toInt ≤ 2 ^ 30
  maxLemmas : s.maxLemmas.toInt ≤ 2 ^ 30

/-- C:156–158 after `analyze` returned the lemma at `r.2`: assign its first literal, with
the `forced` flag set when the lemma is a unit. `propLoop` continues from this state. -/
def conflictNext (L : Lay) (r : St × Cell) : St :=
  { r.1 with
    db := assign L r.1.db r.1.assigned r.2 (ld r.1.db (r.2 + 1) == 0)
    assigned := r.1.assigned + 1 }

end MicrosatLean.Fast.Verification
