import MicrosatLean.Faithful.Memory
import MicrosatLean.Faithful.Microsat
import MicrosatLean.Faithful.Valid

/-!
Faithful port of `upstream/microsat.c`: one `DB` array laid out exactly as C lays
it out, C's pointers as offsets into it, and C's functions, names and loops.
See `FAITHFUL_PORT_HANDOFF.md`. The executable is `FaithfulMain.lean`
(`lake exe microsat-faithful`); `tools/diff_faithful.py` compares it with C.
-/
