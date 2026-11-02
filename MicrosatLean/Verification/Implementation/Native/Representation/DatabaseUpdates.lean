import MicrosatLean.Verification.Implementation.Native.Representation.Database
import MicrosatLean.Verification.Implementation.Native.Representation.Restart
import MicrosatLean.Verification.Implementation.Native.Representation.Heuristic

namespace MicrosatLean.Verification.Implementation.Native.Representation

open CDCL

theorem PackedClause.frame {before after : State} {id : Nat} {lits : Array Lit}
    (packed : PackedClause before id lits) (arena : after.arena = before.arena)
    (variables : after.nVars = before.nVars) : PackedClause after id lits := by
  refine ⟨packed.startLower, ?_, ?_, ?_, ?_⟩
  · simpa only [arena] using packed.endBound
  · intro i bound
    simpa only [State.db, arena] using packed.literals i bound
  · simpa only [State.db, arena] using packed.terminator
  · simpa only [variables] using packed.wellFormed

theorem DatabaseFrom.frame {before after : State} {start : Nat} {entries : List StoredClause}
    (layout : DatabaseFrom before start entries) (arena : after.arena = before.arena)
    (variables : after.nVars = before.nVars) : DatabaseFrom after start entries := by
  induction entries generalizing start with
  | nil => simpa only [DatabaseFrom, arena] using layout
  | cons entry rest ih =>
    exact ⟨layout.1, layout.2.1.frame arena variables, ih layout.2.2⟩

theorem Database.frame {before after : State} {original learned : List StoredClause}
    (database : Database before original learned) (arena : after.arena = before.arena)
    (variables : after.nVars = before.nVars) (fixed : after.fixed = before.fixed)
    (count : after.nLemmas = before.nLemmas) : Database after original learned :=
  ⟨database.layout.frame arena variables, fixed.trans database.fixed,
    count.trans database.learnedCount⟩

theorem Database.setMark {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (lit value : Nat) :
    Database (s.setMark lit value) original learned := database.frame rfl rfl rfl rfl

theorem Database.assign {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (id : Nat) (root : Bool) :
    Database (s.assign id root) original learned := database.frame rfl rfl rfl rfl

theorem Database.decide {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (var : Nat) :
    Database (s.decide var) original learned := database.frame rfl rfl rfl rfl

theorem Database.restart {s : State} {original learned : List StoredClause}
    (database : Database s original learned) : Database s.restart original learned := by
  apply database.frame restart_arena restart_nVars restart_fixed
  simpa using congrArg State.nLemmas (restart_frame s).restore

theorem Database.bump {s : State} {original learned : List StoredClause}
    (database : Database s original learned) (lit : Lit) : Database (s.bump lit) original learned := by
  apply database.frame bump_arena bump_nVars
  · simpa using congrArg State.fixed (bump_frame s lit).restore
  · simpa using congrArg State.nLemmas (bump_frame s lit).restore

end MicrosatLean.Verification.Implementation.Native.Representation
