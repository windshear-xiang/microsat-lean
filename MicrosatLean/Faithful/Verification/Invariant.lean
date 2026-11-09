import MicrosatLean.Faithful.Verification.Order
import MicrosatLean.Faithful.Verification.Frame

/-!
# The loop invariant and the termination rank

`Inv input S decision` holds at the top of every iteration of `solve`'s main loop
(C:162). `rank` decreases at every iteration (`step_decreases` in `Step.lean`).
-/

namespace MicrosatLean.Faithful.Verification

/-- There are at most `3^n` clauses over `n` variables that use each variable at most
once, so at most `3^n` distinct lemmas. Bounds `nLemmas` for the rank and memory. -/
def clauseBound (n : CInt) : Nat := 3 ^ n.toNat

/-- Memory that suffices for the whole run (`ASSUMPTIONS.md`, E3): the arrays, every
input record, and `clauseBound` lemma records of at most `n + 3` cells each. -/
def memoryBound (input : Input) : CInt :=
  let n := max 1 input.nVars
  clausesAt n + (input.clauses.toList.map fun c => (c.size : CInt) + 3).sum +
    clauseBound n * (n + 3)

/-- The facts that hold between `step`s and also inside `propagate` whenever no
conflict is being analyzed: the layout, the trail, the clause database with its
watch lists and reasons, and the decision order `vs`. -/
structure Core (input : Input) (S : solver) (db : Records) (vs : List CInt) : Prop where
  valid : input.Valid
  nVars : S.nVars = max 1 input.nVars
  memory : memoryBound input ≤ S.mem_max
  maxLemmas : 0 ≤ S.maxLemmas
  layout : Layout S
  trail : Trail S
  root : RootEntailed input S
  database : Database input S db
  watches : WatchLists S db
  reasons : Reasons S db
  units : UnitsTrue S db
  order : OrderList S vs

/-- Where `solve`'s loop is: before the first `propagate` (only root literals, none
processed yet), or just after a decision (C:176–179): the decision is the last, still
unprocessed literal, and the root is exactly the part below `forced`. `propagate`
uses this to show its `forced` flag (C:134) is set exactly at the root. -/
def Mode (S : solver) : Prop :=
  (processedPos S = 0 ∧ ∀ i < trailLen S, RootLevel S i) ∨
  (processedPos S + 1 = trailLen S ∧ IsDecision S (processedPos S) ∧
    ∀ i < trailLen S, RootLevel S i → i < forcedPos S)

/-- The invariant at the top of `solve`'s loop (C:162), for a valid input. -/
def Inv (input : Input) (S : solver) (decision : CInt) : Prop :=
  ∃ db vs, Core input S db vs ∧ WatchedTrue S db ∧ Mode S ∧ Cursor S vs decision

/-- The state after `propagate` returns without a root conflict (C:157): everything is
processed, the watched-literal invariant holds for the whole trail, and the root is
exactly the part below `forced`. `restart`, `reduceDB` and the decision start here. -/
structure Settled (input : Input) (S : solver) (db : Records) (vs : List CInt) : Prop where
  core : Core input S db vs
  watched : WatchedTrue S db
  processed : S.processed = S.assigned
  root_below : ∀ i < trailLen S, RootLevel S i → i < forcedPos S

/-- `Settled` does not read the statistics `res` and `fast`, which `solve` updates
before a restart (C:169). Used by `afterConflict_spec`. -/
theorem Settled.withStats {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Settled input S db vs) (r f : CInt) : Settled input { S with res := r, fast := f } db vs := by
  obtain ⟨⟨valid, nv, mem, ml, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
    ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩, root,
    ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9, d10⟩, watches, reasons, units, ⟨o1, o2, o3, o4⟩⟩,
    watched, processed, below⟩ := h
  exact ⟨⟨valid, nv, mem, ml, ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩,
    ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12⟩, root,
    ⟨d1.frame fun _ _ _ _ => rfl, d2.frame fun _ _ _ _ => rfl, d3, d4, d5, d6, d7, d8, d9, d10⟩,
    fun lit hl => by
      obtain ⟨links, hlinks, hnd, hm⟩ := watches lit hl
      exact ⟨links, hlinks.frame fun _ _ => rfl, hnd, hm⟩,
    reasons, units, ⟨o1.congr fun _ _ => rfl, o2, o3, o4⟩⟩, watched, processed, below⟩

/-- The termination measure, compared lexicographically. Each `step` that does not
finish either raises `maxLemmas` (a `reduceDB`, C:69), or learns at least one new
lemma (`nLemmas`, C:65), or assigns one more variable (a decision, C:177). -/
def rank (S : solver) : Nat × Nat × Nat :=
  let b := clauseBound S.nVars
  (b - min b S.maxLemmas.toNat, b - S.nLemmas.toNat, S.nVars.toNat - trailLen S)

/-- Lexicographic order on ranks. -/
def RankLT : Nat × Nat × Nat → Nat × Nat × Nat → Prop :=
  Prod.Lex (· < ·) (Prod.Lex (· < ·) (· < ·))

/-- Ranks cannot decrease forever. Used by `Main.lean` for termination. -/
theorem rankLT_wf : WellFounded RankLT :=
  (Prod.lex Nat.lt_wfRel (Prod.lex Nat.lt_wfRel Nat.lt_wfRel)).wf

end MicrosatLean.Faithful.Verification
