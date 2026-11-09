import MicrosatLean.Faithful.Verification.Push
import Std.Tactic.Do

/-!
# The decision (C:173–179)

After `propagate` (and possibly `restart`/`reduceDB`), `solve` scans the decision order
from the cursor for an unassigned variable (C:173–174). At the end of the list every
variable is assigned and the model satisfies the input (C:175); otherwise the
variable is assigned with its saved phase as a new decision (C:176–179).

`scan` and `assignDecision` name these two parts of `step`; `step_eq` (in `Step.lean`)
shows `step` is built from them.
-/

namespace MicrosatLean.Faithful.Verification

open Std.Do
set_option mvcgen.warning false

/-- C:173–174: from `decision`, follow `prev` past assigned variables. -/
def scan (S : solver) (decision : CInt) : CInt := Id.run do
  let mut decision := decision
  while S.ld (S.false + decision) != 0 || S.ld (S.false + -decision) != 0 do
    decision := S.ld (S.prev + decision)
  return decision

/-- C:175–179: SAT at the end of the list, otherwise assign the decision. -/
def assignDecision (S : solver) (decision : CInt) : Progress :=
  if decision == 0 then .finished S SAT else
  let decision := if S.ld (S.model + decision) != 0 then decision else -decision
  let S := S.st (S.false + -decision) 1
  let S := S.st S.assigned (-decision)
  let S := { S with assigned := S.assigned + 1 }
  let decision := abs decision
  let S := S.st (S.reason + decision) 0
  .running S decision

/-- The scan stops at 0 with every variable assigned, or at the first unassigned
variable after the cursor. -/
theorem scan_spec {input : Input} {S : solver} {db : Records} {vs : List CInt} {d : CInt}
    (h : Settled input S db vs) (c : Cursor S vs d) :
    (scan S d = 0 ∧ ∀ v, 1 ≤ v → v ≤ S.nVars → Assigned S v) ∨
    (∃ k, ∃ hk : k < vs.length, vs[k] = scan S d ∧
      (∀ j (h : j < vs.length), j < k → Assigned S vs[j]) ∧ ¬ Assigned S (scan S d)) := by
  have ht := h.core.trail
  have ho := h.core.order
  have hnd := ho.nodup
  have h0 : (0 : CInt) ∉ vs := fun h0 => by have := ho.mem_iff.mp h0; omega
  have hz : flag S 0 = 0 := ht.flag_zero
  generalize hR : scan S d = R
  apply Id.of_wp_run_eq hR
  mvcgen [scan] invariants
  · fun d => ULift.up (vs.length - vs.idxOf d)
  · ⇓ c => match c with
      | .inl d => ⌜Cursor S vs d⌝
      | .inr d => ⌜(d = 0 ∧ ∀ v, 1 ≤ v → v ≤ S.nVars → Assigned S v) ∨
          (∃ k, ∃ hk : k < vs.length, vs[k] = d ∧
            (∀ j (h : j < vs.length), j < k → Assigned S vs[j]) ∧ ¬ Assigned S d)⌝
  case vc1.step.isTrue =>
    rename_i d0 m hc hinv
    obtain ⟨hvar, k, hk, hd, before⟩ := hinv
    simp [WhileVariant.eval, SVal.evalsTo] at hvar ⊢
    have hflag : flag S d0 ≠ 0 ∨ flag S (-d0) ≠ 0 := by simpa [flag] using hc
    have hk' : k < vs.length := by
      rcases Nat.lt_or_ge k vs.length with h' | h'
      · exact h'
      · exfalso
        rw [List.getElem?_eq_none h'] at hd; simp at hd; subst hd
        simp [hz] at hflag
    rw [List.getElem?_eq_getElem hk'] at hd; simp only [Option.getD_some] at hd; subst hd
    have hmem : vs[k] ∈ vs := List.getElem_mem hk'
    have hasg := (ht.assigned_iff (ho.mem_iff.mp hmem)).mp hflag
    have hnext := ho.chain.prev_getElem k hk'
    refine ⟨?_, k + 1, by omega, by rw [hnext], ?_⟩
    · rw [hvar, hnext, hnd.idxOf_getElem k hk']
      rcases Nat.lt_or_ge (k + 1) vs.length with h' | h'
      · rw [List.getElem?_eq_getElem h', Option.getD_some, hnd.idxOf_getElem (k + 1) h']; omega
      · rw [List.getElem?_eq_none h', Option.getD_none, List.idxOf_eq_length h0]; omega
    · intro j hj hjk
      rcases Nat.lt_or_ge j k with h' | h'
      · exact before j hj h'
      · have : j = k := by omega
        subst this; exact hasg
  case vc2.step.isFalse =>
    rename_i d0 m hc hinv
    obtain ⟨hvar, k, hk, hd, before⟩ := hinv
    have hflag : ¬ (flag S d0 ≠ 0 ∨ flag S (-d0) ≠ 0) := by simpa [flag] using hc
    rcases Nat.lt_or_ge k vs.length with hk' | hk'
    · rw [List.getElem?_eq_getElem hk'] at hd; simp only [Option.getD_some] at hd; subst hd
      have hmem : vs[k] ∈ vs := List.getElem_mem hk'
      refine Or.inr ⟨k, hk', rfl, before, fun ha => hflag ((ht.assigned_iff (ho.mem_iff.mp hmem)).mpr ha)⟩
    · rw [List.getElem?_eq_none hk'] at hd; simp at hd; subst hd
      refine Or.inl ⟨rfl, fun v h1 h2 => ?_⟩
      obtain ⟨j, hj, he⟩ := List.getElem_of_mem (ho.mem_iff.mpr ⟨h1, h2⟩)
      rw [← he]; exact before j hj (by omega)


/-- With every variable assigned after `propagate`, the saved phases satisfy the input:
each clause has a true watched literal (`WatchedTrue`) or is a true unit (`UnitsTrue`). -/
theorem sat_of_assigned {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Settled input S db vs) (all : ∀ v, 1 ≤ v → v ≤ S.nVars → Assigned S v) :
    input.Sat (modelOf S) := by
  intro clause hc
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem hc
  have hdb := h.core.database
  have ht := h.core.trail
  have hi' : i < db.inputs.length := by rw [hdb.inputs_length]; exact hi
  rw [← clauseSat_perm (hdb.inputs_perm i hi' hi)]
  have hr : db.inputs[i] ∈ db.all := List.mem_append_left _ (List.getElem_mem hi')
  have hne := hdb.inputs_nonempty _ (List.getElem_mem hi')
  generalize db.inputs[i] = r at hr hne
  obtain ⟨x, xs, hrx⟩ : ∃ x xs, r.2 = x :: xs := by
    cases h' : r.2 with
    | nil => exact absurd h' hne
    | cons x xs => exact ⟨x, xs, rfl⟩
  have h0 : r.2[0]! = x := by rw [hrx]; rfl
  have hpos : processedPos S = trailLen S := by
    simp only [processedPos, trailLen, h.processed]
  by_cases hunit : r.2.length = 1
  · obtain ⟨q, hq, -, he⟩ := h.core.units r hr hunit
    rw [h0] at he
    exact ⟨x, by rw [hrx]; simp, ht.litTrue hq he⟩
  · have h2 : 2 ≤ r.2.length := by
      have : r.2.length ≠ 0 := by rw [hrx]; simp
      omega
    have hx := inRange_iff.mp (h.core.record_lit hr (l := x) (by rw [hrx]; simp))
    obtain ⟨j, hj, hab⟩ := all (abs x) (by rcases abs_cases x with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
      (by rcases abs_cases x with ⟨_, e⟩ | ⟨_, e⟩ <;> omega)
    have hx' : trailAt S j = x ∨ trailAt S j = -x := by
      rcases abs_cases x with ⟨_, e⟩ | ⟨_, e⟩ <;>
        rcases abs_cases (trailAt S j) with ⟨_, e'⟩ | ⟨_, e'⟩ <;> omega
    rcases hx' with he | he
    · obtain ⟨q, ⟨hq, hq'⟩, -⟩ := h.watched r hr h2 0 1 (Or.inl ⟨rfl, rfl⟩) j (by omega)
        ⟨hj, by rw [h0]; exact he⟩
      have hm : r.2[1]! ∈ r.2 := by
        rw [getElem!_pos r.2 1 h2]; exact List.getElem_mem _
      exact ⟨r.2[1]!, hm, ht.litTrue hq hq'⟩
    · exact ⟨x, by rw [hrx]; simp, ht.litTrue hj he⟩

/-- Assigning an unassigned variable as a decision (C:176–179) gives the invariant of
the next iteration, with the cursor at that variable. -/
theorem assignDecision_spec {input : Input} {S : solver} {db : Records} {vs : List CInt}
    {k : Nat} (h : Settled input S db vs) (hk : k < vs.length)
    (before : ∀ j (h : j < vs.length), j < k → Assigned S vs[j]) (free : ¬ Assigned S vs[k]) :
    match assignDecision S vs[k] with
    | .finished _ _ => False
    | .running S' d' => Inv input S' d' ∧ trailLen S' = trailLen S + 1 ∧
        S'.nLemmas = S.nLemmas ∧ S'.maxLemmas = S.maxLemmas := by
  have core := h.core
  have hl := core.layout; have hn := hl.num; have ht := core.trail
  have hv : 1 ≤ vs[k] ∧ vs[k] ≤ S.nVars := core.order.mem_iff.mp (List.getElem_mem hk)
  have hA : S.falseStack ≤ S.assigned ∧ S.assigned ≤ S.falseStack + S.nVars := by
    have := ht.forced_le; have := ht.processed_le; have := ht.assigned_le; have := ht.len_le
    simp only [trailLen] at this; omega
  generalize hvk : vs[k] = v at free hv
  -- the decision literal, with its saved phase (C:176)
  generalize hdl : (if S.ld (S.model + v) != 0 then v else -v) = dl
  have hsign : (S.ld (S.model + v) ≠ 0 → dl = v) ∧ (S.ld (S.model + v) = 0 → dl = -v) := by
    constructor <;> intro hm <;> rw [← hdl] <;> simp [hm]
  have hda : abs dl = v ∧ (dl = v ∨ dl = -v) := by
    have hor : dl = v ∨ dl = -v := by
      by_cases hm : S.ld (S.model + v) = 0
      · exact Or.inr (hsign.2 hm)
      · exact Or.inl (hsign.1 hm)
    refine ⟨?_, hor⟩
    simp only [abs]; split <;> omega
  have hdn : dl ≠ 0 ∧ -S.nVars ≤ dl ∧ dl ≤ S.nVars := by omega
  -- the state after C:177–179
  generalize hT : (let S1 := S.st (S.false + -dl) 1
    let S2 := S1.st S1.assigned (-dl)
    let S3 : solver := { S2 with assigned := S2.assigned + 1 }
    S3.st (S3.reason + abs dl) 0) = T
  have heq : assignDecision S v = .running T (abs dl) := by
    rw [← hT, ← hdl]; unfold assignDecision; rw [if_neg (by simp; omega)]
  rw [heq]
  have hcell : ∀ q, 0 ≤ q → T.ld q = if q = S.reason + v then 0 else if q = S.assigned then -dl
      else if q = S.false + -dl then 1 else S.ld q := by
    intro q hq
    rw [← hT]
    dsimp only
    rw [ld_st _ _ (by simp only [st_reason]; omega) hq, st_reason, st_reason, hda.1]
    split; rfl
    show ((S.st (S.false + -dl) 1).st (S.st (S.false + -dl) 1).assigned (-dl)).ld q = _
    rw [ld_st _ _ (by simp; omega) hq, st_assigned]
    split; rfl
    rw [ld_st _ _ (by omega) hq]
  have hfresh : Fresh S (-dl) := ⟨hl, ht, inRange_iff.mpr ⟨by omega, by omega, by omega⟩, fun i hi he => by
    rw [abs_neg', hda.1] at he; exact free ⟨i, hi, he⟩⟩
  have hpush : Push S T (-dl) 1 0 := by
    refine ⟨⟨T.DB, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hT]; apply solver.ext <;> simp
    · rw [hcell _ (by omega), if_neg (by omega), if_pos rfl]
    · rw [hcell _ (by omega), if_neg (by omega), if_neg (by omega), if_pos rfl]
    · rw [abs_neg', hda.1, hcell _ (by omega), if_pos rfl]
    · rw [abs_neg', hda.1, hcell _ (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
      by_cases hm : S.ld (S.model + v) = 0
      · rw [hsign.2 hm]; exact ⟨fun h0 => absurd hm h0, fun h0 => by omega⟩
      · rw [hsign.1 hm]; exact ⟨fun _ => by omega, fun _ => hm⟩
    · intro q hq h1 h2 h3 _
      rw [abs_neg', hda.1] at h3
      rw [hcell q hq, if_neg h3, if_neg h1, if_neg h2]
  obtain ⟨hla, hdb, hwl, hol⟩ := hpush.frames hfresh core.database core.watches core.order
  have hnotroot : ¬ RootLevel T (trailLen S) := fun hr =>
    ((hpush.rootLevel_top hfresh).mp hr).2 rfl
  obtain ⟨hA', hF', hP', hH', hU', hFx', hN', hM', hMM'⟩ := hpush.keeps
  have hlen := hpush.trailLen_eq hfresh
  have hppos : processedPos S = trailLen S := by simp only [processedPos, trailLen, h.processed]
  refine ⟨⟨db, vs, ⟨core.valid, by rw [hpush.shape.nVars]; exact core.nVars, by rw [hMM']; exact core.memory,
      by rw [hM']; exact core.maxLemmas, hla, hpush.trail hfresh ⟨fun hr => absurd hr hnotroot, fun _ => rfl⟩,
      hpush.rootEntailed hfresh core.root (fun hr => absurd hr hnotroot), hdb, hwl,
      hpush.reasons hfresh core.reasons (fun h0 => absurd rfl h0), hpush.units hfresh core.units, hol⟩,
      hpush.watched hfresh h.watched, ?_, ?_⟩, hlen, hN', hM'⟩
  · -- the decision is the last literal and not yet processed (C:178–179)
    have hpp : processedPos T = trailLen S := by
      rw [← hppos]; simp only [processedPos, hP', hpush.shape.falseStack]
    refine Or.inr ⟨by rw [hpp, hlen], by rw [hpp]; exact (hpush.isDecision_top hfresh).mpr rfl, ?_⟩
    intro i hi hr
    have hfp : forcedPos T = forcedPos S := by simp only [forcedPos, hF', hpush.shape.falseStack]
    rw [hfp]
    rw [hlen] at hi
    rcases Nat.lt_or_ge i (trailLen S) with hi' | hi'
    · exact h.root_below i hi' ((hpush.rootLevel_lt hfresh hi').mp hr)
    · have : i = trailLen S := by omega
      subst this; exact absurd hr hnotroot
  · -- the cursor is at the decision (C:173)
    refine ⟨k, Nat.le_of_lt hk, by rw [List.getElem?_eq_getElem hk, hvk, hda.1]; rfl,
      fun j hj hjk => hpush.assigned hfresh (before j hj hjk)⟩

/-- The decision part of `step`, from a `Settled` state with a cursor. Used by `step`'s
proof. -/
theorem decide_spec {input : Input} {S : solver} {db : Records} {vs : List CInt} {d : CInt}
    (h : Settled input S db vs) (c : Cursor S vs d) :
    match assignDecision S (scan S d) with
    | .finished S' r => CorrectResult input (S', r)
    | .running S' d' => Inv input S' d' ∧ trailLen S' = trailLen S + 1 ∧
        S'.nLemmas = S.nLemmas ∧ S'.maxLemmas = S.maxLemmas := by
  rcases scan_spec h c with ⟨h0, all⟩ | ⟨k, hk, hv, before, free⟩
  · rw [h0]
    exact Or.inl ⟨rfl, sat_of_assigned h all⟩
  · rw [← hv]
    have := assignDecision_spec h hk before (hv ▸ free)
    revert this
    cases assignDecision S vs[k] with
    | finished _ _ => exact False.elim
    | running _ _ => exact id

end MicrosatLean.Faithful.Verification
