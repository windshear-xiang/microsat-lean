import MicrosatLean.Faithful.Verification.AnalyzeState

/-!
# MARK and resolution in `analyze` (C:103–113)

One iteration of each of the first four loops of `analyze`: bumping the conflict clause,
the resolution loop, its first-UIP check loop, and bumping a reason. The `vc_*` lemmas
state them in the form `mvcgen` produces in `AnalyzeLoop.lean`.
-/

namespace MicrosatLean.Faithful.Verification

section Resolve
variable {input : Input} {T : solver} {db : Records} {vs : List CInt} {D : Nat}

/-- `bump` changes only `DB` and `head`. -/
theorem AFields.dbhead {S : solver} (h : AFields T S) (DB : Array CInt) (hd : CInt) :
    AFields T ({ S with DB := DB, head := hd } : solver) := by
  obtain ⟨_, a, p, _, r, nc, fa, sl, rfl⟩ := h; exact ⟨DB, a, p, hd, r, nc, fa, sl, rfl⟩

/-- The state after C:103. -/
theorem RState.init (ctx : ACtx input T db vs D) :
    RState T ({ T with res := T.res + 1, nConflicts := T.nConflicts + 1 } : solver) (trailLen T) := by
  have ht := ctx.core.trail
  have o := ctx.core.order
  exact ⟨⟨T.DB, T.assigned, T.processed, T.head, T.res + 1, T.nConflicts + 1, T.fast, T.slow, rfl⟩,
    ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun q _ _ => rfl, fun q _ => rfl⟩, fun q _ _ => rfl,
    Nat.le_refl _, ⟨vs, o.1.congr fun _ _ => rfl, o.2, o.3, o.4⟩, fun i hi hr => ht.flag_root i hi hr,
    fun i hi hr => Or.inl (ht.flag_level i hi hr), fun i h1 h2 => absurd h2 (by omega),
    fun l hl ho => ht.flag_off l hl ho, ht.flag_zero⟩

/-- Moving `assigned` keeps an `RState`. -/
theorem RState.setAssigned {S : solver} {a : Nat} (h : RState T S a) (x : CInt) :
    RState T ({ S with assigned := x } : solver) a := by
  obtain ⟨hf, ⟨hs, hm, hh⟩, hmod, hle, ⟨vs, o⟩, h1, h2, h3, h4, h5⟩ := h
  refine ⟨?_, ⟨⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6, hs.7, hs.8, hs.9⟩, hm, hh⟩, hmod, hle, ⟨vs, o.1.congr fun _ _ => rfl, o.2, o.3, o.4⟩,
    h1, h2, h3, h4, h5⟩
  obtain ⟨DB, a, p, hd, r, nc, fa, sl, rfl⟩ := hf; exact ⟨DB, x, p, hd, r, nc, fa, sl, rfl⟩

/-- Writing a flag of a literal other than `l` keeps `l`'s flag. -/
theorem flag_st_ne (ctx : ACtx input T db vs D) {S : solver} (hs : SameShape T S) {x l v : CInt}
    (hx : -T.nVars ≤ x ∧ x ≤ T.nVars) (hl : -T.nVars ≤ l ∧ l ≤ T.nVars) (hne : l ≠ x) :
    flag (S.st (S.false + x) v) l = flag S l := by
  have := ctx.num
  simp only [flag, st_false, hs.false]
  rw [ld_st _ _ (by omega) (by omega), if_neg (by omega)]

/-- `bump` (C:85–91) on a trail literal below `a`: it is MARKed unless at the root. -/
theorem RState.mark (ctx : ACtx input T db vs D) {S : solver} {a i : Nat} (h : RState T S a) (hi : i < a) :
    RState T (bump S (trailAt T i)) a ∧ (bump S (trailAt T i)).assigned = S.assigned ∧
    (¬ RootLevel T i → Marked T (bump S (trailAt T i)) i) ∧
    ∀ i' < trailLen T, i' ≠ i → flag (bump S (trailAt T i)) (trailAt T i') = flag S (trailAt T i') := by
  have hn := ctx.num
  have hle := h.le
  have hit : i < trailLen T := by omega
  have hlit := ctx.lit hit
  obtain ⟨vs0, ho⟩ := h.order
  have hS := h.fields.shape
  have hl := ctx.layout h.fields h.low
  have hin : InRange S.nVars (trailAt T i) := inRange_iff.mpr (by rw [hS.nVars]; exact hlit)
  obtain ⟨⟨DB, hd, heq⟩, hflag, hcells, ⟨vs', ho'⟩⟩ := bump_spec hl ho hin
  generalize hB : bump S (trailAt T i) = S' at heq hflag hcells ho' ⊢
  have hsh : SameShape S S' := by rw [heq]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  have same : ∀ q, 0 ≤ q → q ≠ T.false + trailAt T i → (q ≤ T.nVars ∨ 3 * T.nVars + 2 < q) →
      S'.ld q = S.ld q := fun q h0 h1 h2 => hcells q h0 (by rw [hS.false]; exact h1) (by rw [hS.nVars]; exact h2)
  have flag_ne : ∀ l, -T.nVars ≤ l → l ≤ T.nVars → l ≠ trailAt T i → flag S' l = flag S l := by
    intro l h1 h2 h3
    simp only [flag, hsh.false, hS.false]
    exact same _ (by omega) (by omega) (by omega)
  have ne_of : ∀ i' < trailLen T, i' ≠ i → trailAt T i' ≠ trailAt T i := fun i' hi' hne he =>
    hne (ctx.pos_eq hi' hit he)
  have hfi : flag S (trailAt T i) = IMPLIED ↔ RootLevel T i := by
    constructor
    · intro hf; refine Classical.byContradiction fun hr => ?_
      rcases h.level i hi hr with e | e <;> rw [e] at hf <;> exact absurd hf (by decide)
    · exact h.root i hi
  refine ⟨⟨?_, ⟨hS.trans hsh, fun q h1 h2 => ?_, fun q h1 => ?_⟩, fun q h1 h2 => ?_, h.le, ⟨vs', ho'⟩,
    fun i' hi' hr => ?_, fun i' hi' hr => ?_, fun i' h1 h2 => ?_, fun l hl ho => ?_, ?_⟩,
    by rw [heq], fun hr => ?_, fun i' hi' hne => flag_ne _ (ctx.lit hi').2.1 (ctx.lit hi').2.2 (ne_of i' hi' hne)⟩
  · rw [heq]; exact h.fields.dbhead DB hd
  · rw [same q (by omega) (by omega) (by omega)]; exact h.low.mid q h1 h2
  · rw [same q (by omega) (by omega) (by omega)]; exact h.low.high q h1
  · rw [same q h1 (by omega) (by omega)]; exact h.model q h1 h2
  · by_cases he : i' = i
    · subst he; rw [hflag, if_pos (h.root i' hi' hr)]
    · rw [flag_ne _ (ctx.lit (by omega)).2.1 (ctx.lit (by omega)).2.2 (ne_of i' (by omega) he)]; exact h.root i' hi' hr
  · by_cases he : i' = i
    · subst he; rw [hflag, if_neg (fun e => hr (hfi.mp e))]; exact Or.inr rfl
    · rw [flag_ne _ (ctx.lit (by omega)).2.1 (ctx.lit (by omega)).2.2 (ne_of i' (by omega) he)]; exact h.level i' hi' hr
  · rw [flag_ne _ (ctx.lit h2).2.1 (ctx.lit h2).2.2 (ne_of i' h2 (by omega))]; exact h.above i' h1 h2
  · have hl' := inRange_iff.mp hl
    rw [flag_ne _ hl'.2.1 hl'.2.2 (fun e => ho i hit e.symm)]; exact h.off l hl ho
  · rw [flag_ne 0 (by omega) (by omega) (fun e => hlit.1 e.symm)]; exact h.zero
  · show flag S' (trailAt T i) = MARK
    rw [hflag, if_neg (fun e => hr (hfi.mp e))]

/-- `unassign` (C:36) of the top position `j`. -/
theorem RState.unassignTop (ctx : ACtx input T db vs D) {S : solver} {j : Nat} (h : RState T S (j + 1)) :
    RState T (unassign S (trailAt T j)) j ∧ (unassign S (trailAt T j)).assigned = S.assigned ∧
    ∀ i' < trailLen T, i' ≠ j → flag (unassign S (trailAt T j)) (trailAt T i') = flag S (trailAt T i') := by
  have hn := ctx.num
  have hjt : j < trailLen T := by have := h.le; omega
  have hlit := ctx.lit hjt
  have hS := h.fields.shape
  have hw : Writable T (S.false + trailAt T j) := by rw [hS.false]; exact ctx.writable_flag ⟨hlit.2.1, hlit.2.2⟩
  have ne_of : ∀ i' < trailLen T, i' ≠ j → trailAt T i' ≠ trailAt T j := fun i' hi' hne he =>
    hne (ctx.pos_eq hi' hjt he)
  have flag_ne : ∀ l, -T.nVars ≤ l → l ≤ T.nVars → l ≠ trailAt T j →
      flag (unassign S (trailAt T j)) l = flag S l := fun l h1 h2 h3 =>
    flag_st_ne ctx hS ⟨hlit.2.1, hlit.2.2⟩ ⟨h1, h2⟩ h3
  have hz : flag (unassign S (trailAt T j)) (trailAt T j) = 0 := by
    simp only [unassign, flag, st_false]; rw [ld_st_self _ _ (by rw [hS.false]; omega)]
  refine ⟨⟨h.fields.st _ _, h.low.st hw 0, fun q h1 h2 => ?_, by omega, ?_, fun i' hi' hr => ?_,
    fun i' hi' hr => ?_, fun i' h1 h2 => ?_, fun l hl ho => ?_, ?_⟩, by simp [unassign],
    fun i' hi' hne => flag_ne _ (ctx.lit hi').2.1 (ctx.lit hi').2.2 (ne_of i' hi' hne)⟩
  · simp only [unassign]
    rw [ld_st _ _ (by rw [hS.false]; omega) h1, if_neg (by rw [hS.false]; omega)]; exact h.model q h1 h2
  · obtain ⟨vs, o⟩ := h.order
    refine ⟨vs, o.frame (ctx.layout h.fields h.low) (SameShape.st _ _ _) (by simp [unassign]) fun q h1 h2 => ?_⟩
    simp only [unassign]
    rw [ld_st _ _ (by rw [hS.false]; omega) (by omega), if_neg (by rw [hS.false, hS.nVars] at *; omega)]
  · rw [flag_ne _ (ctx.lit (by omega)).2.1 (ctx.lit (by omega)).2.2 (ne_of i' (by omega) (by omega))]
    exact h.root i' (by omega) hr
  · rw [flag_ne _ (ctx.lit (by omega)).2.1 (ctx.lit (by omega)).2.2 (ne_of i' (by omega) (by omega))]
    exact h.level i' (by omega) hr
  · by_cases he : i' = j
    · subst he; exact hz
    · rw [flag_ne _ (ctx.lit h2).2.1 (ctx.lit h2).2.2 (ne_of i' h2 he)]; exact h.above i' (by omega) h2
  · have hl' := inRange_iff.mp hl
    rw [flag_ne _ hl'.2.1 hl'.2.2 (fun e => ho j hjt e.symm)]; exact h.off l hl ho
  · rw [flag_ne 0 (by omega) (by omega) (fun e => hlit.1 e.symm)]; exact h.zero

end Resolve

section Phase12
variable {input : Input} {T : solver} {db : Records} {vs : List CInt} {D : Nat}

/-- A record of the database sits at its pointer in `T`. -/
theorem ACtx.clauseAt (ctx : ACtx input T db vs D) {r : Record} (hr : r ∈ db.all) : ClauseAt T r.1 r.2 := by
  rcases List.mem_append.mp hr with h' | h'
  · exact ctx.core.database.inputs_tile.clauseAt h'
  · exact ctx.core.database.lemmas_tile.clauseAt h'

/-- Reading a record's cell `k ≤ length` in a state with `T`'s high cells. -/
theorem ACtx.read (ctx : ACtx input T db vs D) {S : solver} (hl : SameLow T S) {r : Record} (hr : r ∈ db.all)
    {k : Nat} (hk : k ≤ r.2.length) : S.ld (r.1 + k) = if h : k < r.2.length then r.2[k] else 0 := by
  have hc := ctx.clauseAt hr
  have hg := ctx.core.database.record_ge hr
  have := ctx.num
  rw [hl.high _ (by simp only [clausesAt] at hg; omega)]
  split
  · exact hc.1 k (by assumption)
  · rw [show k = r.2.length by omega]; exact hc.2

/-- The literals of a record are nonzero. -/
theorem ACtx.rec_ne (ctx : ACtx input T db vs D) {r : Record} (hr : r ∈ db.all) {k : Nat} (hk : k < r.2.length) :
    r.2[k] ≠ 0 :=
  (inRange_iff.mp (ctx.core.record_lit hr (List.getElem_mem hk))).1

/-- Membership in a prefix one longer. -/
theorem mem_take_succ {l : List CInt} {k : Nat} (hk : k < l.length) {x : CInt} (h : x ∈ l.take (k + 1)) :
    x ∈ l.take k ∨ x = l[k] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk] at h
  rcases List.mem_append.mp h with h | h
  · exact Or.inl h
  · exact Or.inr (by simpa using h)

/-- C:104, one literal of the conflict clause. -/
theorem BumpInv.step (ctx : ACtx input T db vs D) {r : Record} (hr : r ∈ db.all)
    (hfalse : ∀ l ∈ r.2, ∃ j < trailLen T, trailAt T j = l) {S : solver} {cl : Ptr}
    (h : BumpInv T S r.1 r.2 cl) (hne : S.ld cl ≠ 0) :
    BumpInv T (bump S (S.ld cl)) r.1 r.2 (cl + 1) ∧ T.mem_used - (cl + 1) < T.mem_used - cl ∧
      0 ≤ T.mem_used - (cl + 1) := by
  obtain ⟨hrs, hA, k, hk, rfl, hmarks⟩ := h
  have hg := ctx.core.database.record_ge hr
  have hread := ctx.read hrs.low hr hk
  have hk' : k < r.2.length := by
    refine Classical.byContradiction fun hn => hne ?_
    rw [hread, dif_neg hn]
  rw [dif_pos hk'] at hread
  obtain ⟨j, hj, hje⟩ := hfalse _ (List.getElem_mem hk')
  rw [hread, ← hje]
  obtain ⟨hrs', hA', hmark, hflags⟩ := hrs.mark ctx hj
  refine ⟨⟨hrs', hA'.trans hA, k + 1, hk', by omega, fun i hi hr hm => ?_⟩, by omega, by omega⟩
  rcases mem_take_succ hk' hm with hm | hm
  · have := hmarks i hi hr hm
    by_cases he : i = j
    · subst he; exact hmark hr
    · unfold Marked at this ⊢; rw [hflags i hi he]; exact this
  · rw [← hje] at hm
    have := ctx.pos_eq hi hj hm; subst this; exact hmark hr

/-- C:105: after C:104 the MARKed literals are the conflict clause without its root
literals, one of them at the last decision level. -/
theorem ResInv.init (ctx : ACtx input T db vs D) {r : Record} (hr : r ∈ db.all)
    (hfalse : ∀ l ∈ r.2, ∃ j < trailLen T, trailAt T j = l)
    (hmark : ∃ j, D ≤ j ∧ j < trailLen T ∧ trailAt T j ∈ r.2) {S : solver} {cl : Ptr}
    (h : BumpInv T S r.1 r.2 cl) (hz : S.ld cl = 0) : ResInv input T D S (trailLen T) := by
  obtain ⟨hrs, hA, k, hk, rfl, hmarks⟩ := h
  have hread := ctx.read hrs.low hr hk
  have hk' : k = r.2.length := by
    refine Classical.byContradiction fun hn => ?_
    rw [dif_pos (by omega)] at hread
    exact ctx.rec_ne hr (by omega) (hread.symm.trans hz)
  subst hk'
  rw [List.take_length] at hmarks
  have hn := ctx.num
  refine ⟨hrs, by rw [hA]; omega, ctx.lt, fun a ha => ?_, ?_⟩
  · obtain ⟨l, hl, ht⟩ := ctx.core.record_entailed hr a ha
    obtain ⟨j, hj, rfl⟩ := hfalse l hl
    have hnr : ¬ RootLevel T j := fun hroot => ctx.root_false hj hroot ha ht
    exact ⟨j, hj, hmarks j hj hnr hl, ht⟩
  · obtain ⟨j, hDj, hj, hm⟩ := hmark
    exact ⟨j, hDj, hj, hmarks j hj (ctx.not_root hDj) hm⟩

/-- The values the resolution loop reads at its top position `a - 1`. -/
theorem ResInv.reads (ctx : ACtx input T db vs D) {S : solver} {a : Nat} (h : ResInv input T D S a) :
    let S1 : solver := { S with assigned := S.assigned - 1 }
    S1.assigned = T.falseStack + (a - 1 : Nat) ∧ a - 1 < trailLen T ∧ D ≤ a - 1 ∧
    S1.ld S1.assigned = trailAt T (a - 1) ∧
    S1.ld (S1.reason + abs (S1.ld S1.assigned)) = reasonOf T (trailAt T (a - 1)) ∧
    S1.ld (S1.false + S1.ld S1.assigned) = flag S (trailAt T (a - 1)) := by
  intro S1
  obtain ⟨hrs, hA, hDa, -, -⟩ := h
  have hle := hrs.le
  have hn := ctx.num
  have hs := hrs.fields.shape
  have hA1 : S1.assigned = T.falseStack + (a - 1 : Nat) := by
    show S.assigned - 1 = _; rw [hA]; omega
  have htr : S1.ld S1.assigned = trailAt T (a - 1) := by
    rw [hA1]; exact hrs.low.trail ctx (by omega)
  refine ⟨hA1, by omega, by omega, htr, ?_, ?_⟩
  · rw [htr]; show S.ld (S.reason + _) = _; rw [hs.reason]; exact hrs.low.reason ctx (ctx.lit (by omega))
  · rw [htr]; rfl

/-- C:105: the top position is the last decision, so it is the first UIP (`build`). -/
theorem ResInv.decision (ctx : ACtx input T db vs D) {S : solver} {a : Nat} (h : ResInv input T D S a)
    (hz : reasonOf T (trailAt T (a - 1)) = 0) :
    BuildStart input T D ({ S with assigned := S.assigned - 1 } : solver) (a - 1) := by
  obtain ⟨hA1, hlt, hDj, -, -, -⟩ := h.reads ctx
  obtain ⟨hrs, hA, hDa, hme, ⟨i, hDi, hia, hmi⟩⟩ := h
  have hjD : a - 1 = D := Classical.byContradiction fun hne => ctx.last (a - 1) (by omega) hlt hz
  have ha : a - 1 + 1 = a := by omega
  refine ⟨by rw [ha]; exact hrs.setAssigned _, hA1, hDj, hlt, by rw [ha]; exact hme, ?_, fun i h1 h2 => by omega⟩
  have : i = a - 1 := by omega
  subst this; exact hmi

/-- C:108: the check loop starts at the top position. -/
theorem ResInv.check_init (ctx : ACtx input T db vs D) {S : solver} {a : Nat} (h : ResInv input T D S a)
    (hnz : reasonOf T (trailAt T (a - 1)) ≠ 0) :
    CheckInv T D ({ S with assigned := S.assigned - 1 } : solver) ({ S with assigned := S.assigned - 1 } : solver).assigned := by
  obtain ⟨hA1, hlt, hDj, -, -, -⟩ := h.reads ctx
  have hDl : D < a - 1 := by
    rcases Nat.lt_or_ge D (a - 1) with h1 | h1
    · exact h1
    · have : a - 1 = D := by omega
      rw [this] at hnz; exact absurd ctx.dec hnz
  exact ⟨a - 1, hA1, hDl, by rw [hA1]; omega, fun m h1 h2 => by rw [hA1] at h2; omega⟩

/-- The values the check loop reads (C:108–109). -/
theorem CheckInv.reads (ctx : ACtx input T db vs D) {S1 : solver} {ck : Ptr} (hl : SameLow T S1)
    (hs : SameShape T S1) (hA : S1.assigned - T.falseStack < trailLen T) (h : CheckInv T D S1 ck) :
    ∃ k : Nat, ck = T.falseStack + k ∧ D < k ∧ (k : CInt) ≤ S1.assigned - T.falseStack ∧
      (∀ m : Nat, k ≤ m → (m : CInt) < S1.assigned - T.falseStack → ¬ Marked T S1 m) ∧
      S1.ld (ck - 1) = trailAt T (k - 1) ∧
      S1.ld (S1.false + S1.ld (ck - 1)) = flag S1 (trailAt T (k - 1)) ∧
      S1.ld (S1.reason + abs (S1.ld (ck - 1))) = reasonOf T (trailAt T (k - 1)) := by
  obtain ⟨k, rfl, hDk, hkj, hnm⟩ := h
  have hn := ctx.num
  have htr : S1.ld (T.falseStack + k - 1) = trailAt T (k - 1) := by
    rw [show T.falseStack + (k : CInt) - 1 = T.falseStack + ((k - 1 : Nat) : CInt) by omega]
    exact hl.trail ctx (by omega)
  refine ⟨k, rfl, hDk, hkj, hnm, htr, by rw [htr]; rfl, ?_⟩
  rw [htr, hs.reason]; exact hl.reason ctx (ctx.lit (by omega))

/-- C:108–109: no MARK and no decision at `k - 1`: the check moves down. -/
theorem CheckInv.step (ctx : ACtx input T db vs D) {S1 : solver} {k : Nat} (hDk : D < k)
    (hnm : ∀ m : Nat, k ≤ m → (m : CInt) < S1.assigned - T.falseStack → ¬ Marked T S1 m)
    (hkj : (k : CInt) ≤ S1.assigned - T.falseStack) (hA : S1.assigned - T.falseStack < trailLen T)
    (hmk : ¬ Marked T S1 (k - 1)) (hdec : reasonOf T (trailAt T (k - 1)) ≠ 0) :
    CheckInv T D S1 (T.falseStack + k - 1) := by
  have hDk' : D < k - 1 := by
    rcases Nat.lt_or_ge D (k - 1) with h1 | h1
    · exact h1
    · have : k - 1 = D := by omega
      rw [this] at hdec; exact absurd ctx.dec hdec
  refine ⟨k - 1, by omega, hDk', by omega, fun m h1 h2 => ?_⟩
  rcases Nat.lt_or_ge m k with h3 | h3
  · have : m = k - 1 := by omega
    subst this; exact hmk
  · exact hnm m h3 h2

/-- C:109: reaching the last decision with no MARK means `goto build`. -/
theorem CheckInv.uip (ctx : ACtx input T db vs D) {S1 : solver} {k : Nat} (hDk : D < k)
    (hnm : ∀ m : Nat, k ≤ m → (m : CInt) < S1.assigned - T.falseStack → ¬ Marked T S1 m)
    (hA : S1.assigned - T.falseStack < trailLen T) (hkj : (k : CInt) ≤ S1.assigned - T.falseStack)
    (hmk : ¬ Marked T S1 (k - 1)) (hdec : reasonOf T (trailAt T (k - 1)) = 0) :
    CheckOut T D S1 true := by
  have hkD : k - 1 = D := Classical.byContradiction fun hne => ctx.last (k - 1) (by omega) (by omega) hdec
  refine Or.inl ⟨rfl, fun m h1 h2 => ?_⟩
  rcases Nat.lt_or_ge m k with h3 | h3
  · have : m = k - 1 := by omega
    subst this; exact hmk
  · exact hnm m h3 h2

/-- C:108: another MARK at the last decision level. -/
theorem CheckInv.found {S1 : solver} {k : Nat} (hDk : D < k) (hkj : (k : CInt) ≤ S1.assigned - T.falseStack)
    (hmk : Marked T S1 (k - 1)) : CheckOut T D S1 false :=
  Or.inr ⟨rfl, k - 1, by omega, by omega, hmk⟩

/-- C:109 `goto build`: the top position is the first UIP. -/
theorem ResInv.uip (ctx : ACtx input T db vs D) {S : solver} {a : Nat} (h : ResInv input T D S a)
    (hm : flag S (trailAt T (a - 1)) = MARK)
    (hc : CheckOut T D ({ S with assigned := S.assigned - 1 } : solver) true) :
    BuildStart input T D ({ S with assigned := S.assigned - 1 } : solver) (a - 1) := by
  obtain ⟨hA1, hlt, hDj, -, -, -⟩ := h.reads ctx
  obtain ⟨hrs, hA, hDa, hme, -⟩ := h
  have ha : a - 1 + 1 = a := by omega
  rcases hc with ⟨-, hno⟩ | ⟨he, -⟩
  · refine ⟨by rw [ha]; exact hrs.setAssigned _, hA1, hDj, hlt, by rw [ha]; exact hme, hm, fun i h1 h2 => ?_⟩
    exact hno i h1 (by rw [hA1]; omega)
  · cases he

end Phase12

section Phase2b
variable {input : Input} {T : solver} {db : Records} {vs : List CInt} {D : Nat}

/-- A literal after the first is in `drop 1`. -/
theorem mem_drop_one {l : List CInt} {k : Nat} (hk1 : 1 ≤ k) (hk : k < l.length) : l[k] ∈ l.drop 1 := by
  have h : (l.drop 1)[k - 1]'(by simp; omega) ∈ l.drop 1 := List.getElem_mem _
  have e : (l.drop 1)[k - 1]'(by simp; omega) = l[k] := by
    simp only [List.getElem_drop]; congr 1; omega
  rwa [e] at h

/-- A MARK survives `bump`. -/
theorem RState.mark_keep (ctx : ACtx input T db vs D) {S : solver} {a i0 i : Nat} (h : RState T S a)
    (hi0 : i0 < a) (hi : i < trailLen T) (hm : Marked T S i) : Marked T (bump S (trailAt T i0)) i := by
  obtain ⟨-, -, hmark, hflags⟩ := h.mark ctx hi0
  by_cases he : i = i0
  · subst he
    refine hmark fun hr => ?_
    have := h.root i hi0 hr; unfold Marked at hm; rw [hm] at this; exact absurd this (by decide)
  · unfold Marked at hm ⊢; rw [hflags i hi he]; exact hm

/-- C:110–111: the reason of the top literal `j`, bumped from its literal 1 on. -/
theorem RBump.init (ctx : ACtx input T db vs D) {S : solver} {a : Nat} (h : ResInv input T D S a)
    (hnz : reasonOf T (trailAt T (a - 1)) ≠ 0) :
    RBump T db ({ S with assigned := S.assigned - 1 } : solver) ({ S with assigned := S.assigned - 1 } : solver)
      (({ S with assigned := S.assigned - 1 } : solver).ld
        (({ S with assigned := S.assigned - 1 } : solver).reason +
          abs (({ S with assigned := S.assigned - 1 } : solver).ld ({ S with assigned := S.assigned - 1 } : solver).assigned))) := by
  obtain ⟨hA1, hlt, hDj, -, hrd, -⟩ := h.reads ctx
  have hrs := h.1
  have ha : a - 1 + 1 = a := by have := h.2.2.1; omega
  obtain ⟨rr, hrr, hreason, h0, hdrop, -⟩ := ctx.core.reasons (a - 1) hlt (by have := ctx.forced_le; omega) hnz
  obtain ⟨hl0, -⟩ := List.getElem?_eq_some_iff.mp h0
  refine ⟨a - 1, rr, hA1, hlt, hrr, hreason, h0, hdrop, 1, Nat.le_refl _, hl0, ?_, ?_, rfl,
    fun i _ hm => hm, fun m _ h1 h2 => by omega⟩
  · rw [hrd, hreason]; omega
  · rw [ha]; exact hrs.setAssigned _

/-- C:112, one literal of the reason. -/
theorem RBump.step (ctx : ACtx input T db vs D) {S1 S : solver} {cl : Ptr} (h : RBump T db S1 S cl)
    (hne : S.ld cl ≠ 0) :
    RBump T db S1 (bump S (S.ld cl)) (cl + 1) ∧ T.mem_used - (cl + 1) < T.mem_used - cl ∧
      0 ≤ T.mem_used - (cl + 1) := by
  obtain ⟨j, rr, hA1, hj, hrr, hreason, h0, hdrop, k, hk1, hk, rfl, hrs, hA, hm1, hmk⟩ := h
  have hg := ctx.core.database.record_ge hrr
  have hread := ctx.read hrs.low hrr hk
  have hk' : k < rr.2.length := by
    refine Classical.byContradiction fun hn => hne ?_
    rw [hread, dif_neg hn]
  rw [dif_pos hk'] at hread
  obtain ⟨i0, hi0, ⟨-, hie⟩⟩ := hdrop _ (mem_drop_one hk1 hk')
  rw [hread, ← hie]
  obtain ⟨hrs', hA', hmark, hflags⟩ := hrs.mark ctx (i := i0) (by omega)
  refine ⟨⟨j, rr, hA1, hj, hrr, hreason, h0, hdrop, k + 1, by omega, hk', by omega, hrs', hA'.trans hA,
    fun i hi hm => hrs.mark_keep ctx (by omega) (by omega) (hm1 i hi hm), fun m hm h1 h2 i hi hr he => ?_⟩,
    by omega, by omega⟩
  rcases Nat.lt_or_ge m k with h3 | h3
  · exact hrs.mark_keep ctx (by omega) (by omega) (hmk m hm h1 h3 i hi hr he)
  · have : m = k := by omega
    subst this
    rw [← hie] at he
    have := ctx.pos_eq (by omega) (by omega) he; subst this; exact hmark hr

/-- C:111–113: resolving the top MARKed literal with its reason keeps the MARKed clause
entailed, and one position is unassigned. -/
theorem ResInv.resolve (ctx : ACtx input T db vs D) {S S2 : solver} {a : Nat} {cl : Ptr}
    (h : ResInv input T D S a) (hm : flag S (trailAt T (a - 1)) = MARK)
    (hc : CheckOut T D ({ S with assigned := S.assigned - 1 } : solver) false)
    (hb : RBump T db ({ S with assigned := S.assigned - 1 } : solver) S2 cl) (hz : S2.ld cl = 0) :
    ResInv input T D (unassign S2 (S2.ld S2.assigned)) (a - 1) ∧
      ((unassign S2 (S2.ld S2.assigned)).assigned - T.falseStack).toNat < (S.assigned - T.falseStack).toNat := by
  obtain ⟨hA1, hlt, hDj, -, hrd, -⟩ := h.reads ctx
  obtain ⟨hrs0, hA0, hDa, hme, -⟩ := h
  obtain ⟨j, rr, hA1', hj, hrr, hreason, h0, hdrop, k, hk1, hk, rfl, hrs, hA, hm1, hmk⟩ := hb
  have hn := ctx.num
  have hjj : j = a - 1 := by
    have : (T.falseStack + (j : CInt)) = T.falseStack + ((a - 1 : Nat) : CInt) := by rw [← hA1', hA1]
    omega
  subst hjj
  have hread := ctx.read hrs.low hrr hk
  have hkl : k = rr.2.length := by
    refine Classical.byContradiction fun hn' => ?_
    rw [dif_pos (by omega)] at hread
    exact ctx.rec_ne hrr (by omega) (hread.symm.trans hz)
  have htop : S2.ld S2.assigned = trailAt T (a - 1) := by
    rw [hA, hA1]; exact hrs.low.trail ctx hlt
  rw [htop]
  obtain ⟨hrs3, hA3, hfl3⟩ := hrs.unassignTop ctx
  have keep : ∀ i < a - 1, Marked T S2 i → Marked T (unassign S2 (trailAt T (a - 1))) i := fun i hi hmi => by
    unfold Marked at hmi ⊢; rw [hfl3 i (by omega) (by omega)]; exact hmi
  have hDl : D < a - 1 := by
    rcases Nat.lt_or_ge D (a - 1) with h1 | h1
    · exact h1
    · have : a - 1 = D := by omega
      have hdec := ctx.dec; rw [← this] at hdec
      have hg := ctx.core.database.record_ge hrr; simp only [clausesAt] at hg
      rw [hdec] at hreason; omega
  refine ⟨⟨hrs3, by rw [hA3, hA, hA1], hDl, fun asg hsat => ?_, ?_⟩, by rw [hA3, hA, hA1, hA0]; omega⟩
  · obtain ⟨i, hi, hmi, ht⟩ := hme asg hsat
    rcases Nat.lt_or_ge i (a - 1) with h1 | h1
    · exact ⟨i, h1, keep i h1 (hm1 i (by omega) hmi), ht⟩
    · have : i = a - 1 := by omega
      subst this
      obtain ⟨l, hl, hlt'⟩ := ctx.core.record_entailed hrr asg hsat
      obtain ⟨m, hm', rfl⟩ := List.mem_iff_getElem.mp hl
      rcases Nat.eq_zero_or_pos m with h0' | h0'
      · subst h0'
        have : rr.2[0] = - trailAt T (a - 1) := by
          have := (List.getElem?_eq_some_iff.mp h0).2; exact this
        rw [this] at hlt'
        exact absurd ht (LitTrue.not_of_neg (ctx.lit hlt).1 hlt')
      · obtain ⟨i', hi', ⟨hi't, hie⟩⟩ := hdrop _ (mem_drop_one h0' hm')
        have hnr : ¬ RootLevel T i' := fun hroot => ctx.root_false hi't hroot hsat (by rw [hie]; exact hlt')
        exact ⟨i', hi', keep i' hi' (hmk m hm' h0' (by omega) i' hi' hnr hie), by rw [hie]; exact hlt'⟩
  · rcases hc with ⟨he, -⟩ | ⟨-, m, hDm, hma, hmm⟩
    · cases he
    · have hma' : m < a - 1 := by rw [hA1] at hma; omega
      exact ⟨m, hDm, hma', keep m hma' (hm1 m (by omega) hmm)⟩

/-- C:113: a top literal that is not MARKed is just unassigned. -/
theorem ResInv.skip (ctx : ACtx input T db vs D) {S : solver} {a : Nat} (h : ResInv input T D S a)
    (hnm : flag S (trailAt T (a - 1)) ≠ MARK) (hnz : reasonOf T (trailAt T (a - 1)) ≠ 0) :
    ResInv input T D (unassign ({ S with assigned := S.assigned - 1 } : solver)
      (({ S with assigned := S.assigned - 1 } : solver).ld ({ S with assigned := S.assigned - 1 } : solver).assigned)) (a - 1) ∧
      ((unassign ({ S with assigned := S.assigned - 1 } : solver)
        (({ S with assigned := S.assigned - 1 } : solver).ld ({ S with assigned := S.assigned - 1 } : solver).assigned)).assigned -
          T.falseStack).toNat < (S.assigned - T.falseStack).toNat := by
  obtain ⟨hA1, hlt, hDj, htr, -, -⟩ := h.reads ctx
  obtain ⟨hrs0, hA0, hDa, hme, ⟨i0, hDi0, hi0a, hmi0⟩⟩ := h
  rw [htr]
  have ha : a - 1 + 1 = a := by omega
  have hrs1 : RState T ({ S with assigned := S.assigned - 1 } : solver) (a - 1 + 1) := by
    rw [ha]; exact hrs0.setAssigned _
  obtain ⟨hrs3, hA3, hfl3⟩ := hrs1.unassignTop ctx
  have keep : ∀ i < a - 1, Marked T S i → Marked T (unassign ({ S with assigned := S.assigned - 1 } : solver)
      (trailAt T (a - 1))) i := fun i hi hmi => by
    unfold Marked at hmi ⊢; rw [hfl3 i (by omega) (by omega)]; exact hmi
  have hDl : D < a - 1 := by
    rcases Nat.lt_or_ge D (a - 1) with h1 | h1
    · exact h1
    · have : a - 1 = D := by omega
      have hdec := ctx.dec; rw [← this] at hdec; exact absurd hdec hnz
  have hn := ctx.num
  refine ⟨⟨hrs3, by rw [hA3, hA1], hDl, fun asg hsat => ?_, ?_⟩, by rw [hA3, hA1, hA0]; omega⟩
  · obtain ⟨i, hi, hmi, ht⟩ := hme asg hsat
    have : i ≠ a - 1 := fun e => by subst e; exact hnm hmi
    exact ⟨i, by omega, keep i (by omega) hmi, ht⟩
  · have : i0 ≠ a - 1 := fun e => by subst e; exact hnm hmi0
    exact ⟨i0, hDi0, by omega, keep i0 (by omega) hmi0⟩

end Phase2b

section VCs2
variable {input : Input} {T : solver} {db : Records} {vs : List CInt} {D : Nat}

/-- The reads of the check loop, from the outer state `S0`. -/
theorem check_reads (ctx : ACtx input T db vs D) {S0 : solver} {a : Nat} (hres : ResInv input T D S0 a)
    {ck : Ptr} (hinv : CheckInv T D ({ S0 with assigned := S0.assigned - 1 } : solver) ck) :
    let S1 : solver := { S0 with assigned := S0.assigned - 1 }
    ∃ k : Nat, ck = T.falseStack + k ∧ D < k ∧ (k : CInt) ≤ S1.assigned - T.falseStack ∧
      S1.assigned - T.falseStack < trailLen T ∧
      (∀ m : Nat, k ≤ m → (m : CInt) < S1.assigned - T.falseStack → ¬ Marked T S1 m) ∧
      S1.ld (S1.false + S1.ld (ck - 1)) = flag S1 (trailAt T (k - 1)) ∧
      S1.ld (S1.reason + abs (S1.ld (ck - 1))) = reasonOf T (trailAt T (k - 1)) := by
  intro S1
  have hrs1 := hres.1.setAssigned (S0.assigned - 1)
  obtain ⟨hA1, hlt, -, -, -, -⟩ := hres.reads ctx
  have hA : S1.assigned - T.falseStack < trailLen T := by
    show S0.assigned - 1 - T.falseStack < _
    have : S0.assigned - 1 = T.falseStack + ((a - 1 : Nat) : CInt) := hA1
    omega
  obtain ⟨k, hck, hDk, hkj, hnm, -, hfl, hrd⟩ := CheckInv.reads ctx hrs1.low hrs1.fields.shape hA hinv
  exact ⟨k, hck, hDk, hkj, hA, hnm, hfl, hrd⟩

/-- C:108: the check loop meets another MARK. -/
theorem vc_check_mark (ctx : ACtx input T db vs D) {S0 : solver} {a : Nat} (hres : ResInv input T D S0 a)
    {g : Bool} {ck : Ptr} (hinv : g = false ∧ CheckInv T D ({ S0 with assigned := S0.assigned - 1 } : solver) ck)
    (hm : ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).false +
      ({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck - 1)) = MARK) :
    CheckOut T D ({ S0 with assigned := S0.assigned - 1 } : solver) g := by
  obtain ⟨k, -, hDk, hkj, -, -, hfl, -⟩ := check_reads ctx hres hinv.2
  rw [hfl] at hm
  rw [hinv.1]; exact CheckInv.found hDk hkj hm

/-- C:109: the check loop reaches the decision: `goto build`. -/
theorem vc_check_dec (ctx : ACtx input T db vs D) {S0 : solver} {a : Nat} (hres : ResInv input T D S0 a)
    {g : Bool} {ck : Ptr} (hinv : g = false ∧ CheckInv T D ({ S0 with assigned := S0.assigned - 1 } : solver) ck)
    (hm : ¬ ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).false +
      ({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck - 1)) = MARK)
    (hz : ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).reason +
      abs (({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck - 1))) = 0) :
    CheckOut T D ({ S0 with assigned := S0.assigned - 1 } : solver) true := by
  obtain ⟨k, -, hDk, hkj, hA, hnm, hfl, hrd⟩ := check_reads ctx hres hinv.2
  rw [hfl] at hm; rw [hrd] at hz
  exact CheckInv.uip ctx hDk hnm hA hkj hm hz

/-- C:108–109: the check loop moves one position down. -/
theorem vc_check_next (ctx : ACtx input T db vs D) {S0 : solver} {a : Nat} (hres : ResInv input T D S0 a)
    {g : Bool} {ck : Ptr} (hinv : g = false ∧ CheckInv T D ({ S0 with assigned := S0.assigned - 1 } : solver) ck)
    (hm : ¬ ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).false +
      ({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck - 1)) = MARK)
    (hz : ¬ ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).reason +
      abs (({ S0 with assigned := S0.assigned - 1 } : solver).ld (ck - 1))) = 0) :
    (ck - 1 - T.falseStack).toNat < (ck - T.falseStack).toNat ∧
      g = false ∧ CheckInv T D ({ S0 with assigned := S0.assigned - 1 } : solver) (ck - 1) := by
  obtain ⟨k, hck, hDk, hkj, hA, hnm, hfl, hrd⟩ := check_reads ctx hres hinv.2
  rw [hfl] at hm; rw [hrd] at hz
  have := CheckInv.step ctx hDk hnm hkj hA hm hz
  subst hck
  exact ⟨by omega, hinv.1, by rw [show T.falseStack + (k : CInt) - 1 = T.falseStack + k - 1 by omega]; exact this⟩

/-- C:107: the check loop starts at the top position. -/
theorem vc_check_start (ctx : ACtx input T db vs D) {S0 : solver} {a : Nat} (hres : ResInv input T D S0 a)
    (hnz : ¬ ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).reason +
      abs (({ S0 with assigned := S0.assigned - 1 } : solver).ld ({ S0 with assigned := S0.assigned - 1 } : solver).assigned)) = 0) :
    CheckInv T D ({ S0 with assigned := S0.assigned - 1 } : solver) ({ S0 with assigned := S0.assigned - 1 } : solver).assigned := by
  rw [(hres.reads ctx).2.2.2.2.1] at hnz
  exact hres.check_init ctx hnz

/-- C:109–110: leaving both loops at the first UIP. -/
theorem vc_uip (ctx : ACtx input T db vs D) {S0 : solver} {a : Nat} (hres : ResInv input T D S0 a)
    (hm : ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).false +
      ({ S0 with assigned := S0.assigned - 1 } : solver).ld ({ S0 with assigned := S0.assigned - 1 } : solver).assigned) = MARK)
    {g : Bool} (hc : CheckOut T D ({ S0 with assigned := S0.assigned - 1 } : solver) g) (hg : g = true) :
    ∃ u, BuildStart input T D ({ S0 with assigned := S0.assigned - 1 } : solver) u := by
  rw [(hres.reads ctx).2.2.2.2.2] at hm
  subst hg
  exact ⟨_, hres.uip ctx hm hc⟩

/-- C:110: the reason bump starts at the reason's literal 1. -/
theorem vc_rbump_start (ctx : ACtx input T db vs D) {S0 : solver} {a : Nat} (hres : ResInv input T D S0 a)
    (hnz : ¬ ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).reason +
      abs (({ S0 with assigned := S0.assigned - 1 } : solver).ld ({ S0 with assigned := S0.assigned - 1 } : solver).assigned)) = 0) :
    RBump T db ({ S0 with assigned := S0.assigned - 1 } : solver) ({ S0 with assigned := S0.assigned - 1 } : solver)
      (({ S0 with assigned := S0.assigned - 1 } : solver).ld
        (({ S0 with assigned := S0.assigned - 1 } : solver).reason +
          abs (({ S0 with assigned := S0.assigned - 1 } : solver).ld ({ S0 with assigned := S0.assigned - 1 } : solver).assigned))) := by
  rw [(hres.reads ctx).2.2.2.2.1] at hnz
  exact RBump.init ctx hres hnz

/-- C:111–113: after bumping the reason, unassign the top literal. -/
theorem vc_resolve (ctx : ACtx input T db vs D) {S0 S2 : solver} {a : Nat} {cl : Ptr} (hres : ResInv input T D S0 a)
    (hm : ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).false +
      ({ S0 with assigned := S0.assigned - 1 } : solver).ld ({ S0 with assigned := S0.assigned - 1 } : solver).assigned) = MARK)
    {g : Bool} (hc : CheckOut T D ({ S0 with assigned := S0.assigned - 1 } : solver) g) (hg : g = false)
    (hb : RBump T db ({ S0 with assigned := S0.assigned - 1 } : solver) S2 cl ∧ S2.ld cl = 0) :
    ((unassign S2 (S2.ld S2.assigned)).assigned - T.falseStack).toNat < (S0.assigned - T.falseStack).toNat ∧
      g = false ∧ ∃ a', ResInv input T D (unassign S2 (S2.ld S2.assigned)) a' := by
  rw [(hres.reads ctx).2.2.2.2.2] at hm
  subst hg
  obtain ⟨h1, h2⟩ := hres.resolve ctx hm hc hb.1 hb.2
  exact ⟨h2, rfl, _, h1⟩

/-- C:113: a top literal without MARK is unassigned. -/
theorem vc_skip (ctx : ACtx input T db vs D) {S0 : solver} {a : Nat} (hres : ResInv input T D S0 a) {g : Bool}
    (hg : g = false)
    (hnz : ¬ ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).reason +
      abs (({ S0 with assigned := S0.assigned - 1 } : solver).ld ({ S0 with assigned := S0.assigned - 1 } : solver).assigned)) = 0)
    (hm : ¬ ({ S0 with assigned := S0.assigned - 1 } : solver).ld (({ S0 with assigned := S0.assigned - 1 } : solver).false +
      ({ S0 with assigned := S0.assigned - 1 } : solver).ld ({ S0 with assigned := S0.assigned - 1 } : solver).assigned) = MARK) :
    ((unassign ({ S0 with assigned := S0.assigned - 1 } : solver)
        (({ S0 with assigned := S0.assigned - 1 } : solver).ld ({ S0 with assigned := S0.assigned - 1 } : solver).assigned)).assigned -
          T.falseStack).toNat < (S0.assigned - T.falseStack).toNat ∧
      g = false ∧ ∃ a', ResInv input T D (unassign ({ S0 with assigned := S0.assigned - 1 } : solver)
        (({ S0 with assigned := S0.assigned - 1 } : solver).ld ({ S0 with assigned := S0.assigned - 1 } : solver).assigned)) a' := by
  rw [(hres.reads ctx).2.2.2.2.1] at hnz
  rw [(hres.reads ctx).2.2.2.2.2] at hm
  obtain ⟨h1, h2⟩ := hres.skip ctx hm hnz
  exact ⟨h2, hg, _, h1⟩

end VCs2

end MicrosatLean.Faithful.Verification
