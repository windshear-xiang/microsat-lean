import MicrosatLean.Faithful.Verification.AnalyzeResolve

/-!
# Minimization, backjump and unassignment in `analyze` (C:115–130)

One iteration of the minimization loop (C:116–121, with `implied`), of the unassign loop
(C:127–128), and the final facts: the collected clause is entailed and new, and the state
meets the `Analyzed` contract.
-/

namespace MicrosatLean.Faithful.Verification

section Build
variable {input : Input} {T : solver} {db : Records} {vs : List CInt} {D : Nat}

/-- What one step of the minimization loop (C:117–118) leaves before the flag reset: the
state `S2` and the collected positions `ps2`. -/
structure Collected (input : Input) (T : solver) (D : Nat) (M : Nat → Prop) (u j : Nat) (ps : List Nat)
    (S S2 : solver) (ps2 : List Nat) : Prop where
  fields : AFields T S2
  low : SameLow T S2
  model : ∀ q, 0 ≤ q → q ≤ T.nVars → S2.ld q = T.ld q
  order : ∃ vs, OrderList S2 vs
  assigned : S2.assigned = S.assigned
  processed : S2.processed = S.processed
  cache : Cache input T S2 M j
  marks : ∀ i < j, M i → Marked T S2 i
  flags : ∀ l, -T.nVars ≤ l → l ≤ T.nVars → (∀ i ≤ j, l ≠ trailAt T i) → flag S2 l = flag S l
  noImp : NoImp T S2 D u
  buffer : ∀ m (h : m < ps2.length), S2.ld (S2.buffer + m) = trailAt T ps2[m]
  cover : M j → j ∈ ps2 ∨ Imp input T M j
  shape : ps2 = ps ∨ (ps2 = ps ++ [j] ∧ M j)
  first : j = u → ps = [] → ps2 = [u]

/-- C:117–118: the collect step, from the three ways it can go. -/
theorem BState.collect (ctx : ACtx input T db vs D) {Sb : solver} {u j : Nat} {ps : List Nat} {S : solver}
    (hst : BuildStart input T D Sb u) (h : BState input T D (MarksAt T Sb u) u (j + 1) ps S)
    {S2 : solver} {ps2 : List Nat}
    (hA : (¬ Marked T S j ∧ S2 = S ∧ ps2 = ps) ∨
      (Marked T S j ∧ ∃ r', implied S (trailAt T j) = some (S2, r') ∧ r' ≠ 0 ∧ ps2 = ps) ∨
      (Marked T S j ∧ ∃ S', implied S (trailAt T j) = some (S', 0) ∧
        S2 = S'.st (S'.buffer + ps.length) (trailAt T j) ∧ ps2 = ps ++ [j])) :
    Collected input T D (MarksAt T Sb u) u j ps S S2 ps2 := by
  have hn := ctx.num
  have hu : u < trailLen T := hst.2.2.2.1
  have hju : j ≤ u := by have := h.k_le; omega
  have hjt : j < trailLen T := by omega
  have hx := ctx.lit hjt
  have hS := h.fields.shape
  have hl := ctx.layout h.fields h.low
  have hlen : ps.length ≤ u + 1 - (j + 1) := by
    have hnd : ps.Nodup := h.sorted.imp (fun hab => Nat.ne_of_gt hab)
    have hsub : ps ⊆ (List.range' (j + 1) (u + 1 - (j + 1))) := fun q hq => by
      have := h.ps_mem q hq; rw [List.mem_range'_1]; omega
    have := hnd.length_le_of_subset hsub
    rwa [List.length_range'] at this
  have hMj : Marked T S j → MarksAt T Sb u j := fun hm => by
    rcases (h.cache j (by omega)).2 (fun hr => by
      have := (h.cache j (by omega)).1 hr; unfold Marked at hm; rw [hm] at this; exact absurd this (by decide))
      with e | ⟨-, e⟩ | e | ⟨e, -⟩
    · unfold Marked at hm; rw [hm] at e; exact absurd e (by decide)
    · exact e
    · unfold Marked at hm; rw [hm] at e; exact absurd e (by decide)
    · unfold Marked at hm; rw [hm] at e; exact absurd e (by decide)
  have hpsnil : j = u → ps = [] := fun e => by
    cases ps with
    | nil => rfl
    | cons q _ => have := h.ps_mem q (by simp); omega
  have cache_lt : ∀ {S' : solver}, Cache input T S' (MarksAt T Sb u) (j + 1) → Cache input T S' (MarksAt T Sb u) j :=
    fun hc i hi => hc i (by omega)
  -- the facts shared by the two cases that call `implied`
  have impl : ∀ {S' : solver} {r' : CInt}, Marked T S j → implied S (trailAt T j) = some (S', r') →
      AFields T S' ∧ SameLow T S' ∧ (∀ q, 0 ≤ q → q < 6 * T.nVars + 5 → S'.ld q = S.ld q) ∧
      Cache input T S' (MarksAt T Sb u) (j + 1) ∧ (∀ i < j, MarksAt T Sb u i → Marked T S' i) ∧
      (∀ l, -T.nVars ≤ l → l ≤ T.nVars → (∀ i ≤ j, l ≠ trailAt T i) → flag S' l = flag S l) ∧
      NoImp T S' D u ∧ (r' ≠ 0 → Imp input T (MarksAt T Sb u) j) ∧ (j = u → r' = 0) ∧
      SameShape S S' ∧ S'.assigned = S.assigned ∧ S'.processed = S.processed ∧ S'.head = S.head := by
    intro S' r' hm hi
    obtain ⟨S'', r'', he, ⟨DB, hdb⟩, hcells, hcache, hmarks, himp, hnoimp, huip⟩ :=
      implied_spec ctx.core ctx.dec h.low hjt (h.cache.mono (by omega))
    rw [hi] at he
    obtain ⟨rfl, rfl⟩ := Option.some.inj he |> fun e => Prod.mk.inj e
    have hsh : SameShape S S' := by rw [hdb]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    have low_same : ∀ q, 0 ≤ q → q < 6 * T.nVars + 5 → S'.ld q = S.ld q := fun q h0 h1 =>
      hcells q h0 fun i hi _ => by
        have := ctx.lit (show i < trailLen T by omega); rw [hS.false]; omega
    refine ⟨?_, ⟨hS.trans hsh, fun q h1 h2 => by rw [low_same q (by omega) (by omega)]; exact h.low.mid q h1 h2,
      fun q h1 => ?_⟩, low_same, hcache _ h.cache, fun i hi hmi => ?_, fun l h1 h2 hne => ?_,
      hnoimp u (by omega) h.noImp, himp, fun e => ?_, hsh, by rw [hdb], by rw [hdb], by rw [hdb]⟩
    · rw [hdb]; obtain ⟨_, a, p, hd, r, nc, fa, sl, rfl⟩ := h.fields; exact ⟨DB, a, p, hd, r, nc, fa, sl, rfl⟩
    · rw [hcells q (by omega) fun i hi _ => by have := ctx.lit (show i < trailLen T by omega); rw [hS.false]; omega]
      exact h.low.high q h1
    · exact hmarks i (by omega) (h.marks i (by omega) hmi) hi
    · simp only [flag, hsh.false]
      exact hcells _ (by rw [hS.false]; omega) fun i hi _ => by
        intro he; exact hne i hi (by rw [hS.false] at he; omega)
    · subst e
      refine huip hst.2.2.1 (h.noImp.mono (Nat.le_refl _)) ?_
      unfold Marked at hm; rw [hm]; decide
  rcases hA with ⟨hnm, rfl, rfl⟩ | ⟨hm, r', hi, hr', rfl⟩ | ⟨hm, S', hi, rfl, rfl⟩
  · refine ⟨h.fields, h.low, h.model, h.order, rfl, rfl, cache_lt h.cache, fun i hi hmi => h.marks i (by omega) hmi,
      fun l _ _ _ => rfl, h.noImp, h.buffer, fun hmj => absurd (h.marks j (by omega) hmj) hnm, Or.inl rfl,
      fun e hp => ?_⟩
    subst e
    exact absurd (h.marks j (by omega) ⟨Nat.le_refl _, hst.2.2.2.2.2.1⟩) hnm
  · obtain ⟨hf, hlw, hlow, hc, hmk, hfl, hni, himp, huip, hsh, hA', hP', hH'⟩ := impl hm hi
    obtain ⟨vs0, ho⟩ := h.order
    have hb := hS.buffer; have hnv := hS.nVars
    refine ⟨hf, hlw, fun q h1 h2 => by rw [hlow q h1 (by omega)]; exact h.model q h1 h2,
      ⟨vs0, ho.frame hl hsh hH' fun q h1 h2 => hlow q (by omega) (by omega)⟩,
      hA', hP', cache_lt hc, hmk, hfl, hni, fun m hm' => by rw [hsh.buffer, hlow _ (by omega) (by omega)]; exact h.buffer m hm',
      fun _ => Or.inr (himp hr'), Or.inl rfl, fun e _ => absurd (huip e) hr'⟩
  · obtain ⟨hf, hlw, hlow, hc, hmk, hfl, hni, himp, huip, hsh, hA', hP', hH'⟩ := impl hm hi
    obtain ⟨vs0, ho⟩ := h.order
    have hb := hS.buffer; have hnv := hS.nVars; have hfa := hS.false
    have hsh' := hS.trans hsh
    have hlen' : (ps.length : CInt) ≤ T.nVars := by omega
    have hw : Writable T (S'.buffer + ps.length) := by
      rw [hsh'.buffer]; exact ctx.writable_buffer (by omega) hlen'
    have hq0 : 0 ≤ S'.buffer + ps.length := by rw [hsh'.buffer]; omega
    have wr : ∀ q, 0 ≤ q → q ≠ S'.buffer + ps.length →
        (S'.st (S'.buffer + ps.length) (trailAt T j)).ld q = S'.ld q := fun q h0 hne => by
      rw [ld_st _ _ hq0 h0, if_neg hne]
    have fl : ∀ l, -T.nVars ≤ l → l ≤ T.nVars →
        flag (S'.st (S'.buffer + ps.length) (trailAt T j)) l = flag S' l := fun l h1 h2 => by
      simp only [flag, st_false]; exact wr _ (by rw [hsh'.false]; omega) (by rw [hsh'.false, hsh'.buffer]; omega)
    have flt : ∀ i < trailLen T, flag (S'.st (S'.buffer + ps.length) (trailAt T j)) (trailAt T i) =
        flag S' (trailAt T i) := fun i hi => fl _ (ctx.lit hi).2.1 (ctx.lit hi).2.2
    refine ⟨hf.st _ _, hlw.st hw _, fun q h1 h2 => ?_, ⟨vs0, ?_⟩, by simp [hA'], by simp [hP'],
      fun i hi => ?_, fun i hi hmi => ?_, fun l h1 h2 hne => by rw [fl l h1 h2]; exact hfl l h1 h2 hne,
      fun i h1 h2 => ?_, fun m hm' => ?_, fun _ => Or.inl (by simp), Or.inr ⟨rfl, hMj hm⟩,
      fun e hp => by subst hp; subst e; rfl⟩
    · rw [wr q h1 (by rw [hsh'.buffer]; omega), hlow q h1 (by omega)]; exact h.model q h1 h2
    · refine ho.frame hl (hsh.trans (SameShape.st _ _ _)) (by simp [hH']) fun q h1 h2 => ?_
      rw [wr q (by omega) (by rw [hsh'.buffer]; omega), hlow q (by omega) (by omega)]
    · have := hc i (by omega); unfold Marked at *; rw [flt i (by omega)]; exact this
    · have := hmk i hi hmi; unfold Marked at *; rw [flt i (by omega)]; exact this
    · rw [flt i (by omega)]; exact hni i h1 h2
    · rcases Nat.lt_or_ge m ps.length with h1 | h1
      · rw [st_buffer, wr _ (by rw [hsh'.buffer]; omega) (by omega), hsh.buffer, hlow _ (by omega) (by omega),
          List.getElem_append_left h1]
        exact h.buffer m h1
      · have : m = ps.length := by simp at hm'; omega
        subst this
        rw [st_buffer, ld_st_self _ _ hq0]; simp

/-- Index 1 of an append whose first part has two elements. -/
theorem getElem!_one_append_left {l m : List Nat} (h : 2 ≤ l.length) : (l ++ m)[1]! = l[1]! := by
  rw [getElem!_pos (l ++ m) 1 (by simp; omega), getElem!_pos l 1 (by omega), List.getElem_append_left]

/-- Index 1 after appending to a singleton. -/
theorem getElem!_one_append_single {l : List Nat} (h : l.length = 1) (j : Nat) : (l ++ [j])[1]! = j := by
  rw [getElem!_pos (l ++ [j]) 1 (by simp; omega), List.getElem_append_right (by omega)]
  simp [h]

/-- C:119–121: the backjump update and the flag reset finish one step of the loop. -/
theorem BState.step (ctx : ACtx input T db vs D) {Sb : solver} {u j : Nat} {ps : List Nat} {S : solver}
    (hst : BuildStart input T D Sb u) (h : BState input T D (MarksAt T Sb u) u (j + 1) ps S)
    (hj : forcedPos T ≤ j) {S2 : solver} {ps2 : List Nat}
    (hc : Collected input T D (MarksAt T Sb u) u j ps S S2 ps2) {S3 : solver}
    (hB : (IsDecision T j ∧ ps2.length = 1 ∧ S3 = ({ S2 with processed := T.falseStack + j } : solver)) ∨
      (¬ (IsDecision T j ∧ ps2.length = 1) ∧ S3 = S2)) :
    BState input T D (MarksAt T Sb u) u j ps2 (S3.st (S3.false + trailAt T j) 1) := by
  have hn := ctx.num
  have hu : u < trailLen T := hst.2.2.2.1
  have hju : j ≤ u := by have := h.k_le; omega
  have hjt : j < trailLen T := by omega
  have hx := ctx.lit hjt
  -- the state after the backjump update
  have h3 : AFields T S3 ∧ SameLow T S3 ∧ (∀ q, S3.ld q = S2.ld q) ∧ (∃ vs, OrderList S3 vs) ∧
      S3.assigned = S2.assigned ∧ S3.false = S2.false ∧ S3.buffer = S2.buffer ∧
      ((IsDecision T j ∧ ps2.length = 1 ∧ processedPos S3 = j) ∨
        (¬ (IsDecision T j ∧ ps2.length = 1) ∧ processedPos S3 = processedPos S)) := by
    rcases hB with ⟨hd, hl1, rfl⟩ | ⟨hnd, rfl⟩
    · obtain ⟨vs2, o⟩ := hc.order
      have hs := hc.low.shape
      refine ⟨hc.fields.upd _ _ _ _ _ _ _ _, ⟨⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6, hs.7, hs.8, hs.9⟩,
        hc.low.mid, hc.low.high⟩, fun _ => rfl, ⟨vs2, o.1.congr fun _ _ => rfl, o.2, o.3, o.4⟩, rfl, rfl, rfl,
        Or.inl ⟨hd, hl1, ?_⟩⟩
      have := hc.low.shape.falseStack; simp only [processedPos]; omega
    · exact ⟨hc.fields, hc.low, fun _ => rfl, hc.order, rfl, rfl, rfl, Or.inr ⟨hnd, by
        simp only [processedPos, hc.processed, hc.low.shape.falseStack, h.fields.shape.falseStack]⟩⟩
  obtain ⟨hf3, hl3, hld3, ⟨vs3, ho3⟩, hA3, hF3, hBf3, hpp⟩ := h3
  have hs3 := hl3.shape
  have hw : Writable T (S3.false + trailAt T j) := by rw [hs3.false]; exact ctx.writable_flag ⟨hx.2.1, hx.2.2⟩
  have hq0 : 0 ≤ S3.false + trailAt T j := by rw [hs3.false]; omega
  have flag4 : ∀ l, -T.nVars ≤ l → l ≤ T.nVars → l ≠ trailAt T j →
      flag (S3.st (S3.false + trailAt T j) 1) l = flag S2 l := fun l h1 h2 hne => by
    rw [flag_st_ne ctx hs3 ⟨hx.2.1, hx.2.2⟩ ⟨h1, h2⟩ hne]; simp only [flag, hld3, hF3]
  have flag4j : flag (S3.st (S3.false + trailAt T j) 1) (trailAt T j) = 1 := by
    simp only [flag, st_false]; exact ld_st_self _ _ hq0
  have ne_of : ∀ i < trailLen T, i ≠ j → trailAt T i ≠ trailAt T j := fun i hi hne he => hne (ctx.pos_eq hi hjt he)
  have flagT : ∀ i < trailLen T, i ≠ j → flag (S3.st (S3.false + trailAt T j) 1) (trailAt T i) = flag S2 (trailAt T i) :=
    fun i hi hne => flag4 _ (ctx.lit hi).2.1 (ctx.lit hi).2.2 (ne_of i hi hne)
  have flagS : ∀ i < trailLen T, j < i → flag S2 (trailAt T i) = flag S (trailAt T i) := fun i hi hji =>
    hc.flags _ (ctx.lit hi).2.1 (ctx.lit hi).2.2 fun i' hi' he => by
      have := ctx.pos_eq hi (by omega) he; omega
  have ld4 : ∀ q, 0 ≤ q → q ≠ S3.false + trailAt T j → (S3.st (S3.false + trailAt T j) 1).ld q = S2.ld q :=
    fun q h0 hne => by rw [ld_st _ _ hq0 h0, if_neg hne, hld3]
  have hpp4 : processedPos (S3.st (S3.false + trailAt T j) 1) = processedPos S3 := by simp [processedPos]
  -- the collected positions
  have hmem2 : ∀ q ∈ ps2, j ≤ q ∧ q ≤ u ∧ MarksAt T Sb u q := by
    intro q hq
    rcases hc.shape with rfl | ⟨rfl, hMj⟩
    · have := h.ps_mem q hq; exact ⟨by omega, this.2.1, this.2.2⟩
    · rcases List.mem_append.mp hq with hq | hq
      · have := h.ps_mem q hq; exact ⟨by omega, this.2.1, this.2.2⟩
      · simp at hq; subst hq; exact ⟨Nat.le_refl _, hju, hMj⟩
  have hsorted : ps2.Pairwise (· > ·) := by
    rcases hc.shape with rfl | ⟨rfl, -⟩
    · exact h.sorted
    · refine List.pairwise_append.mpr ⟨h.sorted, by simp, fun a ha b hb => ?_⟩
      simp at hb; subst hb; have := h.ps_mem a ha; omega
  have hpsnil : j = u → ps = [] := fun e => by
    cases ps with
    | nil => rfl
    | cons q _ => have := h.ps_mem q (by simp); omega
  have hhead : ps2.head? = some u := by
    rcases Nat.lt_or_ge j u with hlt | hge
    · have := h.head (by omega)
      rcases hc.shape with rfl | ⟨rfl, -⟩
      · exact this
      · cases ps with
        | nil => simp at this
        | cons q _ => simpa using this
    · have e : j = u := by omega
      rw [hc.first e (hpsnil e)]; rfl
  have hne2 : ps2 ≠ [] := fun e => by rw [e] at hhead; simp at hhead
  have hlen2 : ps2.length ≤ u + 1 - j := by
    have hnd : ps2.Nodup := hsorted.imp (fun hab => Nat.ne_of_gt hab)
    have hsub : ps2 ⊆ (List.range' j (u + 1 - j)) := fun q hq => by
      have := hmem2 q hq; rw [List.mem_range'_1]; omega
    have := hnd.length_le_of_subset hsub
    rwa [List.length_range'] at this
  have hlen1 : 1 ≤ ps2.length := by
    cases ps2 with
    | nil => exact absurd rfl hne2
    | cons _ _ => simp
  refine ⟨hf3.st _ _, hl3.st hw _, fun q h1 h2 => ?_, ⟨vs3, ?_⟩, by simp [hA3, hc.assigned, h.assigned], hj,
    by omega, fun i hi => ?_, fun i hi hmi => ?_, fun i h1 h2 => ?_, fun i h1 h2 => ?_, fun l hl ho => ?_, ?_,
    fun i h1 h2 => ?_, fun m hm => ?_, hmem2, hsorted, fun i h1 h2 hmi => ?_, fun _ => hhead, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_⟩
  · rw [ld4 q h1 (by rw [hs3.false]; omega)]; exact hc.model q h1 h2
  · refine ho3.frame (ctx.layout hf3 hl3) (SameShape.st _ _ _) (by simp) fun q h1 h2 => ?_
    rw [ld4 q (by omega) (by rw [hs3.false]; rw [hs3.nVars] at h2; omega), ← hld3]
  · have := hc.cache i hi; unfold Marked at *
    rw [flagT i (by omega) (by omega)]; exact this
  · have := hc.marks i hi hmi; unfold Marked at *; rw [flagT i (by omega) (by omega)]; exact this
  · rcases Nat.eq_or_lt_of_le h1 with e | hlt
    · subst e; exact flag4j
    · rw [flagT i (by omega) (by omega), flagS i (by omega) hlt]; exact h.done i hlt h2
  · rw [flagT i h2 (by omega), flagS i h2 (by omega)]; exact h.above i h1 h2
  · have hl' := inRange_iff.mp hl
    rw [flag4 l hl'.2.1 hl'.2.2 (fun e => ho j hjt e.symm),
      hc.flags l hl'.2.1 hl'.2.2 (fun i hi e => ho i (by omega) e.symm)]
    exact h.off l hl ho
  · rw [flag4 0 (by omega) (by omega) (fun e => hx.1 e.symm),
      hc.flags 0 (by omega) (by omega) (fun i hi e => (ctx.lit (show i < trailLen T by omega)).1 e.symm)]
    exact h.zero
  · by_cases e : i = j
    · subst e; rw [flag4j]; exact ⟨by decide, by decide⟩
    · rw [flagT i (by omega) e]; exact hc.noImp i h1 h2
  · rw [st_buffer, ld4 _ (by rw [hBf3, hc.low.shape.buffer]; omega)
      (by rw [hBf3, hc.low.shape.buffer, hs3.false]; omega), hBf3]
    exact hc.buffer m hm
  · rcases Nat.eq_or_lt_of_le h1 with e | hlt
    · subst e; exact hc.cover hmi
    · rcases h.cover i hlt h2 hmi with hm | hm
      · left; rcases hc.shape with rfl | ⟨rfl, -⟩
        · exact hm
        · exact List.mem_append_left _ hm
      · exact Or.inr hm
  -- B_le
  · rw [hpp4]; rcases hpp with ⟨-, -, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact hju
    · exact h.B_le
  -- B_ge
  · rw [hpp4]; rcases hpp with ⟨-, -, e⟩ | ⟨-, e⟩ <;> rw [e]
    · omega
    · have := h.B_ge; omega
  -- B_ge'
  · intro _; rw [hpp4]; rcases hpp with ⟨-, -, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact Nat.le_refl _
    · have := h.B_ge; omega
  -- proc_ge
  · simp only [st_processed]
    rcases hB with ⟨-, -, rfl⟩ | ⟨-, rfl⟩
    · show T.falseStack ≤ T.falseStack + (j : CInt); omega
    · rw [hc.processed]; exact h.proc_ge
  -- B_dec
  · rw [hpp4]; rcases hpp with ⟨hd, -, e⟩ | ⟨-, e⟩ <;> rw [e]
    · exact Or.inr hd
    · exact h.B_dec
  -- B_low
  · intro hjD
    rw [hpp4]
    rcases Nat.eq_or_lt_of_le hjD with e | hlt
    · -- at the last decision only the first UIP is collected
      have hone : ps2.length = 1 := by
        have hall : ∀ q ∈ ps2, q = u := fun q hq => by
          obtain ⟨h1, h2, -, hmq⟩ := hmem2 q hq
          refine Classical.byContradiction fun hne => hst.2.2.2.2.2.2 q (by omega) (by omega) hmq
        cases ps2 with
        | nil => exact absurd rfl hne2
        | cons a t =>
          cases t with
          | nil => rfl
          | cons b t' =>
            have ha := hall a (by simp); have hb := hall b (by simp)
            have := List.rel_of_pairwise_cons hsorted (by simp : b ∈ b :: t'); omega
      rcases hpp with ⟨hd, -, e'⟩ | ⟨hnd, -⟩
      · rw [e']; exact ⟨hd, by omega⟩
      · exact absurd ⟨by rw [e]; exact ctx.dec, hone⟩ hnd
    · rcases hpp with ⟨hd, -, e'⟩ | ⟨-, e'⟩ <;> rw [e']
      · exact ⟨hd, by omega⟩
      · exact h.B_low (by omega)
  -- tail_lt
  · intro q hq
    rw [hpp4]
    rcases hpp with ⟨-, hl1, -⟩ | ⟨-, e'⟩
    · cases ps2 with
      | nil => simp at hq
      | cons a t => simp at hl1; subst hl1; simp at hq
    · rw [e']
      rcases hc.shape with rfl | ⟨rfl, -⟩
      · exact h.tail_lt q hq
      · cases ps with
        | nil => simp at hq
        | cons a t =>
          have hqa : q ∈ t ++ [j] := by simpa using hq
          rcases List.mem_append.mp hqa with hq' | hq'
          · exact h.tail_lt q (by simpa using hq')
          · simp at hq'; subst hq'
            have := h.ps_mem a (by simp)
            have := h.B_ge' (by omega); omega
  -- gap
  · intro d hd hdlt
    rw [hpp4] at hdlt
    rcases hpp with ⟨-, hl1, e'⟩ | ⟨hnd, e'⟩
    · rw [e'] at hdlt; exact ⟨fun h2 => by omega, fun _ hjd => by omega⟩
    · rw [e'] at hdlt
      have old := h.gap d hd hdlt
      refine ⟨fun h2 hlt => ?_, fun h1 hjd => ?_⟩
      · rcases hc.shape with rfl | ⟨rfl, -⟩
        · exact old.1 h2 hlt
        · rcases Nat.lt_or_ge ps.length 2 with hp | hp
          · have hp1 : ps.length = 1 := by simp at h2; omega
            rw [getElem!_one_append_single hp1] at hlt
            exact old.2 (by omega) (by omega)
          · rw [getElem!_one_append_left hp] at hlt; exact old.1 hp hlt
      · rcases Nat.eq_or_lt_of_le hjd with e | hlt
        · subst e
          exact hnd ⟨hd, by omega⟩
        · have : ps.length ≤ 1 := by
            rcases hc.shape with rfl | ⟨rfl, -⟩
            · exact h1
            · simp only [List.length_append, List.length_singleton] at h1; omega
          exact old.2 this (by omega)

/-- C:115–116: the minimization loop starts at the first UIP. -/
theorem BState.init (ctx : ACtx input T db vs D) {Sb : solver} {u : Nat} (hst : BuildStart input T D Sb u) :
    BState input T D (MarksAt T Sb u) u (u + 1) [] ({ Sb with processed := Sb.assigned } : solver) := by
  obtain ⟨hrs, hA, hDu, hu, -, hmu, hno⟩ := hst
  have hn := ctx.num
  have hs := hrs.low.shape
  obtain ⟨vs0, o⟩ := hrs.order
  have hpp : processedPos ({ Sb with processed := Sb.assigned } : solver) = u := by
    simp only [processedPos]; rw [hA, hs.falseStack]; omega
  refine ⟨hrs.fields.upd _ _ _ _ _ _ _ _, ⟨⟨hs.1, hs.2, hs.3, hs.4, hs.5, hs.6, hs.7, hs.8, hs.9⟩, hrs.low.mid,
    hrs.low.high⟩, hrs.model, ⟨vs0, o.1.congr fun _ _ => rfl, o.2, o.3, o.4⟩, hA,
    by have := ctx.forced_le; omega, Nat.le_refl _, fun i hi => ⟨hrs.root i hi, fun hr => ?_⟩,
    fun i hi hmi => hmi.2, fun i h1 h2 => by omega, hrs.above, hrs.off, hrs.zero, fun i h1 h2 => ?_,
    fun m hm => by simp at hm, fun q hq => by simp at hq, List.Pairwise.nil, fun i h1 h2 => by omega,
    fun h => by omega, by rw [hpp]; exact Nat.le_refl _, by rw [hpp]; omega, fun h => by omega,
    by show T.falseStack ≤ Sb.assigned; omega, Or.inl hpp,
    fun h => by omega,
    fun q hq => by simp at hq, fun d _ hd => ⟨fun h => by simp at h, fun _ h => by rw [hpp] at hd; omega⟩⟩
  · rcases hrs.level i hi hr with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl ⟨e, by omega, e⟩)
  · have hnr := ctx.not_root h1
    rcases hrs.level i (by omega) hnr with e | e
    · show flag Sb (trailAt T i) ≠ MARK ∧ flag Sb (trailAt T i) ≠ IMPLIED
      rw [e]; exact ⟨by decide, by decide⟩
    · exact absurd e (hno i h1 h2)

/-- One iteration of the minimization loop (C:117–121), in the form `mvcgen` produces: the
collect step (`S2`, `size2`), then the backjump update (`S3`), then the flag reset. -/
theorem vc_build (ctx : ACtx input T db vs D) {Sb S : solver} {size p : CInt}
    (h : BLoop input T D Sb S size p) (hp : p ≥ S.forced) {S2 : solver} {size2 : CInt}
    (hA : (¬ S.ld (S.false + S.ld p) = MARK ∧ S2 = S ∧ size2 = size) ∨
      (S.ld (S.false + S.ld p) = MARK ∧ ¬ ((implied S (S.ld p)).getD (default, 0)).2 = 0 ∧
        S2 = ((implied S (S.ld p)).getD (default, 0)).1 ∧ size2 = size) ∨
      (S.ld (S.false + S.ld p) = MARK ∧ ((implied S (S.ld p)).getD (default, 0)).2 = 0 ∧
        S2 = ((implied S (S.ld p)).getD (default, 0)).1.st (((implied S (S.ld p)).getD (default, 0)).1.buffer + size)
          (((implied S (S.ld p)).getD (default, 0)).1.ld p) ∧ size2 = size + 1))
    {S3 : solver}
    (hB : (S2.ld (S2.reason + abs (S2.ld p)) = 0 ∧ size2 = 1 ∧ S3 = ({ S2 with processed := p } : solver)) ∨
      (¬ (S2.ld (S2.reason + abs (S2.ld p)) = 0 ∧ size2 = 1) ∧ S3 = S2)) :
    BLoop input T D Sb (S3.st (S3.false + S3.ld p) 1) size2 (p - 1) ∧
      (p - 1 + 1 - T.forced).toNat < (p + 1 - T.forced).toNat := by
  obtain ⟨u, k, ps, hst, hb, hsz, hpk⟩ := h
  have hn := ctx.num
  have hs := hb.low.shape
  have hfp : S.forced = T.forced := hb.fields.eqs.2.1
  have hk : forcedPos T + 1 ≤ k := by rw [hfp] at hp; omega
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hu : u < trailLen T := hst.2.2.2.1
  have hjt : j < trailLen T := by have := hb.k_le; omega
  have hpj : p = T.falseStack + (j : Nat) := by push_cast at hpk; omega
  subst hpj
  have hrd : ∀ {S' : solver}, SameLow T S' → S'.ld (T.falseStack + (j : Nat)) = trailAt T j :=
    fun hl => hl.trail ctx hjt
  rw [hrd hb.low] at hA
  have hfl : S.ld (S.false + trailAt T j) = flag S (trailAt T j) := rfl
  rw [hfl] at hA
  obtain ⟨S', r', himp, ⟨DB, hdb⟩, hcells, -⟩ := implied_spec ctx.core ctx.dec hb.low hjt (hb.cache.mono (by omega))
  rw [himp] at hA
  simp only [Option.getD_some] at hA
  have hS'ld : S'.ld (T.falseStack + (j : Nat)) = trailAt T j := by
    rw [hcells _ (by omega) (fun i hi _ => by
      have := ctx.lit (show i < trailLen T by omega); rw [hs.false]; omega)]
    exact hrd hb.low
  have hcol : ∃ ps2, Collected input T D (MarksAt T Sb u) u j ps S S2 ps2 ∧ size2 = ps2.length := by
    rcases hA with ⟨hm, rfl, rfl⟩ | ⟨hm, hr, rfl, rfl⟩ | ⟨hm, hr, rfl, rfl⟩
    · exact ⟨ps, hb.collect ctx hst (Or.inl ⟨hm, rfl, rfl⟩), hsz⟩
    · exact ⟨ps, hb.collect ctx hst (Or.inr (Or.inl ⟨hm, r', himp, hr, rfl⟩)), hsz⟩
    · refine ⟨ps ++ [j], hb.collect ctx hst (Or.inr (Or.inr ⟨hm, S', by rw [himp, hr], ?_, rfl⟩)), ?_⟩
      · rw [hsz, hS'ld]
      · simp [hsz]
  obtain ⟨ps2, hcol, hsz2⟩ := hcol
  have hrd2 : S2.ld (T.falseStack + (j : Nat)) = trailAt T j := hrd hcol.low
  have hrs2 : S2.ld (S2.reason + abs (trailAt T j)) = reasonOf T (trailAt T j) := by
    rw [hcol.low.shape.reason]; exact hcol.low.reason ctx (ctx.lit hjt)
  rw [hrd2, hrs2] at hB
  have hB' : (IsDecision T j ∧ ps2.length = 1 ∧ S3 = ({ S2 with processed := T.falseStack + j } : solver)) ∨
      (¬ (IsDecision T j ∧ ps2.length = 1) ∧ S3 = S2) := by
    rcases hB with ⟨h1, h2, h3⟩ | ⟨h1, h3⟩
    · exact Or.inl ⟨h1, by omega, h3⟩
    · exact Or.inr ⟨fun ⟨e1, e2⟩ => h1 ⟨e1, by rw [hsz2, e2]; rfl⟩, h3⟩
  have hst3 := hb.step ctx hst (by omega) hcol hB'
  have hS3 : S3.ld (T.falseStack + (j : Nat)) = trailAt T j := by
    rcases hB' with ⟨-, -, rfl⟩ | ⟨-, rfl⟩ <;> exact hrd2
  rw [hS3]
  refine ⟨⟨u, j, ps2, hst, hst3, hsz2, by omega⟩, ?_⟩
  have : (T.forced : CInt) = T.falseStack + (forcedPos T : Nat) := by have := hn.2.2.2.2.2.2.2.2.2.2.2.2.2.2; omega
  omega

end Build

section Unassign
variable {input : Input} {T : solver} {db : Records} {vs : List CInt} {D : Nat}

/-- Moving `assigned` keeps `AFields`. -/
theorem AFields.setA {S : solver} (h : AFields T S) (v : CInt) : AFields T ({ S with assigned := v } : solver) := by
  obtain ⟨DB, _, p, hd, r, nc, fa, sl, rfl⟩ := h; exact ⟨DB, v, p, hd, r, nc, fa, sl, rfl⟩

/-- C:127: the unassign loop starts at `assigned`. -/
theorem UInv.init {Se : solver} {u : Nat} (hf : AFields T Se) (hA : Se.assigned = T.falseStack + u)
    (hB : processedPos Se ≤ u) : UInv T Se Se :=
  ⟨u, hf, rfl, rfl, hA, hB, by omega, fun q _ _ => rfl, fun i h1 h2 => by omega⟩

/-- C:127–128, one unassignment. -/
theorem UInv.step (ctx : ACtx input T db vs D) {Se S : solver} (hl : SameLow T Se)
    (hu : Se.assigned - T.falseStack < trailLen T) (hpr : T.falseStack ≤ Se.processed) (h : UInv T Se S)
    (hgt : S.assigned > S.processed) :
    UInv T Se ({ unassign S (S.ld S.assigned) with assigned := (unassign S (S.ld S.assigned)).assigned - 1 } : solver) ∧
      (({ unassign S (S.ld S.assigned) with assigned := (unassign S (S.ld S.assigned)).assigned - 1 } : solver).assigned -
        ({ unassign S (S.ld S.assigned) with assigned := (unassign S (S.ld S.assigned)).assigned - 1 } : solver).processed).toNat <
        (S.assigned - S.processed).toNat := by
  obtain ⟨a, hf, hP, hH, hA, hpa, haA, hcells, hflags⟩ := h
  have hn := ctx.num
  have hs := hl.shape
  have hsS := hf.shape
  have hpp : processedPos Se < a := by
    simp only [processedPos]; rw [hs.falseStack]; have := hgt; omega
  have hat : a < trailLen T := by omega
  have hx := ctx.lit hat
  have htr : S.ld S.assigned = trailAt T a := by
    rw [hA, hcells _ (by omega) (fun i h1 h2 => by
      have := ctx.lit (show i < trailLen T by omega); rw [hs.false]; omega)]
    exact hl.trail ctx hat
  rw [htr]
  have hfz : 0 ≤ S.false + trailAt T a := by rw [hsS.false]; omega
  have ld1 : ∀ q, 0 ≤ q → (unassign S (trailAt T a)).ld q = if q = S.false + trailAt T a then 0 else S.ld q :=
    fun q hq => ld_st _ _ hfz hq
  have hA1 : (unassign S (trailAt T a)).assigned = S.assigned := by simp [unassign]
  have hP1 : (unassign S (trailAt T a)).processed = S.processed := by simp [unassign]
  have hF1 : (unassign S (trailAt T a)).false = S.false := by simp [unassign]
  refine ⟨⟨a - 1, (hf.st _ _).setA _, by simp only; rw [hP1, hP], by simp [unassign, hH],
    by simp only; rw [hA1, hA]; omega, by omega,
    by omega, fun q hq hne => ?_, fun i h1 h2 => ?_⟩, ?_⟩
  · show (unassign S (trailAt T a)).ld q = _
    rw [ld1 q hq, if_neg (by rw [hsS.false, ← hs.false]; exact hne a (by omega) (by omega))]
    exact hcells q hq fun i h1 h2 => hne i (by omega) h2
  · show (unassign S (trailAt T a)).ld ((unassign S (trailAt T a)).false + trailAt T i) = 0
    have hix := ctx.lit (show i < trailLen T by omega)
    rw [hF1, ld1 _ (by rw [hsS.false]; omega)]
    by_cases e : i = a
    · subst e; simp
    · have hne : S.false + trailAt T i ≠ S.false + trailAt T a := fun he =>
        e (ctx.pos_eq (by omega) hat (by omega))
      rw [if_neg hne]; exact hflags i (by omega) h2
  · show ((unassign S (trailAt T a)).assigned - 1 - (unassign S (trailAt T a)).processed).toNat < _
    rw [hA1, hP1]; omega

/-- C:124: updating `fast` keeps `AFields`. -/
theorem AFields.setFast {S : solver} (h : AFields T S) (v : CInt) : AFields T ({ S with fast := v } : solver) := by
  obtain ⟨DB, a, p, hd, r, nc, _, sl, rfl⟩ := h; exact ⟨DB, a, p, hd, r, nc, v, sl, rfl⟩

/-- C:125: updating `slow` keeps `AFields`. -/
theorem AFields.setSlow {S : solver} (h : AFields T S) (v : CInt) : AFields T ({ S with slow := v } : solver) := by
  obtain ⟨DB, a, p, hd, r, nc, fa, _, rfl⟩ := h; exact ⟨DB, a, p, hd, r, nc, fa, v, rfl⟩

/-- What the minimization loop leaves (C:122), seen from `Se`, the state after C:124–125. -/
theorem BLoop.exit (ctx : ACtx input T db vs D) {Sb Se0 : solver} {size p : CInt}
    (h : BLoop input T D Sb Se0 size p ∧ p < Se0.forced) {Se : solver} (hf : AFields T Se0 → AFields T Se)
    (hsh : SameShape Se0 Se) (hld : ∀ q, Se.ld q = Se0.ld q) (hA : Se.assigned = Se0.assigned)
    (hP : Se.processed = Se0.processed) :
    ∃ u ps, BuildStart input T D Sb u ∧ BState input T D (MarksAt T Sb u) u (forcedPos T) ps Se0 ∧
      size = ps.length ∧ AFields T Se ∧ SameLow T Se ∧ Se.assigned = T.falseStack + u ∧
      Se.assigned - T.falseStack < trailLen T ∧ T.falseStack ≤ Se.processed ∧
      processedPos Se = processedPos Se0 := by
  obtain ⟨⟨u, k, ps, hst, hb, hsz, hpk⟩, hp⟩ := h
  have hn := ctx.num
  have hfp : Se0.forced = T.forced := hb.fields.eqs.2.1
  have hk : k = forcedPos T := by have := hb.k_ge; omega
  subst hk
  have hu := hst.2.2.2.1
  have hs := hb.low.shape
  refine ⟨u, ps, hst, hb, hsz, hf hb.fields, ⟨hs.trans hsh, fun q h1 h2 => by rw [hld]; exact hb.low.mid q h1 h2,
    fun q h1 => by rw [hld]; exact hb.low.high q h1⟩, by rw [hA]; exact hb.assigned, by rw [hA, hb.assigned]; omega,
    by rw [hP]; exact hb.proc_ge, by simp only [processedPos, hP, hsh.falseStack]⟩

end Unassign

section Final
variable {input : Input} {T : solver} {db : Records} {vs : List CInt} {D : Nat}

/-- The learned clause is entailed (C:117): the MARKs at `build` form an entailed clause,
and each MARK left out is implied by the MARKs below it. -/
theorem final_entailed (ctx : ACtx input T db vs D) {Sb : solver} {u : Nat} {ps : List Nat} {S : solver}
    (hst : BuildStart input T D Sb u) (hb : BState input T D (MarksAt T Sb u) u (forcedPos T) ps S) :
    input.Entails (ps.map (trailAt T)) := by
  intro asg hsat
  refine Classical.byContradiction fun hno => ?_
  have hnot : ∀ i, MarksAt T Sb u i → ¬ LitTrue asg (trailAt T i) := by
    intro i
    induction i using Nat.strongRecOn with
    | _ i ih =>
      intro hmi ht
      have hge : forcedPos T ≤ i := by
        refine Classical.byContradiction fun hlt => ?_
        have hroot := ctx.core.trail.forced_root i (by omega)
        have := hst.1.root i (by have := hmi.1; omega) hroot
        have hm := hmi.2; unfold Marked at hm; rw [hm] at this; exact absurd this (by decide)
      rcases hb.cover i hge hmi.1 hmi with hin | himp
      · exact hno ⟨trailAt T i, List.mem_map.mpr ⟨i, hin, rfl⟩, ht⟩
      · exact himp asg hsat (fun j hj hmj => ih j hj hmj) ht
  obtain ⟨i, hi, hmi, ht⟩ := hst.2.2.2.2.1 asg hsat
  exact hnot i ⟨by omega, hmi⟩ ht

/-- The learned clause is new (C:130): a clause of the database with the same literals
would have two literals false below the backjump point, or be a unit already true, against
the watched-literal invariant. -/
theorem final_new (ctx : ACtx input T db vs D) {P : Nat}
    (hwatched : ∀ s ∈ db.all, 2 ≤ s.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
      ∀ p < P, FalseAt T s.2[w]! p → ∃ q, FalseAt T (- s.2[o]!) q ∧ SameOrLowerLevel T p q)
    {L : List CInt} {B u : Nat} (hBP : B ≤ P) (hu : u < trailLen T) (hBu : B ≤ u)
    (hL0 : L.head? = some (trailAt T u)) (htail : ∀ l ∈ L.tail, ∃ j < B, trailAt T j = l) (hnd : L.Nodup) :
    ∀ s ∈ db.all, ¬ s.2.Perm L := by
  intro s hs hperm
  obtain ⟨x, t, rfl⟩ : ∃ x t, L = x :: t := by
    cases L with
    | nil => simp at hL0
    | cons x t => exact ⟨x, t, rfl⟩
  simp at hL0; subst hL0
  have onTrail : ∀ l ∈ trailAt T u :: t, ∃ j < trailLen T, trailAt T j = l := fun l hl => by
    rcases List.mem_cons.mp hl with rfl | hl
    · exact ⟨u, hu, rfl⟩
    · obtain ⟨j, hj, e⟩ := htail l hl; exact ⟨j, by omega, e⟩
  have negc : ∀ l ∈ trailAt T u :: t, ∀ q, ¬ FalseAt T (- l) q := fun l hl q hq => by
    obtain ⟨j, hj, rfl⟩ := onTrail l hl
    have e := ctx.pos_eq hq.1 hj (by
      have := hq.2
      have := ctx.core.trail.distinct q hq.1 j hj (by rw [this, abs_neg'])
      subst this; exact (ctx.lit hj).1 |> fun h0 => by omega)
    subst e
    have := hq.2; have := (ctx.lit hj).1; omega
  rcases t with _ | ⟨y, t'⟩
  · -- a unit clause: its literal is true at the root
    have hs1 : s.2 = [trailAt T u] := List.perm_singleton.mp hperm
    obtain ⟨i, hi, -, he⟩ := ctx.core.units s hs (by rw [hs1]; rfl)
    rw [hs1] at he
    exact negc (trailAt T u) (by simp) i ⟨hi, by rw [he]; rfl⟩
  · have hlen : 2 ≤ s.2.length := by rw [hperm.length_eq]; simp
    have hnds : s.2.Nodup := hperm.nodup_iff.mpr hnd
    have m0 : s.2[0]! ∈ trailAt T u :: y :: t' := hperm.subset (by
      rw [getElem!_pos s.2 0 (by omega)]; exact List.getElem_mem _)
    have m1 : s.2[1]! ∈ trailAt T u :: y :: t' := hperm.subset (by
      rw [getElem!_pos s.2 1 (by omega)]; exact List.getElem_mem _)
    have hne01 : s.2[0]! ≠ s.2[1]! := by
      rw [getElem!_pos s.2 0 (by omega), getElem!_pos s.2 1 (by omega)]
      exact (List.pairwise_iff_getElem.mp hnds) 0 1 (by omega) (by omega) (by omega)
    have tailOf : ∀ l ∈ trailAt T u :: y :: t', l ≠ trailAt T u → ∃ j < B, trailAt T j = l := fun l hl hne => by
      rcases List.mem_cons.mp hl with rfl | hl
      · exact absurd rfl hne
      · exact htail l hl
    have use : ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) → s.2[w]! ∈ trailAt T u :: y :: t' →
        s.2[o]! ∈ trailAt T u :: y :: t' → s.2[w]! ≠ trailAt T u → False := fun w o hwo hw ho hne => by
      obtain ⟨j, hj, e⟩ := tailOf _ hw hne
      obtain ⟨q, hq, -⟩ := hwatched s hs hlen w o hwo j (by omega) ⟨by omega, e⟩
      exact negc _ ho q hq
    by_cases h0 : s.2[0]! = trailAt T u
    · exact use 1 0 (Or.inr ⟨rfl, rfl⟩) m1 m0 (fun e => hne01 (h0.trans e.symm))
    · exact use 0 1 (Or.inl ⟨rfl, rfl⟩) m0 m1 h0

/-- `getElem!` of a mapped list. -/
theorem getElem!_map_of_lt {f : Nat → CInt} {l : List Nat} {i : Nat} (h : i < l.length) :
    (l.map f)[i]! = f l[i]! := by
  rw [getElem!_pos (l.map f) i (by simpa using h), getElem!_pos l i h, List.getElem_map]

/-- C:124–130: after the unassign loop, the last unassignment and the terminator, the state
meets the `Analyzed` contract with the collected clause and the backjump point found. -/
theorem analyzed_final (ctx : ACtx input T db vs D) {P : Nat} (hDP : D ≤ P)
    (hwatched : ∀ s ∈ db.all, 2 ≤ s.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
      ∀ p < P, FalseAt T s.2[w]! p → ∃ q, FalseAt T (- s.2[o]!) q ∧ SameOrLowerLevel T p q)
    {Sb Se0 Se S0 : solver} {size p : CInt}
    (h1 : BLoop input T D Sb Se0 size p ∧ p < Se0.forced) (hf : AFields T Se0 → AFields T Se)
    (hsh : SameShape Se0 Se) (hld : ∀ q, Se.ld q = Se0.ld q) (hA : Se.assigned = Se0.assigned)
    (hP : Se.processed = Se0.processed) (hH : Se.head = Se0.head)
    (hU : UInv T Se S0 ∧ S0.assigned ≤ S0.processed) :
    ∃ L vs' B, Analyzed input T db ((unassign S0 (S0.ld S0.assigned)).st
      ((unassign S0 (S0.ld S0.assigned)).buffer + size) 0) size L vs' B ∧ B ≤ D := by
  obtain ⟨u, ps, hst, hb, hsz, hfe, hle, hAe, hue, hpre, hppe⟩ := BLoop.exit ctx h1 hf hsh hld hA hP
  obtain ⟨⟨a, hf0, hP0, hH0, hA0, hpa, haA, hcells, hflags⟩, hle0⟩ := hU
  have hn := ctx.num
  have hu : u < trailLen T := hst.2.2.2.1
  have hDu : D ≤ u := hst.2.2.1
  have hfD := ctx.forced_le
  obtain ⟨hBdec, hBD⟩ := hb.B_low hfD
  have hBu := hb.B_le
  have hse := hle.shape
  have hs0 := hf0.shape
  have hs0e := hb.low.shape
  generalize hBdef : processedPos Se0 = B at hBdec hBD hBu hppe
  have hprocB : Se.processed = T.falseStack + B := by
    simp only [processedPos] at hppe; rw [hse.falseStack] at hppe; omega
  have haB : a = B := by
    rw [hppe] at hpa
    rw [hA0, hP0, hprocB] at hle0; omega
  subst haB
  have hBt : a < trailLen T := by omega
  have hBf : forcedPos T ≤ a := Classical.byContradiction fun hlt =>
    ctx.core.trail.forced_root a (by omega) a (Nat.le_refl _) hBdec
  -- cells that are not flags are those of `Se0`
  have rd : ∀ q, 0 ≤ q → (q < 6 * T.nVars + 5 ∨ 8 * T.nVars + 5 < q) → S0.ld q = Se0.ld q := fun q h0 hq => by
    rw [hcells q h0 (fun i h1 h2 => by
      have := ctx.lit (show i < trailLen T by rw [hAe] at h2; omega); rw [hse.false]; omega), hld]
  have htrB : S0.ld S0.assigned = trailAt T a := by
    rw [hA0, rd _ (by omega) (by omega)]; exact hb.low.trail ctx hBt
  rw [htrB]
  have hxB := ctx.lit hBt
  have hnd : ps.Nodup := hb.sorted.imp (fun hab => Nat.ne_of_gt hab)
  have hlenps : ps.length ≤ u + 1 - forcedPos T := by
    have hsub : ps ⊆ (List.range' (forcedPos T) (u + 1 - forcedPos T)) := fun q hq => by
      have := hb.ps_mem q hq; rw [List.mem_range'_1]; omega
    have := hnd.length_le_of_subset hsub
    rwa [List.length_range'] at this
  have hsz' : size = (ps.length : CInt) := hsz
  have hb0 : (unassign S0 (trailAt T a)).buffer = T.buffer := by simp [unassign, hs0.buffer]
  have hfz : 0 ≤ S0.false + trailAt T a := by rw [hs0.false]; omega
  have ldf : ∀ q, 0 ≤ q → ((unassign S0 (trailAt T a)).st ((unassign S0 (trailAt T a)).buffer + size) 0).ld q =
      if q = T.buffer + size then 0 else if q = T.false + trailAt T a then 0 else S0.ld q := fun q hq => by
    rw [ld_st _ _ (by rw [hb0]; omega) hq, hb0]
    split
    · rfl
    · show (S0.st (S0.false + trailAt T a) 0).ld q = _
      rw [ld_st _ _ hfz hq, hs0.false]
  generalize hSf : (unassign S0 (trailAt T a)).st ((unassign S0 (trailAt T a)).buffer + size) 0 = Sf at ldf
  have hfSf : AFields T Sf := by rw [← hSf]; exact (hf0.st _ _).st _ _
  have hsSf := hfSf.shape
  have hSfA : Sf.assigned = T.falseStack + a := by rw [← hSf]; simp [unassign, hA0]
  have hSfP : Sf.processed = T.falseStack + a := by rw [← hSf]; simp [unassign, hP0, hprocB]
  have hSfH : Sf.head = Se0.head := by rw [← hSf]; simp [unassign, hH0, hH]
  -- reading `Sf` outside the flags and the buffer
  have rdf : ∀ q, 0 ≤ q → (q < 3 * T.nVars + 3 ∨ (4 * T.nVars + 3 < q ∧ q < 6 * T.nVars + 5) ∨ 8 * T.nVars + 5 < q) →
      Sf.ld q = Se0.ld q := fun q h0 hq => by
    rw [ldf q h0, if_neg (by omega), if_neg (by omega)]; exact rd q h0 (by omega)
  -- flags of `Sf`
  have flagf : ∀ l, -T.nVars ≤ l → l ≤ T.nVars → flag Sf l =
      if l = trailAt T a then 0 else flag S0 l := fun l h1 h2 => by
    simp only [flag, hsSf.false]
    rw [ldf _ (by omega), if_neg (by omega)]
    split
    · rw [if_pos (by omega)]
    · rw [if_neg (by omega), hs0.false]
  have flag0 : ∀ l, -T.nVars ≤ l → l ≤ T.nVars → (∀ i, a < i → i ≤ u → l ≠ trailAt T i) →
      flag S0 l = flag Se0 l := fun l h1 h2 hne => by
    simp only [flag, hs0.false]
    rw [hcells _ (by omega) (fun i h1' h2' he => hne i h1' (by rw [hAe] at h2'; omega) (by rw [hse.false] at he; omega)),
      hld, hs0e.false]
  obtain ⟨vs', ho⟩ := hb.order
  have hhead : ps.head? = some u := hb.head (by omega)
  obtain ⟨t, hps⟩ : ∃ t, ps = u :: t := by
    cases ps with
    | nil => simp at hhead
    | cons x t => simp at hhead; exact ⟨t, by rw [hhead]⟩
  have hpos : ∀ q ∈ ps, q < trailLen T := fun q hq => by have := hb.ps_mem q hq; omega
  have nodup_map : ∀ {f : Nat → CInt}, (∀ x ∈ ps, ∀ y ∈ ps, f x = f y → x = y) → (ps.map f).Nodup := fun inj =>
    List.pairwise_map.mpr (hnd.imp_of_mem fun {x y} hx hy hne he => hne (inj x hx y hy he))
  refine ⟨ps.map (trailAt T), vs', a, ⟨by rw [List.length_map]; exact hsz', by simp [hps], fun i hi => ?_, ⟨?_, ?_⟩,
    final_entailed ctx hst hb, final_new ctx hwatched (by omega) hu hBu (by simp [hps]) ?_ ?_, ?_,
    ⟨hBt, hBf, hBdec⟩, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi hr => ?_, fun i hi hr => ?_,
    fun l hl ho' => ?_, ?_, fun q hq => ?_, ?_, ⟨u, hBu, hu, by simp [hps]⟩, fun l hl => ?_, fun hl1 i hi => ?_,
    fun hl2 => ?_⟩, hBD⟩
  -- buffer_eq
  · simp only [List.length_map] at hi
    rw [List.getElem_map, hsSf.buffer, ldf _ (by omega), if_neg (by omega), if_neg (by omega),
      rd _ (by omega) (by omega), ← hs0e.buffer]
    exact hb.buffer i hi
  -- shape
  · rw [List.map_map]
    refine List.pairwise_map.mpr (hnd.imp_of_mem fun {x y} hx hy hne he => hne ?_)
    simp only [Function.comp] at he
    have e2 : abs (trailAt T x) = abs (trailAt T y) := by rw [abs_eq_natAbs, abs_eq_natAbs, he]
    exact ctx.core.trail.distinct x (hpos x hx) y (hpos y hy) e2
  · intro l hl
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
    exact ctx.core.trail.lit i (hpos i hi)
  -- tail
  · intro l hl
    rw [hps] at hl; simp at hl
    obtain ⟨q, hq, rfl⟩ := hl
    exact ⟨q, hBdef ▸ hb.tail_lt q (by rw [hps]; exact hq), rfl⟩
  · exact nodup_map fun x hx y hy he => ctx.pos_eq (hpos x hx) (hpos y hy) he
  -- fields
  · obtain ⟨DB, a', p', hd, r', nc, fa, sl, e⟩ := hfSf
    have e1 := congrArg solver.assigned e; have e2 := congrArg solver.processed e
    simp only at e1 e2
    refine ⟨DB, hd, r', nc, fa, sl, ?_⟩
    rw [e, ← e1, ← e2, hSfA, hSfP]
  -- trail_eq
  · simp only [trailAt, hsSf.falseStack]
    rw [rdf _ (by omega) (by omega)]; exact hb.low.trail ctx (by omega)
  -- reason_eq
  · simp only [reasonOf, hsSf.reason]
    have hl := ctx.lit (show i < trailLen T by omega)
    have : 1 ≤ abs (trailAt T i) ∧ abs (trailAt T i) ≤ T.nVars := by
      rcases abs_cases (trailAt T i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    rw [rdf _ (by omega) (by omega), ← hs0e.reason]; exact hb.low.mid _ (by rw [hs0e.reason]; omega) (by rw [hs0e.reason]; omega)
  -- model_eq
  · have hl := ctx.lit (show i < trailLen T by omega)
    have : 1 ≤ abs (trailAt T i) ∧ abs (trailAt T i) ≤ T.nVars := by
      rcases abs_cases (trailAt T i) with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
    rw [hsSf.model, rdf _ (by omega) (by omega)]; exact hb.model _ (by omega) (by omega)
  -- flag_root
  · have hl := ctx.lit (show i < trailLen T by omega)
    have hif := ctx.root_lt i (by omega) hr
    rw [flagf _ hl.2.1 hl.2.2, if_neg (fun e => by have := ctx.pos_eq (by omega) hBt e; omega),
      flag0 _ hl.2.1 hl.2.2 (fun i' h1 h2 e => by have := ctx.pos_eq (by omega) (by omega) e; omega)]
    exact (hb.cache i hif).1 hr
  -- flag_level
  · have hl := ctx.lit (show i < trailLen T by omega)
    have hif : forcedPos T ≤ i := Classical.byContradiction fun hlt =>
      hr (ctx.core.trail.forced_root i (by omega))
    rw [flagf _ hl.2.1 hl.2.2, if_neg (fun e => by have := ctx.pos_eq (by omega) hBt e; omega),
      flag0 _ hl.2.1 hl.2.2 (fun i' h1 h2 e => by have := ctx.pos_eq (by omega) (by omega) e; omega)]
    exact hb.done i hif (by omega)
  -- flags_off
  · have hl' := inRange_iff.mp hl
    rw [flagf _ hl'.2.1 hl'.2.2]
    split
    · rfl
    · rename_i hneB
      by_cases hon : ∃ i < trailLen T, trailAt T i = l
      · obtain ⟨i, hi, rfl⟩ := hon
        rcases Nat.lt_or_ge i a with h1 | h1
        · exact absurd rfl (ho' i h1)
        · rcases Nat.eq_or_lt_of_le h1 with e | h2
          · subst e; exact absurd rfl hneB
          · rcases Nat.lt_or_ge u i with h3 | h3
            · rw [flag0 _ hl'.2.1 hl'.2.2 (fun i' h1' h2' e => by have := ctx.pos_eq hi (by omega) e; omega)]
              exact hb.above i h3 hi
            · exact hflags i h2 (by rw [hAe]; omega)
      · rw [flag0 _ hl'.2.1 hl'.2.2 (fun i' h1' h2' e => hon ⟨i', by omega, e.symm⟩)]
        exact hb.off l hl (fun i hi e => hon ⟨i, hi, e⟩)
  -- flag_zero
  · rw [flagf 0 (by omega) (by omega), if_neg (fun e => hxB.1 e.symm),
      flag0 0 (by omega) (by omega) (fun i' h1 h2 e => (ctx.lit (show i' < trailLen T by omega)).1 e.symm)]
    exact hb.zero
  -- high
  · rw [rdf q (by omega) (by omega)]; exact hb.low.high q hq
  -- order
  · refine ho.frame (ctx.layout hb.fields hb.low) ?_ hSfH fun q h1 h2 => ?_
    · exact ⟨by rw [hsSf.nVars, hs0e.nVars], by rw [hsSf.model, hs0e.model], by rw [hsSf.next, hs0e.next],
        by rw [hsSf.prev, hs0e.prev], by rw [hsSf.buffer, hs0e.buffer], by rw [hsSf.reason, hs0e.reason],
        by rw [hsSf.falseStack, hs0e.falseStack], by rw [hsSf.false, hs0e.false], by rw [hsSf.first, hs0e.first]⟩
    · rw [hs0e.nVars] at h1 h2; exact rdf q (by omega) (by omega)
  -- rest_false
  · rw [hps] at hl; simp at hl
    obtain ⟨q, hq, rfl⟩ := hl
    exact ⟨q, hBdef ▸ hb.tail_lt q (by rw [hps]; exact hq), rfl⟩
  -- unit
  · simp only [List.length_map] at hl1
    intro k hk hdec
    rcases Nat.lt_or_ge k (forcedPos T) with h1 | h1
    · exact ctx.core.trail.forced_root k h1 k (Nat.le_refl _) hdec
    · exact (hb.gap k hdec (by omega)).2 (by omega) h1
  -- second
  · simp only [List.length_map] at hl2
    have h1t : ps[1]! ∈ ps.tail := by
      rw [hps]; rw [hps] at hl2; simp at hl2
      rw [getElem!_pos _ 1 (by simp; omega)]; simp
    have hj1 : ps[1]! < a := hBdef ▸ hb.tail_lt _ h1t
    have hj1m : ps[1]! ∈ ps := by rw [hps] at h1t ⊢; exact List.mem_cons_of_mem _ h1t
    refine ⟨⟨ps[1]!, hj1, (getElem!_map_of_lt (by omega)).symm, fun k hk1 hk2 hdec =>
      (hb.gap k hdec (by rw [hBdef]; exact hk2)).1 hl2 hk1⟩, ?_⟩
    have hmj := (hb.ps_mem _ hj1m).2.2
    have hnr : ¬ RootLevel T ps[1]! := fun hr => by
      have := hst.1.root _ (by have := (hb.ps_mem _ hj1m).2.1; omega) hr
      have hm := hmj.2; unfold Marked at hm; rw [hm] at this; exact absurd this (by decide)
    obtain ⟨k, hk, hdec⟩ : ∃ k ≤ ps[1]!, IsDecision T k :=
      Classical.byContradiction fun hno => hnr fun k hk hd => hno ⟨k, hk, hd⟩
    have hkf : forcedPos T ≤ k := Classical.byContradiction fun hlt =>
      ctx.core.trail.forced_root k (by omega) k (Nat.le_refl _) hdec
    exact ⟨k, hkf, by omega, hdec⟩

end Final

end MicrosatLean.Faithful.Verification
