import MicrosatLean.Faithful.Verification.ParseStep
import MicrosatLean.Faithful.Verification.Invariant

/-!
# After `parse`: the invariant of `solve`'s loop

Once every clause is loaded, `parse`'s invariant gives `Inv` for the state `solve`
starts from: `res = 0` and the decision cursor at `head` (C:161).
-/

namespace MicrosatLean.Faithful.Verification

/-- `vars` grows by one variable at a time. -/
theorem vars_succ (m : Nat) : vars ((m : CInt) + 1) = vars m ++ [(m : CInt) + 1] := by
  simp only [vars, show ((m : CInt) + 1).toNat = m + 1 by omega, Int.toNat_natCast,
    List.range_succ, List.map_append, List.map_cons, List.map_nil]

/-- Following `prev` from `m` visits `m, m - 1, …, 1` and ends at 0, as `initCDCL` links
them (C:207). -/
theorem prevChain_init {S : solver} {N : CInt}
    (hprev : ∀ v, 1 ≤ v → v ≤ N → S.ld (S.prev + v) = v - 1) :
    ∀ m : Nat, (m : CInt) ≤ N → PrevChain S m (vars m).reverse
  | 0, _ => by simp [vars, PrevChain]
  | m + 1, hm => by
    have e : ((m + 1 : Nat) : CInt) = (m : CInt) + 1 := by omega
    rw [e, vars_succ, List.reverse_append]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.cons_append,
      List.singleton_append]
    refine ⟨rfl, ?_⟩
    rw [hprev _ (by omega) (by omega), show (m : CInt) + 1 - 1 = m by omega]
    exact prevChain_init hprev m (by omega)

/-- The `i`-th variable in `head`'s order is `N - i`. -/
theorem vars_reverse_getElem {N : CInt} (hN : 0 ≤ N) (i : Nat) (h : i < (vars N).reverse.length) :
    (vars N).reverse[i] = N - i := by
  rw [List.getElem_reverse]
  simp only [vars, List.getElem_map, List.getElem_range, List.length_map, List.length_range,
    List.length_reverse] at h ⊢
  omega

/-- One record per clause. -/
theorem parseRecords_length (p : Ptr) (cs : List (Array CInt)) : (parseRecords p cs).length = cs.length := by
  induction cs generalizing p with
  | nil => rfl
  | cons c cs ih => simp [parseRecords, ih]

/-- Record `i` holds clause `i`'s literals, in order. -/
theorem parseRecords_getElem_snd (p : Ptr) (cs : List (Array CInt)) (i : Nat)
    (h : i < (parseRecords p cs).length) :
    ((parseRecords p cs)[i]).2 = (cs[i]'(by rw [parseRecords_length] at h; exact h)).toList := by
  induction cs generalizing p i with
  | nil => simp [parseRecords] at h
  | cons c cs ih =>
    cases i with
    | zero => simp [parseRecords]
    | succ i => simp only [parseRecords, List.getElem_cons_succ]; exact ih _ i _

/-- `parse`'s final state satisfies `solve`'s loop invariant. Used by `parse_correct`. -/
theorem ParseCore.inv {input : Input} {S0 S : solver} (valid : input.Valid)
    (memory : memoryBound input ≤ S0.mem_max)
    (h0 : InitState input.nVars input.nClauses S0.mem_max S0)
    (h : ParseCore input S0 S input.clauses.size) :
    Inv input { S with res := 0 } S.head := by
  obtain ⟨hnv, hbuf, hfirst, hfalse, hmodel, hreason, hstack, hprev, hnext, hnl, hmm⟩ := h.ptrs h0
  have hN : 1 ≤ S0.nVars := by rw [h0.nVars]; exact varsOf_pos _
  have hNv : S0.nVars = varsOf input.nVars := h0.nVars
  have hmax : varsOf input.nVars = max 1 input.nVars := by unfold varsOf; split <;> omega
  obtain ⟨DB, mf, hS⟩ := h.fields
  have hfS : S.forced = stackAt S0.nVars ∧ S.processed = stackAt S0.nVars ∧ S.head = S0.nVars := by
    rw [hS]; simp only [withParsed]
    exact ⟨by rw [h0.forced, hNv], by rw [h0.processed, hNv], by rw [h0.head, hNv]⟩
  have hcells : ∀ q, StaticCell S0.nVars q → S.ld q = initCell S0.nVars (vars S0.nVars) q := by
    intro q hq
    rw [h.static q hq, h0.cells q (by simp only [StaticCell, nextAt, prevAt, clausesAt, falseAt] at hq; omega), hNv]
  have hlen := h.trail.2.1
  have hlit := h.trail.2.2.1
  -- every literal `parse` assigned has a unit-clause reason: no decisions, all at the root
  have hreasonNZ : ∀ i < trailLen S, reasonOf S (trailAt S i) ≠ 0 := by
    intro i hi
    obtain ⟨r, hr, e1, -⟩ := h.reasons i hi
    have := h.record_ge hr
    rw [e1]; simp only [clausesAt] at this; omega
  have hroot : ∀ i < trailLen S, RootLevel S i := fun i hi k hk hd =>
    hreasonNZ k (by omega) hd
  have hrecs : parseRecords (clausesAt S0.nVars) (input.clauses.toList.take input.clauses.size) =
      parseRecords (clausesAt S0.nVars) input.clauses.toList := by
    rw [← Array.length_toList, List.take_length]
  have hmu : S.mem_used = parseEnd (clausesAt S0.nVars) input.clauses.toList := by
    rw [hS]; simp only [withParsed]; rw [← Array.length_toList, List.take_length]
  have htile : Tiling { S with res := 0 } (clausesAt S0.nVars) S.mem_used
      (parseRecords (clausesAt S0.nVars) input.clauses.toList) := by
    have := h.records; rw [hrecs] at this; exact this.frame fun _ _ _ _ => rfl
  have hstart : lemmasStart { S with res := 0 }
      ⟨parseRecords (clausesAt S0.nVars) input.clauses.toList, [], fun _ => false⟩ = S.mem_used := by
    unfold lemmasStart
    split
    · rename_i hnil
      have : input.clauses.toList = [] := by
        have := congrArg List.length hnil; rw [parseRecords_length] at this
        exact List.eq_nil_of_length_eq_zero (by simpa using this)
      rw [hmu, this]; show clausesAt S.nVars = _; rw [hnv]; rfl
    · rename_i hne
      have hpos : 0 < input.clauses.size := by
        rcases Nat.eq_zero_or_pos input.clauses.size with h' | h'
        · exfalso; apply hne
          have : input.clauses.toList = [] := List.eq_nil_of_length_eq_zero (by simpa using h')
          rw [this]; rfl
        · exact h'
      exact h.fixed hpos
  have hNt : ((S0.nVars.toNat : Nat) : CInt) = S0.nVars := by omega
  have hlenv : (vars S0.nVars).reverse.length = S0.nVars.toNat := by simp [vars]
  have hml : S.maxLemmas = 2000 := by rw [hS]; exact h0.maxLemmas
  refine ⟨⟨parseRecords (clausesAt S0.nVars) input.clauses.toList, [], fun _ => false⟩, (vars S0.nVars).reverse,
    ⟨valid, by show S.nVars = _; rw [hnv, hNv, hmax], by show _ ≤ S.mem_max; rw [hmm]; exact memory,
      by show (0 : CInt) ≤ S.maxLemmas; rw [hml]; decide,
      ?layout, ?trail, ?root, ?database, ?watches, ?reasons, ?units, ?order⟩, ?watched, ?mode, ?cursor⟩
  case layout =>
    refine ⟨by show 1 ≤ S.nVars; omega, by show S.model = modelAt S.nVars; rw [hnv]; exact hmodel,
      by show S.next = nextAt S.nVars; rw [hnv]; exact hnext,
      by show S.prev = prevAt S.nVars; rw [hnv]; exact hprev,
      by show S.buffer = bufferAt S.nVars; rw [hnv]; exact hbuf,
      by show S.reason = reasonAt S.nVars; rw [hnv]; exact hreason,
      by show S.falseStack = stackAt S.nVars; rw [hnv]; exact hstack,
      by show S.false = falseAt S.nVars; rw [hnv]; exact hfalse,
      by show S.first = firstAt S.nVars; rw [hnv]; exact hfirst, ?_⟩
    show S.ld (clausesAt S.nVars - 1) = 0
    rw [hnv, hcells _ (by simp [StaticCell])]
    exact initCell_sentinel hN
  case trail =>
    refine ⟨?_, ?_, ?_, by rw [hnv]; exact hlen, by rw [hnv]; exact hlit, h.trail.2.2.2, ?_, ?_, ?_, ?_,
      ?_, ?_⟩
    · show S.falseStack ≤ S.forced; rw [hstack, hfS.1]; exact Int.le_refl _
    · show S.forced ≤ S.processed; rw [hfS.1, hfS.2.1]; exact Int.le_refl _
    · show S.processed ≤ S.assigned; rw [hfS.2.1]; exact h.trail.1
    · intro i hi _
      show flag S (trailAt S i) = IMPLIED
      rw [h.flags _ (hlit i hi), if_pos ⟨i, hi, rfl⟩]
    · intro i hi hnr; exact absurd (hroot i hi) hnr
    · intro lit hl hoff
      show flag S lit = 0
      rw [hnv] at hl
      rw [h.flags _ hl, if_neg (fun ⟨i, hi, he⟩ => hoff i hi he)]
    · intro i hi
      show S.ld (S.model + abs (trailAt S i)) ≠ 0 ↔ trailAt S i < 0
      rw [h.model i hi]
      by_cases hc : trailAt S i < 0
      · rw [if_pos hc]; exact ⟨fun _ => hc, fun _ => by decide⟩
      · rw [if_neg hc]; exact ⟨fun h' => absurd rfl h', fun h' => absurd h' hc⟩
    · show S.ld (S.false + 0) = 0
      rw [hfalse, Int.add_zero, hcells _ (by simp [StaticCell])]
      exact initCell_zero (fun v hv => mem_vars.mp hv) (by simp only [falseAt]; omega)
    · intro i hi
      simp only [forcedPos] at hi
      rw [hstack, hfS.1] at hi; simp at hi
  case root =>
    intro i hi _ a hsat
    obtain ⟨j, hj, hjs, cj⟩ := h.units_input i hi
    have := hsat _ (Array.getElem_mem hjs)
    rw [cj] at this; exact this
  case database =>
    refine ⟨?_, ?_, ?_, ?_, ?_, fun _ => rfl, ?_, ?_, ?_, ?_⟩
    · rw [hstart, show clausesAt ({ S with res := 0 } : solver).nVars = clausesAt S0.nVars by
        show clausesAt S.nVars = _; rw [hnv]]
      exact htile
    · rw [hstart]; exact .nil _
    · simp [parseRecords_length]
    · intro i hi hi'
      rw [parseRecords_getElem_snd]
      simp
    · intro r hr
      obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
      have hi' : i < input.clauses.size := by rw [parseRecords_length] at hi; simpa using hi
      rw [parseRecords_getElem_snd]
      have hmem : input.clauses[i] ∈ input.clauses.toList.take input.clauses.size := by
        rw [← Array.length_toList, List.take_length]; simp
      have := h.nonempty _ hmem
      intro he; apply this; simpa using congrArg List.length he
    · show S.nLemmas = _; rw [hnl]; rfl
    · intro r hr; simp at hr
    · intro r hr; simp at hr
    · simp
  case watches =>
    intro lit hl
    have := h.watches lit hl
    rw [hrecs] at this
    obtain ⟨links, hl', hnd, hm⟩ := this
    exact ⟨links, hl'.frame fun q _ => rfl, hnd, hm⟩
  case reasons =>
    intro i hi hf hr
    obtain ⟨r, hr', e1, e2⟩ := h.reasons i hi
    rw [hrecs] at hr'
    refine ⟨r, by simpa [Records.all] using hr', e1, by rw [e2]; rfl, by rw [e2]; simp,
      fun hnr => absurd (hroot i hi) hnr⟩
  case units =>
    intro r hr h1
    simp only [Records.all, List.append_nil] at hr
    rw [← hrecs] at hr
    obtain ⟨i, hi, he⟩ := h.units_true r hr h1
    exact ⟨i, hi, hroot i hi, he⟩
  case watched =>
    intro r hr h2 w o hwo p hp
    simp only [processedPos] at hp
    rw [hfS.2.1, hstack] at hp; simp at hp
  case mode =>
    refine Or.inl ⟨?_, hroot⟩
    simp only [processedPos]
    show (S.processed - S.falseStack).toNat = 0
    rw [hfS.2.1, hstack]; simp
  case order =>
    refine ⟨?_, ?_, ?_, ?_⟩
    · show PrevChain _ S.head _
      have := prevChain_init (S := { S with res := 0 }) (N := S0.nVars) (fun v h1 h2 => by
        show S.ld (S.prev + v) = v - 1
        rw [hprev, hcells _ (by simp only [StaticCell, prevAt, nextAt, clausesAt]; omega)]
        exact initCell_prev ⟨h1, h2⟩) S0.nVars.toNat (by omega)
      rw [hNt] at this
      exact (congrArg (fun x => PrevChain { S with res := 0 } x (vars S0.nVars).reverse) hfS.2.2).mpr this
    · show (vars S0.nVars).reverse.Perm (vars S.nVars)
      rw [hnv]; exact List.reverse_perm _
    · intro i h
      have hi : i + 1 < S0.nVars.toNat := hlenv ▸ h
      rw [vars_reverse_getElem (N := S0.nVars) (by omega), vars_reverse_getElem (N := S0.nVars) (by omega)]
      show S.ld (S.next + (S0.nVars - ((i + 1 : Nat) : CInt))) = S0.nVars - (i : CInt)
      rw [hnext, show nextAt S0.nVars + (S0.nVars - ((i + 1 : Nat) : CInt)) =
          nextAt S0.nVars + (S0.nVars - i) - 1 by omega,
        hcells _ (by simp only [StaticCell, prevAt, nextAt, clausesAt]; omega)]
      exact initCell_next ⟨by omega, by omega⟩
    · show S.ld (S.next + 0) = _
      have hlast : (vars S0.nVars).reverse.getLast? = some 1 := by
        rw [List.getLast?_reverse]
        simp only [vars, List.head?_map, List.head?_range, show S0.nVars.toNat ≠ 0 by omega,
          if_false, Option.map_some]
        rfl
      rw [hlast, hnext, show nextAt S0.nVars + 0 = nextAt S0.nVars + 1 - 1 by omega,
        hcells _ (by simp only [StaticCell, prevAt, nextAt, clausesAt]; omega)]
      exact initCell_next ⟨Int.le_refl 1, hN⟩
  case cursor =>
    refine ⟨0, Nat.zero_le _, ?_, fun j _ hj => absurd hj (Nat.not_lt_zero j)⟩
    have h0 : 0 < (vars S0.nVars).reverse.length := by omega
    rw [List.getElem?_eq_getElem h0, vars_reverse_getElem (N := S0.nVars) (by omega)]
    show S0.nVars - ((0 : Nat) : CInt) = S.head
    rw [hfS.2.2]; omega

end MicrosatLean.Faithful.Verification
