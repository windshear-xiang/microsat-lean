import MicrosatLean.Faithful.Verification.Regions

/-!
# `bump` (C:85–91)

`bump` MARKs a literal unless it is a root literal (`IMPLIED`), and moves its variable to
the front of the decision order: the doubly linked list of `OrderList`.
-/

namespace MicrosatLean.Faithful.Verification

/-- Setting `head` keeps every cell. -/
theorem ld_with_head (S : solver) (h q : CInt) :
    ({ S with head := h } : solver).ld q = S.ld q := rfl

/-- A `prev` chain starts at its first entry. -/
theorem PrevChain.head_eq {S : solver} {v : CInt} {vs : List CInt} (h : PrevChain S v vs)
    (hv : 0 < vs.length) : vs[0] = v := by
  cases vs with
  | nil => simp at hv
  | cons w ws => exact h.1.symm

/-- A `prev` chain from its links: each entry's `prev` is the following entry, or 0 at the end. -/
theorem PrevChain.of_getElem {S : solver} {v : CInt} {vs : List CInt} (hv : vs[0]?.getD 0 = v)
    (h : ∀ k (hk : k < vs.length), S.ld (S.prev + vs[k]) = vs[k + 1]?.getD 0) :
    PrevChain S v vs := by
  induction vs generalizing v with
  | nil => show v = 0; simpa using hv.symm
  | cons w ws ih =>
    refine ⟨by simpa using hv.symm, ih ?_ fun k hk => ?_⟩
    · have := h 0 (by simp)
      simp only [List.getElem_cons_zero, List.getElem?_cons_succ] at this
      exact this.symm
    · have := h (k + 1) (by simp; omega)
      simp only [List.getElem_cons_succ, List.getElem?_cons_succ] at this
      exact this

/-- Moving entry `k > 0` of the decision order to the front, relinked as `bump` does (C:87–90). -/
theorem OrderList.move {S T : solver} {vs : List CInt} (h : OrderList S vs) (hl : Layout S)
    {k : Nat} (hk0 : 0 < k) (hk : k < vs.length)
    (hn : T.nVars = S.nVars) (hnext : T.next = S.next) (hprev : T.prev = S.prev)
    (hh : T.head = vs[k])
    (e1 : T.ld (S.prev + vs[k]) = vs[0])
    (e2 : T.ld (S.next + vs[0]) = vs[k])
    (e3 : T.ld (S.next + vs[k + 1]?.getD 0) = vs[k - 1])
    (e4 : T.ld (S.prev + vs[k - 1]) = vs[k + 1]?.getD 0)
    (same : ∀ q, S.nVars + 1 ≤ q → q ≤ 3 * S.nVars + 2 → q ≠ S.prev + vs[k] →
      q ≠ S.next + vs[0] → q ≠ S.next + vs[k + 1]?.getD 0 → q ≠ S.prev + vs[k - 1] →
      T.ld q = S.ld q) :
    OrderList T (vs[k] :: vs.eraseIdx k) := by
  have num := hl.num
  have hN := hl.nVars_pos
  have hnd := h.nodup
  have hv : ∀ j (hj : j < vs.length), 1 ≤ vs[j] ∧ vs[j] ≤ S.nVars :=
    fun j hj => h.mem_iff.mp (List.getElem_mem hj)
  have hlen : (vs.eraseIdx k).length = vs.length - 1 := List.length_eraseIdx_of_lt hk
  have hc : ∀ j (hj : j < vs.length), vs[j] = vs[k + 1]?.getD 0 → j = k + 1 := by
    intro j hj e
    by_cases hk1 : k + 1 < vs.length
    · rw [List.getElem?_eq_getElem hk1, Option.getD_some] at e
      exact hnd.getElem_inj.mp e
    · rw [List.getElem?_eq_none (by omega), Option.getD_none] at e
      have := hv j hj; omega
  have hc0 : 0 ≤ vs[k + 1]?.getD 0 ∧ vs[k + 1]?.getD 0 ≤ S.nVars := by
    by_cases hk1 : k + 1 < vs.length
    · rw [List.getElem?_eq_getElem hk1, Option.getD_some]; have := hv _ hk1; omega
    · rw [List.getElem?_eq_none (by omega), Option.getD_none]; omega
  have hv0 := hv 0 (by omega)
  have hvk := hv k hk
  have hvk1 := hv (k - 1) (by omega)
  have tprev : ∀ j (hj : j < vs.length), j ≠ k → j ≠ k - 1 →
      T.ld (S.prev + vs[j]) = vs[j + 1]?.getD 0 := by
    intro j hj h1 h2
    have hvj := hv j hj
    have n1 : vs[j] ≠ vs[k] := fun e => h1 (hnd.getElem_inj.mp e)
    have n2 : vs[j] ≠ vs[k - 1] := fun e => h2 (hnd.getElem_inj.mp e)
    rw [same _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
    exact h.chain.prev_getElem j hj
  have tnext : ∀ j (hj : j < vs.length), j ≠ 0 → j ≠ k + 1 →
      T.ld (S.next + vs[j]) = S.ld (S.next + vs[j]) := by
    intro j hj h1 h2
    have hvj := hv j hj
    have n1 : vs[j] ≠ vs[0] := fun e => h1 (hnd.getElem_inj.mp e)
    have n2 : vs[j] ≠ vs[k + 1]?.getD 0 := fun e => h2 (hc j hj e)
    exact same _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hh]
    refine PrevChain.of_getElem (by simp) fun i hi => ?_
    simp only [List.length_cons, hlen] at hi
    rw [hprev]
    cases i with
    | zero =>
      simp only [List.getElem_cons_zero, List.getElem?_cons_succ, e1]
      rw [List.getElem?_eraseIdx_of_lt hk0, List.getElem?_eq_getElem (by omega), Option.getD_some]
    | succ j =>
      simp only [List.getElem_cons_succ, List.getElem?_cons_succ]
      by_cases hjk : j + 1 < k
      · rw [List.getElem_eraseIdx_of_lt _ (by omega), List.getElem?_eraseIdx_of_lt hjk]
        exact tprev j (by omega) (by omega) (by omega)
      · by_cases hjk' : j + 1 = k
        · rw [List.getElem_eraseIdx_of_lt _ (by omega), List.getElem?_eraseIdx_of_ge (by omega)]
          subst hjk'
          simpa using e4
        · rw [List.getElem_eraseIdx_of_ge _ (by omega), List.getElem?_eraseIdx_of_ge (by omega)]
          exact tprev (j + 1) (by omega) (by omega) (by omega)
  · rw [hn]
    refine List.Perm.trans ?_ h.perm
    have e : vs = vs.take k ++ vs[k] :: vs.drop (k + 1) := by
      rw [← List.drop_eq_getElem_cons hk, List.take_append_drop]
    have := List.perm_middle (a := vs[k]) (l₁ := vs.take k) (l₂ := vs.drop (k + 1))
    rw [← e] at this
    rw [List.eraseIdx_eq_take_drop_succ]
    exact this.symm
  · intro i hi
    simp only [List.length_cons, hlen] at hi
    rw [hnext]
    cases i with
    | zero =>
      simp only [List.getElem_cons_succ, List.getElem_cons_zero]
      rw [List.getElem_eraseIdx_of_lt _ hk0]
      exact e2
    | succ j =>
      simp only [List.getElem_cons_succ]
      by_cases hjk : j + 1 < k
      · rw [List.getElem_eraseIdx_of_lt _ hjk, List.getElem_eraseIdx_of_lt _ (by omega),
          tnext (j + 1) (by omega) (by omega) (by omega)]
        exact h.next_back j (by omega)
      · by_cases hjk' : j + 1 = k
        · rw [List.getElem_eraseIdx_of_ge _ (by omega), List.getElem_eraseIdx_of_lt _ (by omega)]
          subst hjk'
          rw [List.getElem?_eq_getElem (by omega), Option.getD_some] at e3
          simpa using e3
        · rw [List.getElem_eraseIdx_of_ge _ (by omega), List.getElem_eraseIdx_of_ge _ (by omega),
            tnext (j + 1 + 1) (by omega) (by omega) (by omega)]
          exact h.next_back (j + 1) (by omega)
  · rw [hnext, List.getLast?_eq_getElem?]
    have hL : (vs[k] :: vs.eraseIdx k).length - 1 = (vs.length - 2) + 1 := by
      simp only [List.length_cons, hlen]; omega
    rw [hL, List.getElem?_cons_succ]
    by_cases hk1 : k + 1 < vs.length
    · have n1 : (0 : CInt) ≠ vs[k + 1]?.getD 0 := by
        rw [List.getElem?_eq_getElem hk1, Option.getD_some]; have := hv _ hk1; omega
      rw [same _ (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h.next_zero,
        List.getLast?_eq_getElem?, List.getElem?_eraseIdx_of_ge (by omega),
        show vs.length - 2 + 1 = vs.length - 1 by omega]
    · rw [List.getElem?_eq_none (by omega), Option.getD_none] at e3
      rw [e3, List.getElem?_eraseIdx_of_lt (by omega), List.getElem?_eq_getElem (by omega),
        Option.getD_some]
      simp only [show k - 1 = vs.length - 2 by omega]

/-- `bump` (C:85–91) changes only `DB` and `head`: the literal's flag becomes MARK unless it
is `IMPLIED`, the cells outside the flag and the `next`/`prev` arrays are kept, and the
decision order is still a list of all variables. Used by `analyze`. -/
theorem bump_spec {S : solver} {vs : List CInt} (hl : Layout S) (ho : OrderList S vs) {lit : CInt}
    (hlit : InRange S.nVars lit) :
    (∃ DB h, bump S lit = ({ S with DB := DB, head := h } : solver)) ∧
    flag (bump S lit) lit = (if flag S lit = IMPLIED then IMPLIED else MARK) ∧
    (∀ q, 0 ≤ q → q ≠ S.false + lit → (q ≤ S.nVars ∨ 3 * S.nVars + 2 < q) → (bump S lit).ld q = S.ld q) ∧
    ∃ vs', OrderList (bump S lit) vs' := by
  have num := hl.num
  have hN := hl.nVars_pos
  have hr := inRange_iff.mp hlit
  have hvar : 1 ≤ abs lit ∧ abs lit ≤ S.nVars := by
    rcases abs_cases lit with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  have hf0 : 0 ≤ S.false + lit := by omega
  by_cases hI : S.ld (S.false + lit) = IMPLIED
  · have hb : bump S lit = S := by simp [bump, hI]
    rw [hb]
    exact ⟨⟨S.DB, S.head, rfl⟩, by simp [flag, hI], fun q _ _ _ => rfl, vs, ho⟩
  have hflag : flag S lit ≠ IMPLIED := hI
  by_cases hH : abs lit = S.head
  · have hb : bump S lit = S.st (S.false + lit) MARK := by simp [bump, hI, hH]
    rw [hb]
    obtain ⟨DB, hDB⟩ := st_eq S (S.false + lit) MARK
    refine ⟨⟨DB, S.head, by rw [hDB]⟩, by simp [flag, hI, hf0],
      fun q hq hne _ => ld_st_of_ne _ _ hf0 hq hne, vs, ?_⟩
    exact ho.frame hl (SameShape.st _ _ _) (by simp) fun q h1 h2 =>
      ld_st_of_ne _ _ hf0 (by omega) (by omega)
  obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem (ho.mem_iff.mpr hvar)
  have hnd := ho.nodup
  have hv : ∀ j (hj : j < vs.length), 1 ≤ vs[j] ∧ vs[j] ≤ S.nVars :=
    fun j hj => ho.mem_iff.mp (List.getElem_mem hj)
  have h0 : vs[0] = S.head := ho.chain.head_eq (by omega)
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun e => hH (by subst e; exact hkv.symm.trans h0)
  have hv0 := hv 0 (by omega)
  have hvk1 := hv (k - 1) (by omega)
  have ha : S.ld (S.next + abs lit) = vs[k - 1] := by
    have := ho.next_back (k - 1) (by omega)
    simp only [show k - 1 + 1 = k by omega, hkv] at this
    exact this
  have hc : S.ld (S.prev + abs lit) = vs[k + 1]?.getD 0 := by
    rw [← hkv]; exact ho.chain.prev_getElem k hk
  have hc0 : 0 ≤ vs[k + 1]?.getD 0 ∧ vs[k + 1]?.getD 0 ≤ S.nVars ∧
      vs[k + 1]?.getD 0 ≠ S.head := by
    by_cases hk1 : k + 1 < vs.length
    · rw [List.getElem?_eq_getElem hk1, Option.getD_some, ← h0]
      have := hv _ hk1
      have : vs[k + 1] ≠ vs[0] := fun e => by have := hnd.getElem_inj.mp e; omega
      omega
    · rw [List.getElem?_eq_none (by omega), Option.getD_none]; omega
  have hak : vs[k - 1] ≠ abs lit := fun e => by
    rw [← hkv] at e; have := hnd.getElem_inj.mp e; omega
  have hb : bump S lit =
      { ((((S.st (S.false + lit) MARK).st (S.prev + vs[k - 1]) (vs[k + 1]?.getD 0)).st
        (S.next + vs[k + 1]?.getD 0) vs[k - 1]).st (S.next + S.head) (abs lit)).st
        (S.prev + abs lit) S.head with head := abs lit } := by
    have l1 : (S.st (S.false + lit) MARK).ld (S.next + abs lit) = vs[k - 1] := by
      rw [ld_st_of_ne _ _ hf0 (by omega) (by omega), ha]
    have l2 : (S.st (S.false + lit) MARK).ld (S.prev + abs lit) = vs[k + 1]?.getD 0 := by
      rw [ld_st_of_ne _ _ hf0 (by omega) (by omega), hc]
    have l3 : ((S.st (S.false + lit) MARK).st (S.prev + vs[k - 1]) (vs[k + 1]?.getD 0)).ld
        (S.prev + abs lit) = vs[k + 1]?.getD 0 := by
      rw [ld_st_of_ne _ _ (by omega) (by omega) (by omega), l2]
    have l4 : ((S.st (S.false + lit) MARK).st (S.prev + vs[k - 1]) (vs[k + 1]?.getD 0)).ld
        (S.next + abs lit) = vs[k - 1] := by
      rw [ld_st_of_ne _ _ (by omega) (by omega) (by omega), l1]
    simp [bump, hI, hH, l1, l2, l3, l4]
  rw [hb]
  refine ⟨⟨_, _, by apply solver.ext <;> first | rfl | simp⟩, ?_, ?_, ?_⟩
  · simp only [hflag, ↓reduceIte]
    unfold flag
    rw [ld_with_head]
    simp only [st_false]
    rw [ld_st_of_ne _ _ (by omega) (by omega) (by omega),
      ld_st_of_ne _ _ (by omega) (by omega) (by omega),
      ld_st_of_ne _ _ (by omega) (by omega) (by omega),
      ld_st_of_ne _ _ (by omega) (by omega) (by omega), ld_st_self _ _ hf0]
  · intro q hq hne hq'
    rw [ld_with_head, ld_st_of_ne _ _ (by omega) hq (by omega),
      ld_st_of_ne _ _ (by omega) hq (by omega), ld_st_of_ne _ _ (by omega) hq (by omega),
      ld_st_of_ne _ _ (by omega) hq (by omega), ld_st_of_ne _ _ hf0 hq hne]
  refine ⟨_, ho.move hl hk0 hk (by simp) (by simp) (by simp) hkv.symm ?_ ?_ ?_ ?_ ?_⟩
  · rw [hkv, h0, ld_with_head, ld_st_self _ _ (by omega)]
  · rw [hkv, h0, ld_with_head, ld_st_of_ne _ _ (by omega) (by omega) (by omega),
      ld_st_self _ _ (by omega)]
  · rw [ld_with_head, ld_st_of_ne _ _ (by omega) (by omega) (by omega),
      ld_st_of_ne _ _ (by omega) (by omega) (by omega), ld_st_self _ _ (by omega)]
  · rw [ld_with_head, ld_st_of_ne _ _ (by omega) (by omega) (by omega),
      ld_st_of_ne _ _ (by omega) (by omega) (by omega),
      ld_st_of_ne _ _ (by omega) (by omega) (by omega), ld_st_self _ _ (by omega)]
  · intro q h1 h2 n1 n2 n3 n4
    rw [hkv] at n1
    rw [h0] at n2
    rw [ld_with_head, ld_st_of_ne _ _ (by omega) (by omega) n1,
      ld_st_of_ne _ _ (by omega) (by omega) n2, ld_st_of_ne _ _ (by omega) (by omega) n3,
      ld_st_of_ne _ _ (by omega) (by omega) n4, ld_st_of_ne _ _ hf0 (by omega) (by omega)]

end MicrosatLean.Faithful.Verification
