import MicrosatLean.Faithful.Verification.VisitUnit

/-!
# `implied` (C:93–100)

During the minimization of a learned clause, `implied S lit` decides whether the false
literal `lit` is implied by the MARKed literals: every literal of its reason clause is
MARKed or (recursively) implied. Answers are cached in the flag (`IMPLIED`, or
`IMPLIED - 1` for "not implied"). Positions refer to the trail of the conflict state `T`,
which `analyze` does not change below the literals it examines.
-/

namespace MicrosatLean.Faithful.Verification

/-- The literal at trail position `i` of `T` is false in every model of the input in which
the literals at the positions `M` below `i` are false: dropping it from a clause that
contains those literals keeps the clause entailed. -/
def Imp (input : Input) (T : solver) (M : Nat → Prop) (i : Nat) : Prop :=
  ∀ a, input.Sat a → (∀ j < i, M j → ¬ LitTrue a (trailAt T j)) → ¬ LitTrue a (trailAt T i)

/-- The flags `implied` reads, at the trail positions below `K`: root literals are tagged
`IMPLIED`; the others are tagged 1, MARK (only at positions of `M`), or carry a cached
answer, `IMPLIED - 1` ("not implied") or `IMPLIED` (only when `Imp` holds). -/
def Cache (input : Input) (T S : solver) (M : Nat → Prop) (K : Nat) : Prop :=
  ∀ i < K, (RootLevel T i → flag S (trailAt T i) = IMPLIED) ∧
    (¬ RootLevel T i → flag S (trailAt T i) = 1 ∨ (flag S (trailAt T i) = MARK ∧ M i) ∨
      flag S (trailAt T i) = IMPLIED - 1 ∨ (flag S (trailAt T i) = IMPLIED ∧ Imp input T M i))

/-- No literal at the positions `[D, E)` is MARKed or cached as implied. -/
def NoImp (T S : solver) (D E : Nat) : Prop :=
  ∀ i, D ≤ i → i < E → flag S (trailAt T i) ≠ MARK ∧ flag S (trailAt T i) ≠ IMPLIED

/-- `S` is `T` up to the cells `analyze` writes: the `next`/`prev` arrays, the buffer and the
flags. The reasons, the trail and the clauses are `T`'s. -/
structure SameLow (T S : solver) : Prop where
  shape : SameShape T S
  mid : ∀ q, 4 * T.nVars + 4 ≤ q → q ≤ 6 * T.nVars + 4 → S.ld q = T.ld q
  high : ∀ q, 8 * T.nVars + 6 ≤ q → S.ld q = T.ld q

section helpers
variable {input : Input} {T : solver} {db : Records} {vs : List CInt} {M : Nat → Prop} {D : Nat}

/-- What `implied_spec` claims about the result `(S', r)` of `implied` from `S` at position `i`. -/
def ImpliedPost (input : Input) (T : solver) (M : Nat → Prop) (D : Nat) (S : solver) (i : Nat)
    (S' : solver) (r : CInt) : Prop :=
  (∃ DB, S' = ({ S with DB := DB } : solver)) ∧
    (∀ q, 0 ≤ q → (∀ j ≤ i, ¬ RootLevel T j → q ≠ S.false + trailAt T j) → S'.ld q = S.ld q) ∧
    (∀ K, Cache input T S M K → Cache input T S' M K) ∧
    (∀ j ≤ i, flag S (trailAt T j) = MARK → j < i → flag S' (trailAt T j) = MARK) ∧
    (r ≠ 0 → Imp input T M i) ∧
    (∀ E ≤ trailLen T, NoImp T S D E → NoImp T S' D E) ∧
    (D ≤ i → NoImp T S D i → flag S (trailAt T i) ≠ IMPLIED → r = 0)

/-- `implied_spec` at trail position `i`, for every state (the induction hypothesis). -/
def ImpliedAt (input : Input) (T : solver) (M : Nat → Prop) (D i : Nat) : Prop :=
  ∀ S, SameLow T S → i < trailLen T → Cache input T S M (i + 1) →
    ∃ S' r, implied S (trailAt T i) = some (S', r) ∧ ImpliedPost input T M D S i S' r

/-- `l` is false in every model of the input where the `M`-literals below `i` are false. -/
def GoodBelow (input : Input) (T : solver) (M : Nat → Prop) (i : Nat) (l : CInt) : Prop :=
  ∀ a, input.Sat a → (∀ j < i, M j → ¬ LitTrue a (trailAt T j)) → ¬ LitTrue a l

/-- A write leaves every other cell unchanged, also at negative pointers. -/
theorem ld_st_of_ne_any (S : solver) {p q : Int} (v : CInt) (hp : 0 ≤ p) (hne : q ≠ p) :
    (S.st p v).ld q = S.ld q := by
  by_cases hq : 0 ≤ q
  · exact ld_st_of_ne S v hp hq hne
  · have hq' : q < 0 := by omega
    simp [solver.ld, hq']

/-- Writing the flag of `x` changes the flag of `x` only. -/
theorem flag_after_st (S : solver) {x : CInt} (v y : CInt) (hx : 0 ≤ S.false + x) :
    flag (S.st (S.false + x) v) y = if y = x then v else flag S y := by
  unfold flag
  rw [st_false]
  by_cases hy : y = x
  · rw [ite_eq_left hy, hy]; exact ld_st_self S v hx
  · rw [ite_eq_right hy]; exact ld_st_of_ne_any S v hx (by omega)

/-- A literal and its negation are not both true. -/
theorem LitTrue.not_of_neg {a : Assignment} {x : CInt} (hx : x ≠ 0) (h : LitTrue a (-x)) :
    ¬ LitTrue a x := by
  intro ht
  unfold LitTrue at h ht
  rw [Int.natAbs_neg, ht] at h
  simp at h
  omega

/-- Trail positions of `T` hold distinct literals. -/
theorem Core.trailAt_inj (core : Core input T db vs) {j j' : Nat} (hj : j < trailLen T)
    (hj' : j' < trailLen T) (h : trailAt T j = trailAt T j') : j = j' :=
  core.trail.distinct j hj j' hj' (by rw [h])

/-- The flag cell of a trail literal lies in the `false` array. -/
theorem Core.flag_cell (core : Core input T db vs) {X : solver} (hX : X.false = T.false) {j : Nat}
    (hj : j < trailLen T) :
    6 * T.nVars + 5 ≤ X.false + trailAt T j ∧ X.false + trailAt T j ≤ 8 * T.nVars + 5 := by
  obtain ⟨-, -, -, -, -, -, hf, -⟩ := core.layout.num
  have hl := inRange_iff.mp (core.trail.lit j hj)
  omega

/-- Each record of the database holds its literals. -/
theorem Core.record_clauseAt (core : Core input T db vs) {r : Record} (hr : r ∈ db.all) :
    ClauseAt T r.1 r.2 := by
  rcases List.mem_append.mp hr with h | h
  · exact core.database.inputs_tile.clauseAt h
  · exact core.database.lemmas_tile.clauseAt h

/-- `SameLow` survives changes of `DB` in flag cells of trail literals only. -/
theorem SameLow.frame (core : Core input T db vs) {S S1 : solver} (hS : SameLow T S)
    (hdb : ∃ DB, S1 = ({ S with DB := DB } : solver))
    (hfr : ∀ q, 0 ≤ q → (∀ j < trailLen T, q ≠ S.false + trailAt T j) → S1.ld q = S.ld q) :
    SameLow T S1 := by
  obtain ⟨DB, rfl⟩ := hdb
  have hn := core.layout.nVars_pos
  refine ⟨⟨hS.shape.nVars, hS.shape.model, hS.shape.next, hS.shape.prev, hS.shape.buffer,
    hS.shape.reason, hS.shape.falseStack, hS.shape.false, hS.shape.first⟩, fun q h1 h2 => ?_,
    fun q h1 => ?_⟩
  · rw [hfr q (by omega) fun j hj => by have := core.flag_cell hS.shape.false hj; omega]
    exact hS.mid q h1 h2
  · rw [hfr q (by omega) fun j hj => by have := core.flag_cell hS.shape.false hj; omega]
    exact hS.high q h1

/-- `Cache` for fewer positions. -/
theorem Cache.mono {S : solver} {K K' : Nat} (h : Cache input T S M K) (hK : K' ≤ K) :
    Cache input T S M K' :=
  fun j hj => h j (by omega)

/-- The flags `Cache` allows. -/
theorem Cache.vals {S : solver} {K j : Nat} (h : Cache input T S M K) (hj : j < K) :
    flag S (trailAt T j) = 1 ∨ flag S (trailAt T j) = MARK ∨ flag S (trailAt T j) = IMPLIED - 1 ∨
      flag S (trailAt T j) = IMPLIED := by
  by_cases hr : RootLevel T j
  · exact Or.inr (Or.inr (Or.inr ((h j hj).1 hr)))
  · rcases (h j hj).2 hr with h | ⟨h, -⟩ | h | ⟨h, -⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))

/-- `implied`'s test `false[*p] ^ MARK` (C:98) on the flags `Cache` allows. -/
theorem xor_mark_ne_zero {x : CInt} (h : x = 1 ∨ x = MARK ∨ x = IMPLIED - 1 ∨ x = IMPLIED)
    (hm : x ≠ MARK) : (x ^^^ MARK != 0) = true := by
  rcases h with rfl | rfl | rfl | rfl
  · decide
  · exact absurd rfl hm
  · decide
  · decide

/-- `Imp` carries over to a later position holding the same literal. -/
theorem Imp.of_le {j i' : Nat} (h : Imp input T M j) (hle : j ≤ i')
    (he : trailAt T i' = trailAt T j) : Imp input T M i' := by
  intro a ha hM
  rw [he]
  exact h a ha fun j' hj' => hM j' (by omega)

/-- Root literals are false in every model. -/
theorem Imp.of_root (core : Core input T db vs) {i : Nat} (hi : i < trailLen T)
    (h : RootLevel T i) : Imp input T M i := by
  intro a ha _
  obtain ⟨l, hl, hlt⟩ := core.root i hi h a ha
  rw [List.mem_singleton] at hl
  subst hl
  exact LitTrue.not_of_neg (inRange_iff.mp (core.trail.lit i hi)).1 hlt

/-- A literal whose reason's other literals are all `GoodBelow` is implied. -/
theorem Imp.of_reason (core : Core input T db vs) {r : Record} (hr : r ∈ db.all) {i : Nat}
    (hi : i < trailLen T) (h0 : r.2[0]? = some (-trailAt T i))
    (hgood : ∀ m l, 1 ≤ m → r.2[m]? = some l → GoodBelow input T M i l) : Imp input T M i := by
  intro a ha hM ht
  obtain ⟨l, hl, hlt⟩ := core.record_entailed hr a ha
  obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hl
  cases m with
  | zero =>
    rw [h0] at hm
    cases hm
    exact LitTrue.not_of_neg (inRange_iff.mp (core.trail.lit i hi)).1 hlt ht
  | succ m => exact hgood (m + 1) l (by omega) hm a ha hM hlt

/-- One more reason literal is `GoodBelow`. -/
theorem GoodBelow.succ {r : Record} {k i : Nat} {x : CInt}
    (hgood : ∀ m l, 1 ≤ m → m ≤ k → r.2[m]? = some l → GoodBelow input T M i l)
    (hx : r.2[k + 1]? = some x) (hg : GoodBelow input T M i x) :
    ∀ m l, 1 ≤ m → m ≤ k + 1 → r.2[m]? = some l → GoodBelow input T M i l := by
  intro m l h1 h2 hl
  by_cases hm : m ≤ k
  · exact hgood m l h1 hm hl
  · rw [show m = k + 1 by omega, hx] at hl
    cases hl
    exact hg

/-- Caching `IMPLIED - 1`, or `IMPLIED` with `Imp`, for a non-root trail literal keeps `Cache`. -/
theorem Cache.write (core : Core input T db vs) {S : solver} {K i : Nat} {v : CInt}
    (hc : Cache input T S M K) (hi : i < trailLen T) (hroot : ¬ RootLevel T i)
    (hx : 0 ≤ S.false + trailAt T i) (hv : v = IMPLIED - 1 ∨ (v = IMPLIED ∧ Imp input T M i)) :
    Cache input T (S.st (S.false + trailAt T i) v) M K := by
  intro j hj
  rw [flag_after_st S v _ hx]
  by_cases he : trailAt T j = trailAt T i
  · rw [ite_eq_left he]
    have hle : i ≤ j := by
      by_cases h : j < trailLen T
      · exact Nat.le_of_eq (core.trailAt_inj hi h he.symm)
      · omega
    have hnr : ¬ RootLevel T j := fun h => hroot fun k hk => h k (by omega)
    refine ⟨fun h => absurd h hnr, fun _ => ?_⟩
    rcases hv with rfl | ⟨rfl, himp⟩
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr ⟨rfl, himp.of_le hle he⟩))
  · rw [ite_eq_right he]
    exact hc j hj

/-- `NoImp` for fewer positions. -/
theorem NoImp.mono {S : solver} {E E' : Nat} (h : NoImp T S D E) (hE : E' ≤ E) : NoImp T S D E' :=
  fun j h1 h2 => h j h1 (by omega)

/-- A flag write keeps `NoImp` unless it writes MARK or `IMPLIED` to a literal in `[D, E)`. -/
theorem NoImp.write {S : solver} {E : Nat} {x v : CInt} (h : NoImp T S D E) (hx : 0 ≤ S.false + x)
    (hv : (v ≠ MARK ∧ v ≠ IMPLIED) ∨ ∀ j, D ≤ j → j < E → trailAt T j ≠ x) :
    NoImp T (S.st (S.false + x) v) D E := by
  intro j h1 h2
  rw [flag_after_st S v _ hx]
  split
  · rename_i he
    rcases hv with hv | hv
    · exact hv
    · exact absurd he (hv j h1 h2)
  · exact h j h1 h2

/-- `implied`'s final write (C:98–99) of its answer for position `i` gives `ImpliedPost`. -/
theorem ImpliedPost.write (core : Core input T db vs) {S Sk : solver} {i : Nat} {v res : CInt}
    (hSk : SameLow T Sk) (hi : i < trailLen T) (hroot : ¬ RootLevel T i)
    (hdb : ∃ DB, Sk = ({ S with DB := DB } : solver))
    (hfr : ∀ q, 0 ≤ q → (∀ j < i, ¬ RootLevel T j → q ≠ S.false + trailAt T j) → Sk.ld q = S.ld q)
    (hca : ∀ K, Cache input T S M K → Cache input T Sk M K)
    (hmk : ∀ j < i, flag S (trailAt T j) = MARK → flag Sk (trailAt T j) = MARK)
    (hni : ∀ E ≤ trailLen T, NoImp T S D E → NoImp T Sk D E)
    (hv : v = IMPLIED - 1 ∨ (v = IMPLIED ∧ Imp input T M i ∧ ¬ (D ≤ i ∧ NoImp T S D i)))
    (himp : res ≠ 0 → Imp input T M i) (hzero : D ≤ i → NoImp T S D i → res = 0) :
    ImpliedPost input T M D S i (Sk.st (Sk.false + trailAt T i) v) res := by
  obtain ⟨DB, rfl⟩ := hdb
  have hx := core.flag_cell hSk.shape.false hi
  have hn := core.layout.nVars_pos
  have hx0 : 0 ≤ ({ S with DB := DB } : solver).false + trailAt T i := by omega
  refine ⟨?_, ?_, ?_, ?_, himp, ?_, fun h1 h2 _ => hzero h1 h2⟩
  · obtain ⟨DB', h⟩ := st_eq ({ S with DB := DB } : solver) _ v
    exact ⟨DB', h⟩
  · intro q hq hne
    rw [ld_st_of_ne_any _ v hx0 (hne i (Nat.le_refl i) hroot)]
    exact hfr q hq fun j hj hr => hne j (Nat.le_of_lt hj) hr
  · intro K hK
    exact Cache.write core (hca K hK) hi hroot hx0 (hv.imp_right fun h => ⟨h.1, h.2.1⟩)
  · intro j _ hm hlt
    rw [flag_after_st _ v _ hx0,
      ite_eq_right fun he => by have := core.trailAt_inj (by omega) hi he; omega]
    exact hmk j hlt hm
  · intro E hE h
    refine NoImp.write (hni E hE h) hx0 ?_
    rcases hv with rfl | ⟨rfl, -, hno⟩
    · exact Or.inl ⟨by decide, by decide⟩
    · refine Or.inr fun j h1 h2 he => hno ?_
      have := core.trailAt_inj (by omega) hi he
      subst this
      exact ⟨h1, h.mono (by omega)⟩

/-- A recursive call (C:98) at a non-MARK position `j < i` keeps the loop's facts on the state. -/
theorem ImpliedPost.step (core : Core input T db vs) {S Sk S1 : solver} {i j : Nat} {r1 : CInt}
    (hSk : SameLow T Sk) (hj : j < i) (hi : i < trailLen T)
    (hdb : ∃ DB, Sk = ({ S with DB := DB } : solver))
    (hfr : ∀ q, 0 ≤ q → (∀ j < i, ¬ RootLevel T j → q ≠ S.false + trailAt T j) → Sk.ld q = S.ld q)
    (hca : ∀ K, Cache input T S M K → Cache input T Sk M K)
    (hmk : ∀ j < i, flag S (trailAt T j) = MARK → flag Sk (trailAt T j) = MARK)
    (hni : ∀ E ≤ trailLen T, NoImp T S D E → NoImp T Sk D E)
    (hnm : flag Sk (trailAt T j) ≠ MARK) (hp : ImpliedPost input T M D Sk j S1 r1) :
    SameLow T S1 ∧ (∃ DB, S1 = ({ S with DB := DB } : solver)) ∧
      (∀ q, 0 ≤ q → (∀ j < i, ¬ RootLevel T j → q ≠ S.false + trailAt T j) → S1.ld q = S.ld q) ∧
      (∀ K, Cache input T S M K → Cache input T S1 M K) ∧
      (∀ j < i, flag S (trailAt T j) = MARK → flag S1 (trailAt T j) = MARK) ∧
      (∀ E ≤ trailLen T, NoImp T S D E → NoImp T S1 D E) := by
  obtain ⟨⟨DB1, rfl⟩, pfr, pca, pmk, -, pni, -⟩ := hp
  obtain ⟨DB, rfl⟩ := hdb
  have hn := core.layout.nVars_pos
  refine ⟨SameLow.frame core hSk ⟨DB1, rfl⟩ fun q hq hne =>
      pfr q hq fun j' _ _ => hne j' (by omega),
    ⟨DB1, rfl⟩, fun q hq hne => (pfr q hq fun j' _ hr => hne j' (by omega) hr).trans (hfr q hq hne),
    fun K h => pca K (hca K h), fun j' hj' hm => ?_, fun E hE h => pni E hE (hni E hE h)⟩
  have hm' := hmk j' hj' hm
  rcases Nat.lt_trichotomy j' j with h | h | h
  · exact pmk j' (Nat.le_of_lt h) hm' h
  · subst h; exact absurd hm' hnm
  · have hc := core.flag_cell hSk.shape.false (show j' < trailLen T by omega)
    refine (pfr (({ S with DB := DB } : solver).false + trailAt T j') (by omega)
      fun j'' hj'' _ he => ?_).trans hm'
    have := core.trailAt_inj (by omega) (by omega) (Int.add_left_cancel he)
    omega

/-- The loop of `implied` (C:97–100) over the reason of position `i`, from its literal `k`. -/
theorem impliedLoop_post (core : Core input T db vs) {i : Nat}
    (ih : ∀ j < i, ImpliedAt input T M D j) {S : solver} (hi : i < trailLen T)
    (hc : Cache input T S M (i + 1)) (hroot : ¬ RootLevel T i)
    {r : Record} (hr : r ∈ db.all) (h0 : r.2[0]? = some (-trailAt T i))
    (hfalse : ∀ l ∈ r.2.drop 1, ∃ j < i, FalseAt T l j) {m0 j0 : Nat} (hm0 : 1 ≤ m0)
    (hlj0 : r.2[m0]? = some (trailAt T j0)) (hj0 : j0 < i) (hDj0 : D ≤ i → D ≤ j0) (t : Nat) :
    ∀ k Sk, k + 1 + t = r.2.length → SameLow T Sk → (∃ DB, Sk = ({ S with DB := DB } : solver)) →
      (∀ q, 0 ≤ q → (∀ j < i, ¬ RootLevel T j → q ≠ S.false + trailAt T j) → Sk.ld q = S.ld q) →
      (∀ K, Cache input T S M K → Cache input T Sk M K) →
      (∀ j < i, flag S (trailAt T j) = MARK → flag Sk (trailAt T j) = MARK) →
      (∀ m l, 1 ≤ m → m ≤ k → r.2[m]? = some l → GoodBelow input T M i l) →
      (∀ E ≤ trailLen T, NoImp T S D E → NoImp T Sk D E) →
      (D ≤ i → NoImp T S D i → k < m0) →
      ∃ S' res, impliedLoop Sk (trailAt T i) (r.1 + k) = some (S', res) ∧
        ImpliedPost input T M D S i S' res := by
  have hcl := core.record_clauseAt hr
  have hge := core.database.record_ge hr
  have hm0L : m0 < r.2.length := (List.getElem?_eq_some_iff.mp hlj0).1
  have hj0L : j0 < trailLen T := by omega
  have hn := core.layout.nVars_pos
  simp only [clausesAt] at hge
  induction t with
  | zero =>
    intro k Sk hk hSk hdb hfr hca hmk hgood hni hsame
    have hread : Sk.ld (r.1 + k + 1) = 0 := by
      rw [hSk.high _ (by omega), show r.1 + (k : Int) + 1 = r.1 + (r.2.length : Int) by omega]
      exact hcl.2
    have himp : Imp input T M i := Imp.of_reason core hr hi h0 fun m l h1 hl =>
      hgood m l h1 (by have := (List.getElem?_eq_some_iff.mp hl).1; omega) hl
    rw [impliedLoop.eq_1, hread, ite_eq_left (by decide)]
    exact ⟨_, _, rfl, ImpliedPost.write core hSk hi hroot hdb hfr hca hmk hni
      (Or.inr ⟨rfl, himp, fun ⟨h1, h2⟩ => by have := hsame h1 h2; omega⟩) (fun _ => himp)
      (fun h1 h2 => by have := hsame h1 h2; omega)⟩
  | succ t iht =>
    intro k Sk hk hSk hdb hfr hca hmk hgood hni hsame
    have hk1 : k + 1 < r.2.length := by omega
    have hget : r.2[k + 1]? = some r.2[k + 1] := List.getElem?_eq_getElem hk1
    obtain ⟨j, hj, hjL, hjl⟩ := hfalse r.2[k + 1]
      (List.mem_iff_getElem?.mpr ⟨k, by rw [List.getElem?_drop, Nat.add_comm]; exact hget⟩)
    rw [← hjl] at hget
    have hread : Sk.ld (r.1 + k + 1) = trailAt T j := by
      rw [hSk.high _ (by omega), show r.1 + (k : Int) + 1 = r.1 + ((k + 1 : Nat) : Int) by omega,
        hcl.1 _ hk1, hjl]
    have hl0 : trailAt T j ≠ 0 := (inRange_iff.mp (core.trail.lit j hjL)).1
    have hptr : r.1 + (k : Int) + 1 = r.1 + ((k + 1 : Nat) : Int) := by omega
    have hcj := hca _ hc
    rw [impliedLoop.eq_1, hread, ite_eq_right (by simpa using hl0),
      show Sk.ld (Sk.false + trailAt T j) = flag Sk (trailAt T j) from rfl]
    by_cases hm : flag Sk (trailAt T j) = MARK
    · rw [hm, ite_eq_right (by decide), hptr]
      have hM : M j := by
        by_cases hrj : RootLevel T j
        · have h6 := (hcj j (by omega)).1 hrj
          rw [hm] at h6; exact absurd h6 (by decide)
        · rcases (hcj j (by omega)).2 hrj with h | ⟨-, h⟩ | h | ⟨h, -⟩
          · rw [hm] at h; exact absurd h (by decide)
          · exact h
          · rw [hm] at h; exact absurd h (by decide)
          · rw [hm] at h; exact absurd h (by decide)
      refine iht (k + 1) Sk (by omega) hSk hdb hfr hca hmk
        (GoodBelow.succ hgood hget fun _ _ hM' => hM' j hj hM) hni ?_
      intro h1 h2
      have := hsame h1 h2
      refine Nat.lt_of_le_of_ne (by omega) fun he => ?_
      rw [← he, hget] at hlj0
      have hjj := core.trailAt_inj hjL hj0L (Option.some.inj hlj0)
      subst hjj
      exact ((hni i (Nat.le_of_lt hi) h2) j (hDj0 h1) hj).1 hm
    · rw [ite_eq_left (xor_mark_ne_zero (Cache.vals hcj (j := j) (by omega)) hm)]
      obtain ⟨S1, r1, hcall, hpost⟩ := ih j hj Sk hSk hjL (Cache.mono hcj (by omega))
      rw [hcall]
      simp only [bind, Option.bind]
      obtain ⟨hS1, hdb1, hfr1, hca1, hmk1, hni1⟩ :=
        ImpliedPost.step core hSk hj hi hdb hfr hca hmk hni hm hpost
      by_cases hr1 : r1 = 0
      · rw [ite_eq_left (by simp [hr1])]
        exact ⟨_, _, rfl, ImpliedPost.write core hS1 hi hroot hdb1 hfr1 hca1 hmk1 hni1 (Or.inl rfl)
          (fun h => absurd rfl h) (fun _ _ => rfl)⟩
      · rw [ite_eq_right (by simpa using hr1), hptr]
        refine iht (k + 1) S1 (by omega) hS1 hdb1 hfr1 hca1 hmk1
          (GoodBelow.succ hgood hget fun a ha hM =>
            hpost.2.2.2.2.1 hr1 a ha fun j' hj' => hM j' (by omega)) hni1 ?_
        intro h1 h2
        have := hsame h1 h2
        refine Nat.lt_of_le_of_ne (by omega) fun he => ?_
        rw [← he, hget] at hlj0
        have hjj := core.trailAt_inj hjL hj0L (Option.some.inj hlj0)
        subst hjj
        have hN := hni i (Nat.le_of_lt hi) h2
        exact hr1 (hpost.2.2.2.2.2.2 (hDj0 h1) (hN.mono (Nat.le_of_lt hj)) (hN j (hDj0 h1) hj).2)

/-- `implied_spec` by strong induction on the trail position. -/
theorem implied_at (core : Core input T db vs) (hD : IsDecision T D) (i : Nat) :
    ImpliedAt input T M D i := by
  induction i using Nat.strongRecOn with
  | _ i ih =>
  intro S hS hi hc
  have hci := hc i (by omega)
  have hn := core.layout.nVars_pos
  rw [implied.eq_1, show S.ld (S.false + trailAt T i) = flag S (trailAt T i) from rfl]
  by_cases hgt : flag S (trailAt T i) > MARK
  · rw [ite_eq_left hgt]
    refine ⟨S, _, rfl, ⟨S.DB, rfl⟩, fun _ _ _ => rfl, fun _ h => h, fun _ _ h _ => h, ?_,
      fun _ _ h => h, ?_⟩
    · intro hne
      by_cases hroot : RootLevel T i
      · exact Imp.of_root core hi hroot
      · rcases hci.2 hroot with h | ⟨h, -⟩ | h | ⟨-, h⟩
        · rw [h] at hgt; exact absurd hgt (by decide)
        · rw [h] at hgt; exact absurd hgt (by decide)
        · rw [h] at hne; exact absurd hne (by decide)
        · exact h
    · intro hDi _ h6
      rcases hci.2 (fun h => h D hDi hD) with h | ⟨h, -⟩ | h | ⟨h, -⟩
      · rw [h] at hgt; exact absurd hgt (by decide)
      · rw [h] at hgt; exact absurd hgt (by decide)
      · rw [h]; decide
      · exact absurd h h6
  · rw [ite_eq_right hgt]
    have hroot : ¬ RootLevel T i := fun h => hgt (by rw [hci.1 h]; decide)
    by_cases hz : (S.ld (S.reason + abs (trailAt T i)) == 0) = true
    · rw [ite_eq_left hz]
      exact ⟨S, 0, rfl, ⟨S.DB, rfl⟩, fun _ _ _ => rfl, fun _ h => h, fun _ _ h _ => h,
        fun h => absurd rfl h, fun _ _ h => h, fun _ _ _ => rfl⟩
    · rw [ite_eq_right hz]
      have hl := inRange_iff.mp (core.trail.lit i hi)
      obtain ⟨-, -, -, -, hre, -, -, -⟩ := core.layout.num
      have hreason : reasonOf T (trailAt T i) = S.ld (S.reason + abs (trailAt T i)) := by
        unfold reasonOf
        rcases abs_cases (trailAt T i) with ⟨_, e⟩ | ⟨_, e⟩ <;>
          rw [hS.shape.reason, hS.mid _ (by omega) (by omega)]
      have hne : reasonOf T (trailAt T i) ≠ 0 := by rw [hreason]; simpa using hz
      have hforced : forcedPos T ≤ i :=
        Nat.le_of_not_lt fun h => hroot (core.trail.forced_root i h)
      obtain ⟨r, hr, hre1, h0, hfalse, hsl⟩ := core.reasons i hi hforced hne
      obtain ⟨l0, hl0, j0, hj0, hF0, hlev⟩ := hsl hroot
      obtain ⟨m, hm⟩ := List.mem_iff_getElem?.mp hl0
      rw [List.getElem?_drop] at hm
      have hL : 0 + 1 + (r.2.length - 1) = r.2.length := by
        have := (List.getElem?_eq_some_iff.mp h0).1; omega
      rw [show S.ld (S.reason + abs (trailAt T i)) - 1 = r.1 + ((0 : Nat) : Int) by
        rw [← hreason, hre1]; omega]
      exact impliedLoop_post core ih hi hc hroot hr h0 hfalse (m0 := 1 + m) (by omega)
        (by rw [hm, hF0.2]) hj0 (fun hDi => Nat.le_of_not_lt fun h => hlev D h hDi hD) _ 0 S hL hS
        ⟨S.DB, rfl⟩ (fun _ _ _ => rfl) (fun _ h => h) (fun _ _ h => h)
        (fun _ _ h1 h2 _ => absurd h2 (by omega)) (fun _ _ h => h) (fun _ _ => by omega)

end helpers

/-- `implied` (C:93–100) on the literal at trail position `i` returns, and:
it changes only `DB`, and there only the flags of non-root literals at positions up to `i`;
it keeps `Cache` and the MARKs below `i`; a nonzero answer means `Imp`; and below the last
decision `D` nothing changes about `NoImp`, while at or above `D` (where every reason has a
literal of the same level, reaching back to the decision `D`) it answers 0 when nothing in
`[D, i)` is MARKed or cached as implied. Used by `analyze`'s minimization loop. -/
theorem implied_spec {input : Input} {T : solver} {db : Records} {vs : List CInt}
    (core : Core input T db vs) {M : Nat → Prop} {D : Nat} (hD : IsDecision T D)
    {S : solver} (hS : SameLow T S) {i : Nat} (hi : i < trailLen T) (hc : Cache input T S M (i + 1)) :
    ∃ S' r, implied S (trailAt T i) = some (S', r) ∧
      (∃ DB, S' = ({ S with DB := DB } : solver)) ∧
      (∀ q, 0 ≤ q → (∀ j ≤ i, ¬ RootLevel T j → q ≠ S.false + trailAt T j) → S'.ld q = S.ld q) ∧
      (∀ K, Cache input T S M K → Cache input T S' M K) ∧
      (∀ j ≤ i, flag S (trailAt T j) = MARK → j < i → flag S' (trailAt T j) = MARK) ∧
      (r ≠ 0 → Imp input T M i) ∧
      (∀ E ≤ trailLen T, NoImp T S D E → NoImp T S' D E) ∧
      (D ≤ i → NoImp T S D i → flag S (trailAt T i) ≠ IMPLIED → r = 0) := by
  obtain ⟨S', r, h, hp⟩ := implied_at core hD i S hS hi hc
  exact ⟨S', r, h, hp⟩

end MicrosatLean.Faithful.Verification
