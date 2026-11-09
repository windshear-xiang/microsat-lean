import MicrosatLean.Faithful.Verification.Analyze

/-!
# The states of `analyze` (C:102–129)

Positions refer to the trail of the conflict state `T`. `analyze` first MARKs the
conflict clause (C:104), then walks the trail down, resolving each MARKed literal with
its reason until only one MARKed literal is left at the last decision level, the first
UIP (C:105–113). It then collects the MARKed literals that `implied` cannot remove into
the buffer, finding the backjump point on the way (C:115–122), and unassigns down to it
(C:124–128). This file defines the loop invariants of these phases (used by
`AnalyzeLoop.lean`) and the frame facts they share.
-/

namespace MicrosatLean.Faithful.Verification

/-- `S` is `T` with only the fields `analyze` writes changed. -/
def AFields (T S : solver) : Prop :=
  ∃ (DB : Array CInt) (a p h r nc fa sl : CInt), S = ({ T with
    DB := DB, assigned := a, processed := p, head := h, res := r, nConflicts := nc, fast := fa,
    slow := sl } : solver)

/-- What `analyze` knows about the conflict state: its invariant, and `D`, the last
decision, at or above `forced`; the root is below `forced`. -/
structure ACtx (input : Input) (T : solver) (db : Records) (vs : List CInt) (D : Nat) : Prop where
  core : Core input T db vs
  dec : IsDecision T D
  forced_le : forcedPos T ≤ D
  lt : D < trailLen T
  last : ∀ k, D < k → k < trailLen T → ¬ IsDecision T k
  root_lt : ∀ i < trailLen T, RootLevel T i → i < forcedPos T

/-- Trail position `i` is MARKed in `S`. -/
def Marked (T S : solver) (i : Nat) : Prop := flag S (trailAt T i) = MARK

/-- The MARKed literals below position `a` form a clause the input entails. -/
def MEnt (input : Input) (T S : solver) (a : Nat) : Prop :=
  ∀ asg, input.Sat asg → ∃ i < a, Marked T S i ∧ LitTrue asg (trailAt T i)

/-- A state of the MARK and resolution phase with `a` positions still assigned: the
cells `analyze` does not write are `T`'s, root flags are `IMPLIED`, the others 1 or MARK,
and the positions from `a` on are unassigned. -/
structure RState (T S : solver) (a : Nat) : Prop where
  fields : AFields T S
  low : SameLow T S
  model : ∀ q, 0 ≤ q → q ≤ T.nVars → S.ld q = T.ld q
  le : a ≤ trailLen T
  order : ∃ vs, OrderList S vs
  root : ∀ i < a, RootLevel T i → flag S (trailAt T i) = IMPLIED
  level : ∀ i < a, ¬ RootLevel T i → flag S (trailAt T i) = 1 ∨ flag S (trailAt T i) = MARK
  above : ∀ i, a ≤ i → i < trailLen T → flag S (trailAt T i) = 0
  off : ∀ l, InRange T.nVars l → (∀ i < trailLen T, trailAt T i ≠ l) → flag S l = 0
  zero : flag S 0 = 0

/-- C:104: the conflict clause `lits` at `c` is bumped up to the cell `cl`. -/
def BumpInv (T S : solver) (c : Ptr) (lits : List CInt) (cl : Ptr) : Prop :=
  RState T S (trailLen T) ∧ S.assigned = T.assigned ∧ ∃ k ≤ lits.length, cl = c + k ∧
    ∀ i < trailLen T, ¬ RootLevel T i → trailAt T i ∈ lits.take k → Marked T S i

/-- The resolution loop (C:105–113) with `a` positions assigned: the MARKed literals form
an entailed clause, one of them at the last decision level. -/
def ResInv (input : Input) (T : solver) (D : Nat) (S : solver) (a : Nat) : Prop :=
  RState T S a ∧ S.assigned = T.falseStack + a ∧ D < a ∧ MEnt input T S a ∧
    ∃ i, D ≤ i ∧ i < a ∧ Marked T S i

/-- At `build` (C:115): `assigned` points at the first UIP `u`, the only MARKed literal at
the last decision level. -/
def BuildStart (input : Input) (T : solver) (D : Nat) (S : solver) (u : Nat) : Prop :=
  RState T S (u + 1) ∧ S.assigned = T.falseStack + u ∧ D ≤ u ∧ u < trailLen T ∧
    MEnt input T S (u + 1) ∧ Marked T S u ∧ ∀ i, D ≤ i → i < u → ¬ Marked T S i

/-- The check loop (C:108–109) from `assigned = falseStack + j`: no MARK in `[k, j)`. -/
def CheckInv (T : solver) (D : Nat) (S1 : solver) (ck : Ptr) : Prop :=
  ∃ k : Nat, ck = T.falseStack + k ∧ D < k ∧ (k : CInt) ≤ S1.assigned - T.falseStack ∧
    ∀ m : Nat, k ≤ m → (m : CInt) < S1.assigned - T.falseStack → ¬ Marked T S1 m

/-- How the check loop ends: the first UIP is found (`goto build`), or another MARK at the
last decision level. -/
def CheckOut (T : solver) (D : Nat) (S1 : solver) (g : Bool) : Prop :=
  (g = true ∧ ∀ m : Nat, D ≤ m → (m : CInt) < S1.assigned - T.falseStack → ¬ Marked T S1 m) ∨
  (g = false ∧ ∃ m : Nat, D ≤ m ∧ (m : CInt) < S1.assigned - T.falseStack ∧ Marked T S1 m)

/-- C:111–112: the reason `rr` of the literal at `j` is bumped up to the cell `cl`. -/
def RBump (T : solver) (db : Records) (S1 S : solver) (cl : Ptr) : Prop :=
  ∃ (j : Nat) (rr : Record), S1.assigned = T.falseStack + j ∧ j < trailLen T ∧ rr ∈ db.all ∧
    reasonOf T (trailAt T j) = 1 + rr.1 ∧ rr.2[0]? = some (- trailAt T j) ∧
    (∀ l ∈ rr.2.drop 1, ∃ i < j, FalseAt T l i) ∧
    ∃ k, 1 ≤ k ∧ k ≤ rr.2.length ∧ cl = rr.1 + k ∧ RState T S (j + 1) ∧ S.assigned = S1.assigned ∧
      (∀ i ≤ j, Marked T S1 i → Marked T S i) ∧
      ∀ m (hm : m < rr.2.length), 1 ≤ m → m < k → ∀ i < j, ¬ RootLevel T i → trailAt T i = rr.2[m] →
        Marked T S i

/-- The minimization loop (C:116–122) at position `k - 1`: the positions `[k, u]` are done,
`ps` are the positions of the literals collected so far, from the top. `M` are the MARKs at
`build`. `processedPos` is the backjump point found so far. -/
structure BState (input : Input) (T : solver) (D : Nat) (M : Nat → Prop) (u k : Nat) (ps : List Nat)
    (S : solver) : Prop where
  fields : AFields T S
  low : SameLow T S
  model : ∀ q, 0 ≤ q → q ≤ T.nVars → S.ld q = T.ld q
  order : ∃ vs, OrderList S vs
  assigned : S.assigned = T.falseStack + u
  k_ge : forcedPos T ≤ k
  k_le : k ≤ u + 1
  cache : Cache input T S M k
  marks : ∀ i < k, M i → Marked T S i
  done : ∀ i, k ≤ i → i ≤ u → flag S (trailAt T i) = 1
  above : ∀ i, u < i → i < trailLen T → flag S (trailAt T i) = 0
  off : ∀ l, InRange T.nVars l → (∀ i < trailLen T, trailAt T i ≠ l) → flag S l = 0
  zero : flag S 0 = 0
  noImp : NoImp T S D u
  buffer : ∀ m (h : m < ps.length), S.ld (S.buffer + m) = trailAt T ps[m]
  ps_mem : ∀ q ∈ ps, k ≤ q ∧ q ≤ u ∧ M q
  sorted : ps.Pairwise (· > ·)
  cover : ∀ i, k ≤ i → i ≤ u → M i → i ∈ ps ∨ Imp input T M i
  head : k ≤ u → ps.head? = some u
  B_le : processedPos S ≤ u
  B_ge : k ≤ processedPos S + 1
  B_ge' : k ≤ u → k ≤ processedPos S
  proc_ge : T.falseStack ≤ S.processed
  B_dec : processedPos S = u ∨ IsDecision T (processedPos S)
  B_low : k ≤ D → IsDecision T (processedPos S) ∧ processedPos S ≤ D
  tail_lt : ∀ q ∈ ps.tail, q < processedPos S
  gap : ∀ d, IsDecision T d → d < processedPos S →
    (2 ≤ ps.length → ps[1]! < d → False) ∧ (ps.length ≤ 1 → k ≤ d → False)

/-- The MARKs at `build`. -/
def MarksAt (T Sb : solver) (u : Nat) (i : Nat) : Prop := i ≤ u ∧ Marked T Sb i

/-- The minimization loop's invariant, from the state `Sb` at `build`. -/
def BLoop (input : Input) (T : solver) (D : Nat) (Sb S : solver) (size p : CInt) : Prop :=
  ∃ u k ps, BuildStart input T D Sb u ∧ BState input T D (MarksAt T Sb u) u k ps S ∧
    size = ps.length ∧ p + 1 = T.falseStack + k

/-- The unassign loop (C:127–128) from the state `Se` after minimization: positions above
`a` up to the old `assigned` are unassigned. -/
def UInv (T Se S : solver) : Prop :=
  ∃ a : Nat, AFields T S ∧ S.processed = Se.processed ∧ S.head = Se.head ∧ S.assigned = T.falseStack + a ∧
    processedPos Se ≤ a ∧ (a : CInt) ≤ Se.assigned - T.falseStack ∧
    (∀ q, 0 ≤ q → (∀ i : Nat, a < i → (i : CInt) ≤ Se.assigned - T.falseStack → q ≠ Se.false + trailAt T i) →
      S.ld q = Se.ld q) ∧
    ∀ i : Nat, a < i → (i : CInt) ≤ Se.assigned - T.falseStack → flag S (trailAt T i) = 0

section Basic
variable {input : Input} {T : solver} {db : Records} {vs : List CInt} {D : Nat}

/-- The numbers `omega` needs about the conflict state. -/
theorem ACtx.num (ctx : ACtx input T db vs D) :
    1 ≤ T.nVars ∧ trailLen T ≤ T.nVars.toNat ∧ T.model = 0 ∧ T.next = T.nVars + 1 ∧
    T.prev = 2 * T.nVars + 2 ∧ T.buffer = 3 * T.nVars + 3 ∧ T.reason = 4 * T.nVars + 3 ∧
    T.falseStack = 5 * T.nVars + 4 ∧ T.false = 7 * T.nVars + 5 ∧ T.first = 9 * T.nVars + 6 ∧
    T.falseStack ≤ T.forced ∧ T.forced ≤ T.processed ∧ T.processed ≤ T.assigned ∧
    (trailLen T : CInt) = T.assigned - T.falseStack ∧ (forcedPos T : CInt) = T.forced - T.falseStack := by
  have hl := ctx.core.layout; have hn := hl.num; have ht := ctx.core.trail
  have := ht.forced_le; have := ht.processed_le; have := ht.assigned_le
  refine ⟨hl.nVars_pos, ht.len_le, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2.1, hn.2.2.2.2.1, hn.2.2.2.2.2.1,
    hn.2.2.2.2.2.2.1, hn.2.2.2.2.2.2.2, ht.forced_le, ht.processed_le, ht.assigned_le, ?_, ?_⟩ <;>
    simp only [trailLen, forcedPos] <;> omega

/-- A trail literal is a literal of the problem. -/
theorem ACtx.lit (ctx : ACtx input T db vs D) {i : Nat} (hi : i < trailLen T) :
    trailAt T i ≠ 0 ∧ -T.nVars ≤ trailAt T i ∧ trailAt T i ≤ T.nVars :=
  inRange_iff.mp (ctx.core.trail.lit i hi)

/-- Equal trail literals sit at equal positions. -/
theorem ACtx.pos_eq (ctx : ACtx input T db vs D) {i j : Nat} (hi : i < trailLen T) (hj : j < trailLen T)
    (he : trailAt T i = trailAt T j) : i = j :=
  ctx.core.trail.distinct i hi j hj (by rw [he])

/-- A position at or above the last decision is not at the root. -/
theorem ACtx.not_root (ctx : ACtx input T db vs D) {i : Nat} (hi : D ≤ i) : ¬ RootLevel T i :=
  fun h => h D hi ctx.dec

/-- Root literals are false in every model. -/
theorem ACtx.root_false (ctx : ACtx input T db vs D) {i : Nat} (hi : i < trailLen T) (hr : RootLevel T i)
    {a : Assignment} (ha : input.Sat a) : ¬ LitTrue a (trailAt T i) := by
  obtain ⟨l, hl, ht⟩ := ctx.core.root i hi hr a ha
  simp only [List.mem_singleton] at hl
  subst hl
  exact LitTrue.not_of_neg (ctx.lit hi).1 ht

/-- `T` itself has `T`'s fields. -/
theorem AFields.refl (T : solver) : AFields T T :=
  ⟨T.DB, T.assigned, T.processed, T.head, T.res, T.nConflicts, T.fast, T.slow, rfl⟩

/-- The array pointers and `nVars` are `T`'s. -/
theorem AFields.shape {S : solver} (h : AFields T S) : SameShape T S := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The counters and bounds are `T`'s. -/
theorem AFields.eqs {S : solver} (h : AFields T S) :
    S.nVars = T.nVars ∧ S.forced = T.forced ∧ S.mem_used = T.mem_used ∧ S.mem_fixed = T.mem_fixed ∧
    S.nLemmas = T.nLemmas ∧ S.maxLemmas = T.maxLemmas ∧ S.mem_max = T.mem_max ∧ S.nClauses = T.nClauses := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- A write keeps the fields. -/
theorem AFields.st {S : solver} (h : AFields T S) (q v : CInt) : AFields T (S.st q v) := by
  obtain ⟨DB, a, p, hd, r, nc, fa, sl, rfl⟩ := h
  obtain ⟨DB', e⟩ := st_eq ({ T with
    DB := DB, assigned := a, processed := p, head := hd, res := r, nConflicts := nc, fast := fa,
    slow := sl } : solver) q v
  rw [e]; exact ⟨DB', a, p, hd, r, nc, fa, sl, rfl⟩

/-- Changing only the fields `analyze` writes keeps `AFields`. -/
theorem AFields.upd {S : solver} (h : AFields T S) (DB : Array CInt) (a p hd r nc fa sl : CInt) :
    AFields T ({ S with
      DB := DB, assigned := a, processed := p, head := hd, res := r, nConflicts := nc, fast := fa,
      slow := sl } : solver) := by
  obtain ⟨_, _, _, _, _, _, _, _, rfl⟩ := h; exact ⟨DB, a, p, hd, r, nc, fa, sl, rfl⟩

/-- A write outside the cells `SameLow` and the model frame keep. -/
def Writable (T : solver) (q : CInt) : Prop :=
  1 ≤ T.nVars ∧ T.nVars < q ∧ (q < 4 * T.nVars + 4 ∨ (6 * T.nVars + 4 < q ∧ q < 8 * T.nVars + 6))

/-- A writable cell can be written without changing the cells `SameLow` keeps. -/
theorem SameLow.st {S : solver} (h : SameLow T S) {q : CInt} (hq : Writable T q) (v : CInt) :
    SameLow T (S.st q v) := by
  have hs := h.shape
  refine ⟨hs.trans (SameShape.st _ _ _), fun q' h1 h2 => ?_, fun q' h1 => ?_⟩
  · rw [ld_st _ _ (by unfold Writable at hq; omega) (by omega), if_neg (by unfold Writable at hq; omega)]
    exact h.mid q' h1 h2
  · rw [ld_st _ _ (by unfold Writable at hq; omega) (by unfold Writable at hq; omega),
      if_neg (by unfold Writable at hq; omega)]
    exact h.high q' h1

/-- Flag cells are writable. -/
theorem ACtx.writable_flag (ctx : ACtx input T db vs D) {l : CInt} (hl : -T.nVars ≤ l ∧ l ≤ T.nVars) :
    Writable T (T.false + l) := by
  have := ctx.num; unfold Writable; omega

/-- Buffer cells are writable. -/
theorem ACtx.writable_buffer (ctx : ACtx input T db vs D) {m : CInt} (h0 : 0 ≤ m) (hm : m ≤ T.nVars) :
    Writable T (T.buffer + m) := by
  have := ctx.num; unfold Writable; omega

/-- A trail cell of a state with `T`'s low cells. -/
theorem SameLow.trail {S : solver} (h : SameLow T S) (ctx : ACtx input T db vs D) {i : Nat}
    (hi : i < trailLen T) : S.ld (T.falseStack + i) = trailAt T i := by
  have := ctx.num
  exact h.mid _ (by omega) (by omega)

/-- A reason cell of a state with `T`'s low cells. -/
theorem SameLow.reason {S : solver} (h : SameLow T S) (ctx : ACtx input T db vs D) {l : CInt}
    (hl : l ≠ 0 ∧ -T.nVars ≤ l ∧ l ≤ T.nVars) : S.ld (T.reason + abs l) = reasonOf T l := by
  have := ctx.num
  have : 1 ≤ abs l ∧ abs l ≤ T.nVars := by rcases abs_cases l with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
  exact h.mid _ (by omega) (by omega)

/-- The layout of a state with `T`'s fields and high cells. -/
theorem ACtx.layout (ctx : ACtx input T db vs D) {S : solver} (hf : AFields T S) (hl : SameLow T S) :
    Layout S :=
  ctx.core.layout.frame hf.shape (hl.high _ (by have := ctx.num; simp only [clausesAt]; omega))

end Basic

end MicrosatLean.Faithful.Verification
