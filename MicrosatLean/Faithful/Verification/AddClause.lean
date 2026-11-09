import MicrosatLean.Faithful.Microsat
import MicrosatLean.Faithful.Verification.Memory
import Std.Tactic.Do

/-!
# `getMemory`, `addWatch` and `addClause` (C:49–66)

`addClause` allocates a record `[link0, link1, lits…, 0]` at `mem_used`, links its
two watches (for clauses of two or more literals) and copies the literals from `in`.
`addClause_spec` covers a source below the new record, as from `buffer` (`parse`,
`analyze`); `reduceDB`'s in-place copy has its own lemma there.
-/

namespace MicrosatLean.Faithful.Verification

open Std.Do
set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- `getMemory` changes only `mem_used`: by `k` when there is room (C:55–56); the
out-of-memory case (excluded by E3) leaves it unchanged. -/
theorem getMemory_fst (S : solver) (k : CInt) :
    (getMemory S k).1 = { S with mem_used :=
      if S.mem_used + k > S.mem_max then S.mem_used else S.mem_used + k } := by
  unfold getMemory; split <;> simp

/-- The pointer `getMemory` returns: the old `mem_used` (C:55, C:57). -/
@[simp] theorem getMemory_snd (S : solver) (k : CInt) : (getMemory S k).2 = S.mem_used := by
  unfold getMemory; split <;> simp

/-- Reading memory depends only on `DB`. -/
@[simp] theorem ld_with_mem_used (S : solver) (m p : CInt) :
    ({ S with mem_used := m } : solver).ld p = S.ld p := rfl

/-- Cell `q` once `addClause` has allocated at `u = mem_used` and linked its two watches:
link 0 and link 1 hold the old list heads, and the heads point to them (C:62–63). -/
def afterWatches (S0 : solver) (L : List CInt) (q : CInt) : CInt :=
  let u := S0.mem_used
  if 1 < L.length then
    let h0 := S0.first + L[0]!
    let h1 := S0.first + L[1]!
    if q = u then S0.ld h0 else if q = h0 then u
    else if q = u + 1 then S0.ld h1 else if q = h1 then u + 1 else S0.ld q
  else S0.ld q

/-- Loop invariant of the copy loop (C:64): the literals in `pre` are copied. -/
def Copied (S0 : solver) (L : List CInt) (pre : List CInt) (S : solver) : Prop :=
  (∃ DB, S = { S0 with DB := DB, mem_used := S0.mem_used + L.length + 3 }) ∧
  (∀ v ∈ pre, S.ld (S0.mem_used + 2 + v) = L[v.toNat]!) ∧
  (∀ q, 0 ≤ q → (∀ v ∈ pre, q ≠ S0.mem_used + 2 + v) → S.ld q = afterWatches S0 L q)

/-- The fields after `addClause`: only `DB`, `mem_used` and the statistics change (C:65). -/
def added (S0 : solver) (size irr : CInt) (DB : Array CInt) : solver :=
  { S0 with
    DB := DB
    mem_used := S0.mem_used + size + 3
    mem_fixed := if irr != 0 then S0.mem_used + size + 3 else S0.mem_fixed
    nLemmas := if irr != 0 then S0.nLemmas else S0.nLemmas + 1 }

/-- One iteration of the copy loop (C:64) keeps `Copied`: cell `clause + x` gets the
source literal, which no earlier write touched. -/
theorem copied_step {S0 S : solver} {L pre suff : List CInt} {in_ size x : CInt}
    (hsize : size = L.length) (hin : 0 ≤ in_) (hsrc_le : in_ + size ≤ S0.mem_used ∨ (0 ≤ S0.mem_used ∧ S0.mem_used + 2 ≤ in_))
    (hsrc : ∀ i (h : i < L.length), S0.ld (in_ + i) = L[i])
    (hheads : 1 < L.length → ∀ i < 2, 0 ≤ S0.first + L[i]! ∧ S0.first + L[i]! < S0.mem_used ∧
       (S0.first + L[i]! < in_ ∨ in_ + size ≤ S0.first + L[i]!))
    (hlist : (0...size).toList = pre ++ x :: suff) (hinv : Copied S0 L pre S) :
    Copied S0 L (pre ++ [x]) (S.st (S0.mem_used + 2 + x) (S.ld (in_ + x))) := by
  obtain ⟨⟨DB, hS⟩, hcopied, hrest⟩ := hinv
  have hmemb : ∀ v, v ∈ (0...size).toList ↔ 0 ≤ v ∧ v < size := by
    intro v; simp [Std.Rco.mem_toList_iff_mem, Std.Rco.mem_iff]
  have hx : 0 ≤ x ∧ x < size := (hmemb x).1 (by rw [hlist]; simp)
  have hpre : ∀ v ∈ pre, 0 ≤ v ∧ v < size ∧ v < x := by
    intro v hv
    have hsorted : ((0...size).toList).Pairwise (· < ·) := Std.Rco.pairwise_toList_lt
    rw [hlist] at hsorted
    refine ⟨((hmemb v).1 (by rw [hlist]; simp [hv])).1, ((hmemb v).1 (by rw [hlist]; simp [hv])).2, ?_⟩
    exact (List.pairwise_append.mp hsorted).2.2 v hv x List.mem_cons_self
  have hu : 0 ≤ S0.mem_used := by omega
  -- the source literal is still the one from `S0`
  have hval : S.ld (in_ + x) = L[x.toNat]! := by
    rw [hrest (in_ + x) (by omega) (fun v hv => by have := hpre v hv; omega)]
    have hxl : x.toNat < L.length := by omega
    have hsx := hsrc x.toNat hxl
    rw [show (x.toNat : CInt) = x by omega] at hsx
    unfold afterWatches
    split
    · rename_i hl
      have h0 := hheads hl 0 (by omega); have h1 := hheads hl 1 (by omega)
      simp only
      rw [ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega), ite_eq_right_iff.mpr (by omega)]
      rw [hsx, getElem!_pos L x.toNat hxl]
    · rw [hsx, getElem!_pos L x.toNat hxl]
  refine ⟨⟨(S.st (S0.mem_used + 2 + x) (S.ld (in_ + x))).DB, ?_⟩, ?_, ?_⟩
  · apply solver.ext <;> simp [hS]
  · intro v hv
    simp only [List.mem_append, List.mem_singleton] at hv
    rcases hv with hv | rfl
    · have := hpre v hv
      rw [ld_st_of_ne _ _ (by omega) (by omega) (by omega)]
      exact hcopied v hv
    · rw [ld_st_self _ _ (by omega), hval]
  · intro q hq hne
    have hqx : q ≠ S0.mem_used + 2 + x := hne x (by simp)
    rw [ld_st_of_ne _ _ (by omega) hq hqx]
    exact hrest q hq (fun v hv => hne v (by simp [hv]))

/-- `addWatch` (C:49–50) as two stores. -/
theorem addWatch_eq (S : solver) (lit : CInt) (mem : Ptr) :
    addWatch S lit mem = (S.st mem (S.ld (S.first + lit))).st (S.first + lit) mem := by
  simp [addWatch]

/-- What `addClause` guarantees: the record holds `L` and its terminator at `mem_used + 2`,
the cells below hold `afterWatches`, those above are untouched, and only `DB`,
`mem_used`, `mem_fixed`/`nLemmas` change (C:59–66). -/
def AddClausePost (S0 : solver) (L : List CInt) (size irr : CInt) (r : solver × Ptr) : Prop :=
  r.2 = S0.mem_used + 2 ∧ r.1.mem_used = S0.mem_used + size + 3 ∧
    (∀ i (h : i < L.length), r.1.ld (r.2 + i) = L[i]) ∧ r.1.ld (r.2 + size) = 0 ∧
    (∀ q, 0 ≤ q → q < r.2 → r.1.ld q = afterWatches S0 L q) ∧
    (∀ q, r.2 + size < q → r.1.ld q = S0.ld q) ∧
    ∃ DB, r.1 = added S0 size irr DB

/-- The end of `addClause` (C:64–66): from the finished copy loop, writing the
terminator and updating the statistics gives `AddClausePost`, for any final state `T`
with the same memory and the expected fields. -/
theorem post_of_copied {S0 r : solver} {L : List CInt} {in_ size irr : CInt}
    (hsize : size = L.length) (hin : 0 ≤ in_) (hsrc_le : in_ + size ≤ S0.mem_used ∨ (0 ≤ S0.mem_used ∧ S0.mem_used + 2 ≤ in_))
    (hheads : 1 < L.length → ∀ i < 2, 0 ≤ S0.first + L[i]! ∧ S0.first + L[i]! < S0.mem_used ∧
       (S0.first + L[i]! < in_ ∨ in_ + size ≤ S0.first + L[i]!))
    (hinv : Copied S0 L (0...size).toList r) (T : solver)
    (hld : ∀ q, T.ld q = (r.st (S0.mem_used + 2 + size) 0).ld q)
    (hfields : ∃ DB, T = added S0 size irr DB) :
    AddClausePost S0 L size irr (T, S0.mem_used + 2) := by
  obtain ⟨⟨DB, hS⟩, hcopied, hrest⟩ := hinv
  have hmemb : ∀ v, v ∈ (0...size).toList ↔ 0 ≤ v ∧ v < size := by
    intro v; simp [Std.Rco.mem_toList_iff_mem, Std.Rco.mem_iff]
  have hu : 0 ≤ S0.mem_used := by omega
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, hfields⟩
  · obtain ⟨DB', hT⟩ := hfields; simp [hT, added]
  · intro i hi
    have hi' : (i : CInt) ∈ (0...size).toList := (hmemb i).2 (by omega)
    show T.ld (S0.mem_used + 2 + i) = L[i]
    rw [hld, ld_st_of_ne _ _ (by omega) (by omega) (by omega), hcopied _ hi']
    simp [getElem!_pos L i hi]
  · show T.ld (S0.mem_used + 2 + size) = 0
    rw [hld, ld_st_self _ _ (by omega)]
  · intro q hq hlt
    rw [hld, ld_st_of_ne _ _ (by omega) hq (by omega)]
    exact hrest q hq (fun v hv => by have := (hmemb v).1 hv; omega)
  · intro q hlt
    rw [hld, ld_st_of_ne _ _ (by omega) (by omega) (by omega),
      hrest q (by omega) (fun v hv => by have := (hmemb v).1 hv; omega)]
    unfold afterWatches
    split
    · rename_i hl
      have h0 := hheads hl 0 (by omega); have h1 := hheads hl 1 (by omega)
      simp only
      rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), if_neg (by omega)]
    · rfl

/-- `addClause` copying the clause `L` from `in_`, which lies below the new record
(as `buffer` does). Used by `parse_correct` and `analyze`'s proof. -/
theorem addClause_spec (S0 : solver) (L : List CInt) (in_ size irr : CInt)
    (hsize : size = L.length) (hin : 0 ≤ in_) (hsrc_le : in_ + size ≤ S0.mem_used ∨ (0 ≤ S0.mem_used ∧ S0.mem_used + 2 ≤ in_))
    (hsrc : ∀ i (h : i < L.length), S0.ld (in_ + i) = L[i])
    (hmem : S0.mem_used + size + 3 ≤ S0.mem_max)
    (hheads : 1 < L.length → ∀ i < 2, 0 ≤ S0.first + L[i]! ∧ S0.first + L[i]! < S0.mem_used ∧
       (S0.first + L[i]! < in_ ∨ in_ + size ≤ S0.first + L[i]!))
    (hdistinct : 1 < L.length → L[0]! ≠ L[1]!) :
    AddClausePost S0 L size irr (addClause S0 in_ size irr) := by
  generalize hR : addClause S0 in_ size irr = R
  apply Id.of_wp_run_eq hR
  mvcgen [addClause] invariants
  · ⇓⟨cur, S⟩ => ⌜Copied S0 L cur.prefix S⌝
  · ⇓⟨cur, S⟩ => ⌜Copied S0 L cur.prefix S⌝
  case vc1.step =>
    rename_i used G clause _ _ W1 W2 pre x suff hlist B S' hinv
    have hcl : clause = S0.mem_used + 2 := by simp [clause]
    show Copied S0 L _ (B.st (clause + x) (B.ld (in_ + x)))
    rw [hcl]
    exact copied_step hsize hin hsrc_le hsrc hheads hlist hinv
  case vc5.step =>
    rename_i used G clause _ _ pre x suff hlist B S' hinv
    have hcl : clause = S0.mem_used + 2 := by simp [clause]
    show Copied S0 L _ (B.st (clause + x) (B.ld (in_ + x)))
    rw [hcl]
    exact copied_step hsize hin hsrc_le hsrc hheads hlist hinv
  case vc6.isFalse.pre =>
    rename_i used G clause _ hsz
    have hl : ¬ 1 < L.length := by omega
    have hG : G = { S0 with mem_used := S0.mem_used + (size + 3) } := by
      simp only [G, getMemory_fst]; rw [if_neg (by omega)]
    rw [hG]
    refine ⟨⟨_, by apply solver.ext <;> first | rfl | (simp <;> omega)⟩, by simp, ?_⟩
    intro q _ _
    simp [afterWatches, hl]
  case vc2.isTrue.pre =>
    rename_i used G clause _ hsz W1 W2
    have hl : 1 < L.length := by omega
    obtain ⟨h0n, h0lt, h0src⟩ := hheads hl 0 (by omega)
    obtain ⟨h1n, h1lt, h1src⟩ := hheads hl 1 (by omega)
    have hL0 : L[0]! = L[0] := getElem!_pos L 0 (by omega)
    have hL1 : L[1]! = L[1] := getElem!_pos L 1 (by omega)
    have hdist : L[0] ≠ L[1] := by rw [← hL0, ← hL1]; exact hdistinct hl
    have hlit0 : S0.ld in_ = L[0] := by simpa using hsrc 0 (by omega)
    have hlit1 : S0.ld (in_ + 1) = L[1] := by simpa using hsrc 1 (by omega)
    rw [hL0] at h0n h0lt h0src
    rw [hL1] at h1n h1lt h1src
    have hG : G = { S0 with mem_used := S0.mem_used + (size + 3) } := by
      simp only [G, getMemory_fst]; rw [if_neg (by omega)]
    show Copied S0 L [] (addWatch W1 (W1.ld (in_ + 1)) (used + 1))
    simp only [W1, hG, used, addWatch_eq]
    refine ⟨⟨_, by apply solver.ext <;> first | rfl | (simp <;> omega)⟩, by simp, ?_⟩
    intro q hq _
    have hd : S0.first + L[0] ≠ S0.first + L[1] := by intro h; exact hdist (by omega)
    have a1 : S0.first + L[0] ≠ S0.mem_used := by omega
    have a2 : S0.first + L[0] ≠ S0.mem_used + 1 := by omega
    have a3 : S0.first + L[1] ≠ S0.mem_used := by omega
    have a4 : S0.first + L[1] ≠ S0.mem_used + 1 := by omega
    have a5 : S0.first + L[1] ≠ S0.first + L[0] := Ne.symm hd
    have a6 : (S0.mem_used + 1 : CInt) ≠ S0.mem_used := by omega
    have a7 : S0.first + L[0] ≠ in_ + 1 := by omega
    have a8 : S0.mem_used ≠ in_ + 1 := by omega
    simp +zetaDelta (disch := omega) [ld_st, hlit0, hlit1, afterWatches, hl, hL0, hL1,
      a1, a2, a3, a4, a5, a6, a7, a8, Ne.symm a7, Ne.symm a8, hdist, Ne.symm hdist]
    repeat' split
    all_goals first | rfl | omega | (simp_all; done)
  case vc3.isTrue.post.success.isTrue =>
    rename_i used G clause _ _ _ _ r S'' _ hirr hinv
    have hcl : clause = S0.mem_used + 2 := by simp [clause]
    obtain ⟨DB, hS⟩ := hinv.1
    simp only [S'', hcl]
    refine post_of_copied hsize hin hsrc_le hheads hinv _ (fun q => rfl) ⟨?w3, ?h3⟩
    case h3 => apply solver.ext <;> first | rfl | (simp [added, hirr, hS] <;> omega) | simp [added, hirr, hS]
  case vc4.isTrue.post.success.isFalse =>
    rename_i used G clause _ _ _ _ r S'' _ hirr hinv
    have hcl : clause = S0.mem_used + 2 := by simp [clause]
    obtain ⟨DB, hS⟩ := hinv.1
    simp only [S'', hcl]
    refine post_of_copied hsize hin hsrc_le hheads hinv _ (fun q => rfl) ⟨?w4, ?h4⟩
    case h4 => apply solver.ext <;> first | rfl | (simp_all [added] <;> omega) | simp_all [added]
  case vc7.isFalse.post.success.isTrue =>
    rename_i used G clause _ _ r S'' _ hirr hinv
    have hcl : clause = S0.mem_used + 2 := by simp [clause]
    obtain ⟨DB, hS⟩ := hinv.1
    simp only [S'', hcl]
    refine post_of_copied hsize hin hsrc_le hheads hinv _ (fun q => rfl) ⟨?w7, ?h7⟩
    case h7 => apply solver.ext <;> first | rfl | (simp [added, hirr, hS] <;> omega) | simp [added, hirr, hS]
  case vc8.isFalse.post.success.isFalse =>
    rename_i used G clause _ _ r S'' _ hirr hinv
    have hcl : clause = S0.mem_used + 2 := by simp [clause]
    obtain ⟨DB, hS⟩ := hinv.1
    simp only [S'', hcl]
    refine post_of_copied hsize hin hsrc_le hheads hinv _ (fun q => rfl) ⟨?w8, ?h8⟩
    case h8 => apply solver.ext <;> first | rfl | (simp_all [added] <;> omega) | simp_all [added]

end MicrosatLean.Faithful.Verification
