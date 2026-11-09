import MicrosatLean.Faithful.Verification.Invariant
import MicrosatLean.Faithful.Verification.Counting

/-!
# At most `3^n` lemmas

Lemmas are pairwise distinct (up to literal order) and use each variable at most once,
so each is determined by its key: for each variable, "absent", "positive" or
"negative". There are `3^n` keys. This bounds `nLemmas` for the termination rank.
-/

namespace MicrosatLean.Faithful.Verification

/-- Elements of a list with no repeated images are determined by their images. -/
theorem nodup_map_inj {α β : Type} {f : α → β} {l : List α} (h : (l.map f).Nodup) {a b : α}
    (ha : a ∈ l) (hb : b ∈ l) (he : f a = f b) : a = b := by
  induction l with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.map_cons, List.nodup_cons] at h
    obtain ⟨hx, hxs⟩ := h
    simp only [List.mem_cons] at ha hb
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · rw [ha, hb]
    · subst ha; exact absurd (List.mem_map.mpr ⟨b, hb, he.symm⟩) hx
    · subst hb; exact absurd (List.mem_map.mpr ⟨a, ha, he⟩) hx
    · exact ih hxs ha hb

/-- The key of a clause over `n` variables: for each variable, positive, negative or absent. -/
def clauseKey (n : Nat) (l : List CInt) : List (Option Bool) :=
  (List.range n).map fun (i : Nat) => if ((i : CInt) + 1) ∈ l then some true
    else if -((i : CInt) + 1) ∈ l then some false else none

/-- All keys of length `n`. -/
def allKeys : Nat → List (List (Option Bool))
  | 0 => [[]]
  | n + 1 => (allKeys n).map (none :: ·) ++ (allKeys n).map (some true :: ·) ++
      (allKeys n).map (some false :: ·)

theorem allKeys_length (n : Nat) : (allKeys n).length = 3 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [allKeys, List.length_append, List.length_map, ih, Nat.pow_succ]; omega

theorem mem_allKeys (k : List (Option Bool)) : k ∈ allKeys k.length := by
  induction k with
  | nil => simp [allKeys]
  | cons x ks ih =>
    simp only [List.length_cons, allKeys, List.mem_append, List.mem_map]
    rcases x with _ | _ | _
    · exact Or.inl (Or.inl ⟨ks, ih, rfl⟩)
    · exact Or.inr ⟨ks, ih, rfl⟩
    · exact Or.inl (Or.inr ⟨ks, ih, rfl⟩)

/-- A literal of a clause over distinct variables is in every clause with the same key. -/
theorem clauseKey_mem {N : CInt} {l1 l2 : List CInt} (h1 : (l1.map Int.natAbs).Nodup)
    (r1 : ∀ x ∈ l1, InRange N x) (he : clauseKey N.toNat l1 = clauseKey N.toNat l2) {x : CInt}
    (hx : x ∈ l1) : x ∈ l2 := by
  have hr := inRange_iff.mp (r1 x hx)
  have hi : (x.natAbs - 1) < N.toNat := by omega
  have hk := congrArg (·[x.natAbs - 1]?) he
  simp only [clauseKey, List.getElem?_map, List.getElem?_range hi, Option.map_some] at hk
  have hcast : (((x.natAbs - 1 : Nat) : CInt) + 1) = (x.natAbs : CInt) := by omega
  rw [hcast] at hk
  rcases Int.natAbs_eq x with hp | hn
  · -- `x` is positive
    have hpos : (x.natAbs : CInt) = x := by omega
    rw [hpos, if_pos hx] at hk
    by_cases h2 : x ∈ l2
    · exact h2
    · rw [if_neg h2] at hk; split at hk <;> simp at hk
  · -- `x` is negative: its opposite is not in `l1`
    have hneg : (x.natAbs : CInt) = -x := by omega
    rw [hneg, Int.neg_neg] at hk
    have hno : -x ∉ l1 := fun hm => by
      have := nodup_map_inj h1 hm hx (by simp)
      omega
    rw [if_neg hno, if_pos hx] at hk
    by_cases h2 : -x ∈ l2
    · rw [if_pos h2] at hk; simp at hk
    · rw [if_neg h2] at hk; split at hk
      · assumption
      · simp at hk

/-- Two clauses over distinct variables with the same key are reorderings of each other. -/
theorem clauseKey_perm {N : CInt} {l1 l2 : List CInt} (h1 : (l1.map Int.natAbs).Nodup)
    (h2 : (l2.map Int.natAbs).Nodup) (r1 : ∀ x ∈ l1, InRange N x) (r2 : ∀ x ∈ l2, InRange N x)
    (he : clauseKey N.toNat l1 = clauseKey N.toNat l2) : l1.Perm l2 := by
  have n1 : l1.Nodup := List.Pairwise.of_map Int.natAbs (fun a b hab he => hab (by rw [he])) h1
  have n2 : l2.Nodup := List.Pairwise.of_map Int.natAbs (fun a b hab he => hab (by rw [he])) h2
  exact (List.perm_ext_iff_of_nodup n1 n2).mpr fun x =>
    ⟨clauseKey_mem h1 r1 he, clauseKey_mem h2 r2 he.symm⟩

/-- Clauses over distinct variables of the problem, pairwise not reorderings of each
other, number at most `3^n`. -/
theorem lemmas_count_le {N : CInt} {L : List Record}
    (shape : ∀ r ∈ L, (r.2.map Int.natAbs).Nodup ∧ ∀ l ∈ r.2, InRange N l)
    (distinct : L.Pairwise (fun r s => ¬ r.2.Perm s.2)) : L.length ≤ clauseBound N := by
  simp only [clauseBound]
  have hkeys : (L.map fun r => clauseKey N.toNat r.2).Nodup := by
    rw [List.Nodup, List.pairwise_map]
    refine distinct.imp_of_mem fun {r s} hr hs hrs he => hrs ?_
    have sr := shape r hr; have ss := shape s hs
    exact clauseKey_perm sr.1 ss.1 sr.2 ss.2 he
  have hsub : (L.map fun r => clauseKey N.toNat r.2) ⊆ allKeys N.toNat := by
    intro k hk
    obtain ⟨r, _, rfl⟩ := List.mem_map.mp hk
    have := mem_allKeys (clauseKey N.toNat r.2)
    simpa [clauseKey] using this
  have := hkeys.length_le_of_subset hsub
  rw [List.length_map, allKeys_length] at this
  exact this

/-- The database holds at most `3^n` lemmas. Used by `step_decreases` (the rank's
second component). -/
theorem nLemmas_le_bound {input : Input} {S : solver} {db : Records} (h : Database input S db) :
    S.nLemmas.toNat ≤ clauseBound S.nVars := by
  rw [h.nLemmas]
  simp only [Int.toNat_natCast]
  exact lemmas_count_le (fun r hr => ⟨(h.lemma_shape r hr).2.1, (h.lemma_shape r hr).2.2⟩) h.lemma_distinct

/-- A clause over distinct variables has at most `n` literals. -/
theorem clause_length_le {N : CInt} {l : List CInt} (hnd : (l.map Int.natAbs).Nodup)
    (hr : ∀ x ∈ l, InRange N x) : l.length ≤ N.toNat := by
  have := card_le_of_distinct (N := N.toNat) (m := l.length) (fun i => if h : i < l.length then l[i].natAbs else 0)
    (fun i hi => by
      have := inRange_iff.mp (hr _ (List.getElem_mem hi)); simp only [hi, dite_true]; omega)
    (fun i hi j hj he => by
      simp only [hi, hj, dite_true] at he
      have := (List.pairwise_iff_getElem.mp hnd)
      refine Classical.byContradiction fun hne => ?_
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · exact this i j (by simpa using hi) (by simpa using hj) hlt (by simpa using he)
      · exact this j i (by simpa using hj) (by simpa using hi) hlt (by simpa using he.symm))
  exact this

/-- The cells of the lemma records: at most `3^n` records of at most `n + 3` cells. -/
theorem lemmas_size_le {N : CInt} (hN : 1 ≤ N) {L : List Record}
    (shape : ∀ r ∈ L, (r.2.map Int.natAbs).Nodup ∧ ∀ l ∈ r.2, InRange N l)
    (distinct : L.Pairwise (fun r s => ¬ r.2.Perm s.2)) :
    (L.map fun r => (r.2.length : CInt) + 3).sum ≤ (clauseBound N : CInt) * (N + 3) := by
  have hcount := lemmas_count_le shape distinct
  have hle : (L.map fun r => (r.2.length : CInt) + 3).sum ≤ (L.length : CInt) * (N + 3) := by
    clear distinct hcount
    induction L with
    | nil => simp
    | cons r rs ih =>
      have h1 := clause_length_le (shape r (by simp)).1 (shape r (by simp)).2
      have h2 := ih (fun s hs => shape s (by simp [hs]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      push_cast
      have : ((r.2.length : Nat) : CInt) ≤ N := by omega
      rw [Int.add_mul, Int.one_mul]
      omega
  have : (L.length : CInt) * (N + 3) ≤ (clauseBound N : CInt) * (N + 3) :=
    Int.mul_le_mul_of_nonneg_right (by exact_mod_cast hcount) (by omega)
  omega

/-- A tiling ends after its records. -/
theorem Tiling.end_eq {S : solver} {a b : Ptr} {rs : List Record} (h : Tiling S a b rs) :
    b = a + (rs.map fun r => (r.2.length : CInt) + 3).sum := by
  induction h with
  | nil => simp
  | cons _ _ ih => simp only [List.map_cons, List.sum_cons]; omega

/-- The input records take as many cells as the input clauses. -/
theorem Database.inputs_sum {input : Input} {S : solver} {db : Records} (h : Database input S db) :
    (db.inputs.map fun r => (r.2.length : CInt) + 3).sum =
      (input.clauses.toList.map fun c => (c.size : CInt) + 3).sum := by
  congr 1
  apply List.ext_getElem (by simp [h.inputs_length])
  intro i h1 h2
  have hi : i < db.inputs.length := by simpa using h1
  have hi' : i < input.clauses.size := by rw [← h.inputs_length]; exact hi
  simp only [List.getElem_map, (h.inputs_perm i hi hi').length_eq, Array.getElem_toList, Array.length_toList]

/-- The records fit in memory (E3): `mem_used ≤ memoryBound ≤ mem_max`. Used whenever
`addClause` must not run out of memory. -/
theorem Core.used_le_bound {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) :
    S.mem_used = clausesAt S.nVars + (input.clauses.toList.map fun c => (c.size : CInt) + 3).sum +
      (db.lemmas.map fun r => (r.2.length : CInt) + 3).sum := by
  have hd := h.database
  have e1 := hd.inputs_tile.end_eq
  have e2 := hd.lemmas_tile.end_eq
  rw [hd.inputs_sum] at e1
  omega

theorem Core.used_le_max {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) : S.mem_used ≤ S.mem_max := by
  have hd := h.database
  have hl := lemmas_size_le h.layout.nVars_pos
    (fun r hr => ⟨(hd.lemma_shape r hr).2.1, (hd.lemma_shape r hr).2.2⟩) hd.lemma_distinct
  have hm := h.memory
  simp only [memoryBound] at hm
  rw [← h.nVars] at hm
  have := h.used_le_bound
  omega

end MicrosatLean.Faithful.Verification
