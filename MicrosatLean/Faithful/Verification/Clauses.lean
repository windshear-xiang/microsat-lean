import MicrosatLean.Faithful.Verification.Invariant

/-!
# Facts about the records and the trail

Every record's literals are literals of the problem, without repeats (V1, V2 for
input records; `lemma_shape` for lemmas), and a literal is true in the saved phase
when its negation is on the trail.
-/

namespace MicrosatLean.Faithful.Verification

/-- Truth of a clause does not depend on the order of its literals. -/
theorem clauseSat_perm {a : Assignment} {l l' : List CInt} (h : l.Perm l') :
    ClauseSat a l ↔ ClauseSat a l' :=
  ⟨fun ⟨x, hx, ht⟩ => ⟨x, h.mem_iff.mp hx, ht⟩, fun ⟨x, hx, ht⟩ => ⟨x, h.mem_iff.mpr hx, ht⟩⟩

/-- Input record `i` holds the literals of input clause `i`. -/
theorem Database.input_perm {input : Input} {S : solver} {db : Records} (h : Database input S db)
    {r : Record} (hr : r ∈ db.inputs) :
    ∃ i, ∃ hi : i < input.clauses.size, r.2.Perm input.clauses[i].toList := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hr
  have hi' : i < input.clauses.size := by rw [← h.inputs_length]; exact hi
  exact ⟨i, hi', h.inputs_perm i hi hi'⟩

/-- Every literal of a record is a literal of the problem. -/
theorem Core.record_lit {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) {r : Record} (hr : r ∈ db.all) {l : CInt} (hl : l ∈ r.2) :
    InRange S.nVars l := by
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, hi, hp⟩ := h.database.input_perm hr
    have := h.valid.lit_range _ (Array.getElem_mem hi) l (by simpa using hp.mem_iff.mp hl)
    have hn := h.nVars
    refine ⟨this.1, ?_⟩
    omega
  · exact (h.database.lemma_shape r hr).2.2 l hl

/-- No record repeats a literal. -/
theorem Core.record_nodup {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) {r : Record} (hr : r ∈ db.all) : r.2.Nodup := by
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, hi, hp⟩ := h.database.input_perm hr
    exact hp.nodup_iff.mpr (h.valid.no_repeated_lit _ (Array.getElem_mem hi))
  · exact List.Pairwise.of_map Int.natAbs (fun a b hab he => hab (by rw [he]))
      (h.database.lemma_shape r hr).2.1

/-- A literal whose negation is false (on the trail) is true in the saved phase. -/
theorem Trail.litTrue {S : solver} (h : Trail S) {lit : CInt} {q : Nat} (hq : q < trailLen S)
    (he : trailAt S q = -lit) : LitTrue (modelOf S) lit := by
  have hm := h.model q hq
  rw [he, abs_neg', abs_eq_natAbs] at hm
  unfold LitTrue modelOf
  by_cases hp : 0 < lit
  · simp only [hp, decide_true, bne_iff_ne, ne_eq]
    exact hm.mpr (by omega)
  · simp only [hp, decide_false, bne_eq_false_iff_eq]
    exact Classical.byContradiction fun hne => hp (by have := hm.mp hne; omega)

/-- Following `prev` from the `k`-th variable of the order gives the next one, or 0
at the end. -/
theorem PrevChain.prev_getElem {S : solver} {v : CInt} {vs : List CInt} (h : PrevChain S v vs)
    (k : Nat) (hk : k < vs.length) : S.ld (S.prev + vs[k]) = vs[k + 1]?.getD 0 := by
  induction vs generalizing v k with
  | nil => simp at hk
  | cons w ws ih =>
    cases k with
    | zero =>
      have := h.2
      cases ws with
      | nil => simp only [PrevChain] at this; simpa using this
      | cons x xs => simp only [PrevChain] at this; simpa using this.1
    | succ k => simpa using ih h.2 k (by simpa using hk)

/-- The variables of the problem are distinct and nonzero, and so is the decision order. -/
theorem OrderList.nodup {S : solver} {vs : List CInt} (h : OrderList S vs) : vs.Nodup := by
  refine h.perm.nodup_iff.mpr ?_
  unfold vars
  exact List.Pairwise.map _ (fun a b hab he => hab (by omega)) List.nodup_range

/-- The decision order lists exactly the variables `1 … n`. -/
theorem OrderList.mem_iff {S : solver} {vs : List CInt} (h : OrderList S vs) {v : CInt} :
    v ∈ vs ↔ 1 ≤ v ∧ v ≤ S.nVars := by
  rw [h.perm.mem_iff, mem_vars]

/-- A variable is assigned exactly when one of its two literals has a nonzero
`false` flag (C:173). -/
theorem Trail.assigned_iff {S : solver} (h : Trail S) {v : CInt} (hv : 1 ≤ v ∧ v ≤ S.nVars) :
    (flag S v ≠ 0 ∨ flag S (-v) ≠ 0) ↔ Assigned S v := by
  constructor
  · intro hf
    refine Classical.byContradiction fun hna => ?_
    have off : ∀ x, abs x = v → flag S x = 0 := by
      intro x hx
      apply h.flag_off x
      · rw [inRange_iff]; rcases abs_cases x with ⟨_, e⟩ | ⟨_, e⟩ <;> omega
      · intro i hi he; exact hna ⟨i, hi, by rw [he]; exact hx⟩
    rcases hf with hf | hf
    · exact hf (off v (by rcases abs_cases v with ⟨_, e⟩ | ⟨_, e⟩ <;> omega))
    · exact hf (off (-v) (by rw [abs_neg']; rcases abs_cases v with ⟨_, e⟩ | ⟨_, e⟩ <;> omega))
  · rintro ⟨i, hi, he⟩
    have hnz : flag S (trailAt S i) ≠ 0 := by
      by_cases hr : RootLevel S i
      · rw [h.flag_root i hi hr]; decide
      · rw [h.flag_level i hi hr]; decide
    rcases abs_cases (trailAt S i) with ⟨_, e⟩ | ⟨_, e⟩
    · right; rw [show -v = trailAt S i by omega]; exact hnz
    · left; rw [show v = trailAt S i by omega]; exact hnz

end MicrosatLean.Faithful.Verification
