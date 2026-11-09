import MicrosatLean.Faithful.Verification.Update

/-!
# Visiting a watched clause (C:139–142)

`propagate` reaches a clause from a link `x` on `lit`'s watch list. `*watch + 1` is the
record's link 1 or its first literal; `clause[-2] == 0` tells them apart, since the cell
before a record's link 0 is the previous record's terminator (or the 0 of C:204) while a
link cell never holds 0. `Visit` packages what is known at that point.
-/

namespace MicrosatLean.Faithful.Verification

/-- In a tiling, the cell before each record's link 0 holds 0, and so does the last cell. -/
theorem Tiling.zero_before {S : solver} {a b : Ptr} {rs : List Record} (h : Tiling S a b rs)
    (ha : S.ld (a - 1) = 0) : (∀ r ∈ rs, S.ld (r.1 - 3) = 0) ∧ S.ld (b - 1) = 0 := by
  induction h with
  | nil => exact ⟨fun r hr => by simp at hr, ha⟩
  | @cons p q lits rest hc ht ih =>
    have hend : S.ld (p + 3 + lits.length - 1) = 0 := by
      rw [show p + 3 + (lits.length : CInt) - 1 = p + 2 + lits.length by omega]; exact hc.2
    obtain ⟨h1, h2⟩ := ih hend
    refine ⟨fun r hr => ?_, h2⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only; rw [show p + 2 - 3 = p - 1 by omega]; exact ha
    · exact h1 r hr

/-- The cell before each record's link 0 holds 0. -/
theorem Database.zero_before {input : Input} {S : solver} {db : Records} (h : Database input S db)
    (hl : Layout S) {r : Record} (hr : r ∈ db.all) : S.ld (r.1 - 3) = 0 := by
  have z1 := h.inputs_tile.zero_before hl.sentinel
  have z2 := h.lemmas_tile.zero_before (by
    unfold lemmasStart; split
    · exact hl.sentinel
    · rename_i hne
      have := h.inputs_tile.zero_before hl.sentinel
      unfold lemmasStart at this; rw [if_neg hne] at this; exact this.2)
  rcases List.mem_append.mp hr with hr | hr
  · exact z1.1 r hr
  · exact z2.1 r hr

/-- A link on a watch list holds the next link or `END`, never 0. -/
theorem ListFrom.next_mem {S : solver} {head : Ptr} {links : List Ptr} (h : ListFrom S head links)
    {link : Ptr} (hm : link ∈ links) : S.ld link ∈ links ∨ S.ld link = END := by
  induction links generalizing head with
  | nil => simp at hm
  | cons x xs ih =>
    obtain ⟨h1, h2⟩ := h
    rcases List.mem_cons.mp hm with rfl | hm
    · cases xs with
      | nil => exact Or.inr h2
      | cons y ys => exact Or.inl (by simp [h2.1])
    · rcases ih h2 hm with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · exact Or.inr h'

/-- Every link cell of the database holds a nonzero value. -/
theorem Core.link_ne_zero {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) {L link : CInt} (hw : Watches db.all L link db.flip) : S.ld link ≠ 0 := by
  have hL : InRange S.nVars L := by
    obtain ⟨r, hr, h2, hx⟩ := hw
    rcases hx with ⟨_, hx⟩ | ⟨_, hx⟩ <;> exact h.record_lit hr (List.mem_of_getElem? hx)
  obtain ⟨links, hlf, -, hmem⟩ := h.watches L hL
  rcases hlf.next_mem ((hmem link).mpr hw) with h' | h'
  · have := Watches.link_ge h.database ((hmem _).mp h'); simp only [clausesAt] at this
    have := h.layout.nVars_pos; omega
  · rw [h']; decide

/-- Everything known when `propagate` visits the link `S.ld w` of `lit`'s list (C:139–142):
the invariant of the watch loop, and the record `r` the link belongs to, whose literals
start at the pointer C computes. -/
structure Visit (input : Input) (S0 : solver) (vs0 : List CInt) (P : Nat) (lit : CInt) (S : solver)
    (f w : CInt) (db : Records) (vs : List CInt) (visited rest : List Ptr) (r : Record) : Prop where
  core : Core input S db vs
  hpp : processedPos S = P + 1
  hP : P < trailLen S
  hlit : trailAt S P = lit
  path : Path S (S.first + lit) visited w
  list : ListFrom S w (S.ld w :: rest)
  nodup : ((S.first + lit) :: (visited ++ S.ld w :: rest)).Nodup
  mem : ∀ link, link ∈ visited ++ S.ld w :: rest ↔ Watches db.all lit link db.flip
  watched : WatchedExcept S db P (S.ld w :: rest)
  pmode : PMode S f P
  rel : Rel S0 vs0 S vs
  hr : r ∈ db.all
  h2 : 2 ≤ r.2.length
  hx : (S.ld w = r.1 - 2 ∧ r.2[if db.flip r.1 then 1 else 0]? = some lit) ∨
    (S.ld w = r.1 - 1 ∧ r.2[if db.flip r.1 then 0 else 1]? = some lit)
  hc : (if S.ld (S.ld w + 1 - 2) = 0 then S.ld w + 1 + 1 else S.ld w + 1) = r.1

/-- Following a link that is not `END` reaches a record (C:139–141). -/
theorem WInv.visit {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt} {S : solver}
    {f w : CInt} (h : WInv input S0 vs0 P lit S f w) (hne : S.ld w ≠ END) :
    ∃ db vs visited rest r, Visit input S0 vs0 P lit S f w db vs visited rest r := by
  obtain ⟨db, vs, visited, rest0, core, hpp, hP, hlit, hpath, hlf, hnd, hmem, hwe, pmode, rel⟩ := h
  cases rest0 with
  | nil => exact absurd hlf hne
  | cons x rest =>
    have hx : S.ld w = x := hlf.1
    subst hx
    obtain ⟨r, hr, h2, hw⟩ := (hmem (S.ld w)).mp (by simp)
    have hl := core.layout
    refine ⟨db, vs, visited, rest, r, core, hpp, hP, hlit, hpath, hlf, hnd, hmem, hwe, pmode, rel, hr, h2, hw, ?_⟩
    rcases hw with ⟨he, _⟩ | ⟨he, hw1⟩
    · rw [if_pos (by rw [he, show r.1 - 2 + 1 - 2 = r.1 - 3 by omega]; exact core.database.zero_before hl hr)]
      omega
    · have hlink0 : S.ld (r.1 - 2) ≠ 0 := by
        have hw0 : Watches db.all r.2[if db.flip r.1 then 1 else 0]! (r.1 - 2) db.flip := by
          refine ⟨r, hr, h2, Or.inl ⟨rfl, ?_⟩⟩
          rw [List.getElem?_eq_getElem (by split <;> omega), getElem!_pos r.2 _ (by split <;> omega)]
        exact core.link_ne_zero hw0
      rw [if_neg (by rw [he, show r.1 - 1 + 1 - 2 = r.1 - 2 by omega]; exact hlink0)]
      omega

/-- A clause of the database whose literals are all false at the root makes the input
unsatisfiable (C:154, `forced` set). -/
theorem Core.unsat_of_root_conflict {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) {r : Record} (hr : r ∈ db.all)
    (hall : ∀ l ∈ r.2, ∃ i < trailLen S, RootLevel S i ∧ trailAt S i = l) : input.Unsat := by
  intro a hsat
  have hent : input.Entails r.2 := by
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i, hi, hp⟩ := h.database.input_perm hr
      exact fun a ha => (clauseSat_perm hp).mpr (ha _ (Array.getElem_mem hi))
    · exact h.database.lemma_entailed r hr
  obtain ⟨l, hl, ht⟩ := hent a hsat
  obtain ⟨i, hi, hroot, he⟩ := hall l hl
  obtain ⟨l', hl', ht'⟩ := h.root i hi hroot a hsat
  simp only [List.mem_singleton] at hl'
  subst hl'
  rw [he] at ht'
  have hnz := (inRange_iff.mp (h.trail.lit i hi)).1
  rw [he] at hnz
  unfold LitTrue at ht ht'
  rw [Int.natAbs_neg, ht] at ht'
  simp at ht'; omega

/-- A record has at most `n` literals: V3 for input clauses, distinct variables for lemmas. -/
theorem Core.record_length_le {input : Input} {S : solver} {db : Records} {vs : List CInt}
    (h : Core input S db vs) {r : Record} (hr : r ∈ db.all) : (r.2.length : CInt) ≤ S.nVars := by
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i, hi, hp⟩ := h.database.input_perm hr
    have hs : (input.clauses[i].size : CInt) ≤ input.nVars := h.valid.clause_size_le _ (Array.getElem_mem hi)
    have hl : r.2.length = input.clauses[i].size := by rw [hp.length_eq, Array.length_toList]
    have hn := h.nVars
    rw [hl]; omega
  · have := clause_length_le (h.database.lemma_shape r hr).2.1 (h.database.lemma_shape r hr).2.2
    have := h.layout.nVars_pos
    omega

/-- The literal scan starts (C:143) at literal 2 of the clause, whose cells from 2 on are
the record's. -/
theorem Visit.scan_start {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt}
    {S : solver} {f w : CInt} {db : Records} {vs : List CInt} {visited rest : List Ptr} {r : Record}
    (hv : Visit input S0 vs0 P lit S f w db vs visited rest r) {c N : CInt} (hc : c = r.1)
    (hN : N = S.nVars) {Ss : solver} (hSs : ∀ q, c + 2 ≤ q → Ss.ld q = S.ld q) :
    ScanInv Ss c w lit N Ss 1 2 := by
  have hrec : ClauseAt S r.1 r.2 := by
    rcases List.mem_append.mp hv.hr with h' | h'
    · exact hv.core.database.inputs_tile.clauseAt h'
    · exact hv.core.database.lemmas_tile.clauseAt h'
  have hlen := hv.core.record_length_le hv.hr
  have h2 := hv.h2
  subst hc
  refine ⟨r.2.length, by omega, by omega, ?_, fun t h1 h3 => ?_, Or.inl ⟨by decide, rfl, Int.le_refl _, by omega,
    fun t h1 h3 => by omega⟩⟩
  · rw [hSs _ (by omega)]; exact hrec.2
  · rw [hSs _ (by omega)]
    have ht : (t.toNat) < r.2.length := by omega
    have := hrec.1 _ ht
    rw [show r.1 + ((t.toNat : Nat) : CInt) = r.1 + t by omega] at this
    rw [this]
    exact (inRange_iff.mp (hv.core.record_lit hv.hr (List.getElem_mem ht))).1

end MicrosatLean.Faithful.Verification
