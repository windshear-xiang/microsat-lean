import MicrosatLean.Faithful.Verification.Clauses

/-!
# Which cells each part of the invariant reads

The arrays sit at fixed offsets (`Layout.lean`), so every C function writes into a
few known regions. These frame lemmas say that the layout, the clause database, the
watch lists and the decision order survive any change outside the cells they read.
-/

namespace MicrosatLean.Faithful.Verification

/-- The pointer fields as numbers, for `omega`. -/
theorem Layout.num {S : solver} (h : Layout S) :
    S.model = 0 ∧ S.next = S.nVars + 1 ∧ S.prev = 2 * S.nVars + 2 ∧ S.buffer = 3 * S.nVars + 3 ∧
    S.reason = 4 * S.nVars + 3 ∧ S.falseStack = 5 * S.nVars + 4 ∧ S.false = 7 * S.nVars + 5 ∧
    S.first = 9 * S.nVars + 6 := by
  refine ⟨by rw [h.model]; rfl, by rw [h.next]; rfl, by rw [h.prev]; simp only [prevAt]; omega,
    by rw [h.buffer]; simp only [bufferAt]; omega, by rw [h.reason]; rfl, by rw [h.falseStack]; rfl,
    by rw [h.false]; rfl, by rw [h.first]; rfl⟩

/-- `T` keeps `S`'s array pointers and `nVars`. Every C function after `initCDCL` does. -/
structure SameShape (S T : solver) : Prop where
  nVars : T.nVars = S.nVars
  model : T.model = S.model
  next : T.next = S.next
  prev : T.prev = S.prev
  buffer : T.buffer = S.buffer
  reason : T.reason = S.reason
  falseStack : T.falseStack = S.falseStack
  «false» : T.false = S.false
  first : T.first = S.first

theorem SameShape.refl (S : solver) : SameShape S S := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem SameShape.trans {S T U : solver} (h1 : SameShape S T) (h2 : SameShape T U) : SameShape S U :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2, h2.3.trans h1.3, h2.4.trans h1.4, h2.5.trans h1.5,
    h2.6.trans h1.6, h2.7.trans h1.7, h2.8.trans h1.8, h2.9.trans h1.9⟩

/-- A write keeps the shape. -/
theorem SameShape.st (S : solver) (p v : CInt) : SameShape S (S.st p v) := by
  constructor <;> simp

/-- The layout survives any change that keeps the shape and the cell before the records. -/
theorem Layout.frame {S T : solver} (h : Layout S) (hs : SameShape S T)
    (sent : T.ld (clausesAt S.nVars - 1) = S.ld (clausesAt S.nVars - 1)) : Layout T := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [hs.nVars, hs.model, hs.next, hs.prev,
    hs.buffer, hs.reason, hs.falseStack, hs.false, hs.first, sent]
  · exact h.1
  · exact h.2
  · exact h.3
  · exact h.4
  · exact h.5
  · exact h.6
  · exact h.7
  · exact h.8
  · exact h.9
  · exact h.10

/-- Records lie at or above `clausesAt`, two cells past their link cells. -/
theorem Database.record_ge {input : Input} {S : solver} {db : Records} (h : Database input S db)
    {r : Record} (hr : r ∈ db.all) : clausesAt S.nVars + 2 ≤ r.1 ∧ r.1 + r.2.length < S.mem_used := by
  have b1 := h.inputs_tile.bounds
  have b2 := h.lemmas_tile.bounds
  rcases List.mem_append.mp hr with hr | hr
  · have := b1.2 r hr; omega
  · have := b2.2 r hr; omega

/-- The database survives any change that keeps the shape, the counters, and every cell
from `clausesAt` on. -/
theorem Database.frame {input : Input} {S T : solver} {db : Records} (h : Database input S db)
    (hs : SameShape S T) (hu : T.mem_used = S.mem_used) (hf : T.mem_fixed = S.mem_fixed)
    (hn : T.nLemmas = S.nLemmas) (cells : ∀ q, clausesAt S.nVars ≤ q → T.ld q = S.ld q) :
    Database input T db := by
  have hst : lemmasStart T db = lemmasStart S db := by simp only [lemmasStart, hs.nVars, hf]
  have same : ∀ r ∈ db.all, ∀ q, RecordCell r q → T.ld q = S.ld q := fun r hr q hq => by
    have := h.record_ge hr; simp only [RecordCell] at hq; exact cells q (by omega)
  refine ⟨?_, ?_, h.inputs_length, h.inputs_perm, h.inputs_nonempty, h.no_lemmas, by rw [hn]; exact h.nLemmas,
    ?_, h.lemma_entailed, h.lemma_distinct⟩
  · rw [hst, hs.nVars]
    exact h.inputs_tile.frame fun r hr => same r (List.mem_append_left _ hr)
  · rw [hst, hu]
    exact h.lemmas_tile.frame fun r hr => same r (List.mem_append_right _ hr)
  · rw [hs.nVars]; exact h.lemma_shape

/-- Link cells of watched records lie at or above `clausesAt`. -/
theorem Watches.link_ge {input : Input} {S : solver} {db : Records} (h : Database input S db)
    {lit link : CInt} {f : Ptr → Bool} (hw : Watches db.all lit link f) : clausesAt S.nVars ≤ link := by
  obtain ⟨r, hr, -, hw⟩ := hw
  have := h.record_ge hr
  rcases hw with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega

/-- The watch lists survive any change that keeps the shape and every cell from the
`first` array on. -/
theorem WatchLists.frame {input : Input} {S T : solver} {db : Records} (h : WatchLists S db)
    (hl : Layout S) (hd : Database input S db) (hs : SameShape S T)
    (cells : ∀ q, 8 * S.nVars + 6 ≤ q → T.ld q = S.ld q) : WatchLists T db := by
  intro lit hlit
  rw [hs.nVars] at hlit
  obtain ⟨links, hlinks, hnd, hm⟩ := h lit hlit
  refine ⟨links, ?_, hnd, hm⟩
  rw [hs.first]
  have hn := hl.num
  have hr := inRange_iff.mp hlit
  refine hlinks.frame fun q hq => cells q ?_
  rcases hq with rfl | hq
  · omega
  · have := Watches.link_ge hd ((hm q).mp hq); simp only [clausesAt] at this; omega

/-- The decision order survives any change that keeps the shape, `head`, and the
`next` and `prev` arrays. -/
theorem OrderList.frame {S T : solver} {vs : List CInt} (h : OrderList S vs) (hl : Layout S)
    (hs : SameShape S T) (hh : T.head = S.head)
    (cells : ∀ q, S.nVars + 1 ≤ q → q ≤ 3 * S.nVars + 2 → T.ld q = S.ld q) : OrderList T vs := by
  have hn := hl.num
  have hn1 := hl.nVars_pos
  have hv : ∀ w ∈ vs, 1 ≤ w ∧ w ≤ S.nVars := fun w hw => h.mem_iff.mp hw
  refine ⟨?_, by rw [hs.nVars]; exact h.perm, ?_, ?_⟩
  · rw [hh]
    exact h.chain.congr fun w hw => by
      have := hv w hw; rw [hs.prev]; exact cells _ (by omega) (by omega)
  · intro i hi
    have := hv _ (List.getElem_mem hi)
    rw [hs.next, cells _ (by omega) (by omega)]
    exact h.next_back i hi
  · rw [hs.next, cells _ (by omega) (by omega)]
    exact h.next_zero

end MicrosatLean.Faithful.Verification
