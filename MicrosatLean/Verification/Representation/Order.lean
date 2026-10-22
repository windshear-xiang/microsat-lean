import MicrosatLean.Verification.Representation.State

namespace MicrosatLean.Verification.Representation.Order

variable {s : CDCL.State}

/-- Finite index and list facts for the move-to-front decision order. -/
def moveIndex (selected i : Nat) : Nat :=
  if i = 0 then selected else if i ≤ selected then i - 1 else i

def movedOrder (order : List Nat) (selected : Nat) : List Nat :=
  order.getD selected 0 :: order.eraseIdx selected

theorem movedOrder_getD (order : List Nat) (selected i : Nat) :
    (movedOrder order selected).getD i 0 = order.getD (moveIndex selected i) 0 := by
  cases i with
  | zero => simp [movedOrder, moveIndex]
  | succ i =>
    simp only [movedOrder, List.getD_eq_getElem?_getD, moveIndex, Nat.succ_ne_zero, ite_false]
    rw [List.getElem?_cons_succ, List.getElem?_eraseIdx]
    by_cases before : i < selected
    · simp [before, show i + 1 ≤ selected by omega]
    · simp [before, show ¬i + 1 ≤ selected by omega]

theorem moveIndex_bound {selected i length : Nat} (chosen : selected < length)
    (bound : i < length) : moveIndex selected i < length := by
  unfold moveIndex
  split
  · exact chosen
  · split <;> omega

theorem movedOrder_perm {order : List Nat} {selected : Nat} (distinct : order.Nodup)
    (bound : selected < order.length) : order.Perm (movedOrder order selected) := by
  have value : order.getD selected 0 = order[selected] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
  have erased : order.erase order[selected] = order.eraseIdx selected :=
    List.erase_eq_eraseIdx_of_idxOf (distinct.idxOf_getElem selected bound)
  simpa only [movedOrder, value, erased] using List.perm_cons_erase (List.getElem_mem bound)

theorem order_getD_bound {order : List Nat} (valid : MTFOrder s order) (i : Nat) :
    order.getD i 0 ≤ s.nVars := by
  by_cases bound : i < order.length
  · have value : order.getD i 0 = order[i] := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
    exact ((valid.2.1 _).mp (value ▸ List.getElem_mem bound)).2
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : order.length ≤ i)]

theorem order_getD_ne_zero {order : List Nat} (valid : MTFOrder s order)
    {i : Nat} (bound : i < order.length) : order.getD i 0 ≠ 0 := by
  have value : order.getD i 0 = order[i] := by
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem bound]
  have lower := ((valid.2.1 _).mp (value ▸ List.getElem_mem bound)).1
  omega

theorem order_getD_eq_iff {order : List Nat} (valid : MTFOrder s order)
    {i j : Nat} (left : i ≤ order.length) (right : j < order.length) :
    order.getD i 0 = order.getD j 0 ↔ i = j := by
  by_cases bound : i < order.length
  · exact valid.1.getD_inj bound right
  · have last : i = order.length := by omega
    have zero : order.getD i 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : order.length ≤ i)]
    rw [zero]
    constructor
    · intro equal
      exact False.elim (order_getD_ne_zero valid right equal.symm)
    · intro equal
      omega

theorem moveIndex_previous (selected i : Nat) (positive : 0 < selected) :
    moveIndex selected (i + 1) =
      if selected = moveIndex selected i then 0
      else if selected - 1 = moveIndex selected i then selected + 1
      else moveIndex selected i + 1 := by
  unfold moveIndex
  repeat first | split | omega

theorem moveIndex_next (selected i : Nat) (positive : 0 < selected) (nonhead : 0 < i) :
    moveIndex selected (i - 1) =
      if 0 = moveIndex selected i then selected
      else if selected + 1 = moveIndex selected i then selected - 1
      else moveIndex selected i - 1 := by
  unfold moveIndex
  repeat first | split | omega

end MicrosatLean.Verification.Representation.Order

namespace MicrosatLean.Verification.Representation

open CDCL

theorem MTFOrder.frame {before after : State} {order : List Nat} (valid : MTFOrder before order)
    (variables : after.nVars = before.nVars) (head : after.head = before.head)
    (previous : after.previous = before.previous) (next : after.next = before.next) :
    MTFOrder after order := by
  simpa only [MTFOrder, variables, head, previous, next] using valid

theorem MTFOrder.assign {s : State} {order : List Nat} (valid : MTFOrder s order)
    (id : Nat) (root : Bool) : MTFOrder (s.assign id root) order :=
  valid.frame rfl rfl rfl rfl

theorem MTFOrder.decide {s : State} {order : List Nat} (valid : MTFOrder s order)
    (var : Nat) : MTFOrder (s.decide var) order := valid.frame rfl rfl rfl rfl

theorem MTFOrder.addClause {s : State} {order : List Nat} (valid : MTFOrder s order)
    (lits : Array Lit) (original : Bool) : MTFOrder (s.addClause lits original).1 order := by
  by_cases watches : 1 < lits.size <;> cases original <;>
    simpa [MTFOrder, State.addClause, State.addWatch, watches] using valid

theorem MTFCoverage.assign {s : State} (valid : MTFCoverage s) (id : Nat) (root : Bool) :
    MTFCoverage (s.assign id root) := by
  obtain ⟨order, valid⟩ := valid
  exact ⟨order, valid.assign id root⟩

theorem MTFCoverage.decide {s : State} (valid : MTFCoverage s) (var : Nat) :
    MTFCoverage (s.decide var) := by
  obtain ⟨order, valid⟩ := valid
  exact ⟨order, valid.decide var⟩

theorem MTFCoverage.addClause {s : State} (valid : MTFCoverage s) (lits : Array Lit)
    (original : Bool) : MTFCoverage (s.addClause lits original).1 := by
  obtain ⟨order, valid⟩ := valid
  exact ⟨order, valid.addClause lits original⟩

end MicrosatLean.Verification.Representation
