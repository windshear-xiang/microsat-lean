import MicrosatLean.Verification.Implementation.Bridge.ToNativeBase
import MicrosatLean.Verification.Implementation.Native.Propagation.DatabaseIdentity
import MicrosatLean.Verification.Implementation.Native.Propagation.WatchIdentity

namespace MicrosatLean.Verification.Implementation.Bridge

/-!
The packed solver determines its logical view. This lets independent concrete
operation proofs share a logical state rather than silently choosing different
clause or reason witnesses for the same arrays.
-/

theorem rep_frame_solver {before after : CDCL.Machine} (same : before.solver = after.solver)
    {a : LogicalState} {w : RepresentationWitness} (represented : Rep before a w) : Rep after a w := by
  cases before
  cases after
  cases same
  cases represented
  constructor <;> assumption

theorem rep_entries_unique {m : CDCL.Machine} {a b : LogicalState}
    {w v : RepresentationWitness} (left : Rep m a w) (right : Rep m b v) :
    w.original = v.original ∧ w.learned = v.learned := by
  exact (database_toNative left).unique (database_toNative right)

private theorem packed_of_mem {m : CDCL.Machine} {a : LogicalState}
    {w : RepresentationWitness} (represented : Rep m a w)
    {entry : StoredClause} (member : entry ∈ w.entries) :
    Native.Representation.PackedClause m.solver entry.id entry.lits := by
  exact represented.layout.packed member

theorem rep_reason_unique {m : CDCL.Machine} {a b : LogicalState}
    {w v : RepresentationWitness} (left : Rep m a w) (right : Rep m b v)
    {i : Nat} (active : i < m.solver.assigned) : a.trail[i]!.reason = b.trail[i]!.reason := by
  have leftReason := left.reasons i active
  have rightReason := right.reasons i active
  cases first : a.trail[i]!.reason with
  | none =>
    cases second : b.trail[i]!.reason with
    | none => rfl
    | some clause =>
      simp only [first] at leftReason
      simp only [second] at rightReason
      obtain ⟨entry, member, id, _⟩ := rightReason
      have lower := (packed_of_mem right member).startLower
      omega
  | some clause =>
    cases second : b.trail[i]!.reason with
    | none =>
      simp only [first] at leftReason
      simp only [second] at rightReason
      obtain ⟨entry, member, id, _⟩ := leftReason
      have lower := (packed_of_mem left member).startLower
      omega
    | some other =>
      simp only [first] at leftReason
      simp only [second] at rightReason
      obtain ⟨entry, member, id, view⟩ := leftReason
      obtain ⟨next, contained, nextId, nextView⟩ := rightReason
      have sameId : entry.id = next.id := id.trans nextId.symm
      have nextPacked : Native.Representation.PackedClause m.solver entry.id next.lits :=
        sameId.symm ▸ packed_of_mem right contained
      have sameLiterals := (packed_of_mem left member).unique nextPacked
      have sameView : entry.view = next.view := by
        simp only [Native.Representation.StoredClause.view, sameLiterals]
      exact congrArg some (view.symm.trans (sameView.trans nextView))

theorem rep_trail_unique {m : CDCL.Machine} {a b : LogicalState}
    {w v : RepresentationWitness} (left : Rep m a w) (right : Rep m b v) :
    a.trail = b.trail := by
  apply List.ext_getElem (left.trailLength.trans right.trailLength.symm)
  intro i leftBound rightBound
  have active : i < m.solver.assigned := by simpa only [left.trailLength] using leftBound
  have literal := (left.trail i active).trans (right.trail i active).symm
  have reason := rep_reason_unique left right active
  have entry : a.trail[i]! = b.trail[i]! := by
    cases first : a.trail[i]!
    cases second : b.trail[i]!
    rw [first, second] at literal reason
    cases literal
    cases reason
    rfl
  simpa only [getElem!_pos a.trail i leftBound, getElem!_pos b.trail i rightBound] using entry

/-- Present solver data uniquely determine the entire logical state. -/
theorem rep_unique {m : CDCL.Machine} {a b : LogicalState}
    {w v : RepresentationWitness} (left : Rep m a w) (right : Rep m b v) : a = b := by
  have entries := rep_entries_unique left right
  have variables := left.variables.trans right.variables.symm
  have original := left.original.trans ((congrArg (List.map Native.Representation.StoredClause.view) entries.1).trans right.original.symm)
  have learned := left.learned.trans ((congrArg (List.map Native.Representation.StoredClause.view) entries.2).trans right.learned.symm)
  have trail := rep_trail_unique left right
  have roots := left.rootSize.trans right.rootSize.symm
  cases a
  cases b
  simp_all

theorem rep_unique_of_solver_eq {before after : CDCL.Machine}
    {a b : LogicalState} {w v : RepresentationWitness}
    (same : before.solver = after.solver) (left : Rep before a w) (right : Rep after b v) : a = b :=
  rep_unique (rep_frame_solver same left) right

private theorem watch_links {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) (lit : Lit) :
    Native.Propagation.WatchLinks m.solver lit (w.heads lit) :=
  represented.watches.links lit

private theorem watch_nonzero {m : CDCL.Machine} {a : LogicalState} {w : RepresentationWitness}
    (represented : Rep m a w) (lit : Lit) : ∀ ref ∈ w.heads lit, ref ≠ 0 := by
  intro ref member zero
  obtain ⟨entry, stored, id, _⟩ := represented.watches.references lit ref member
  have lower := (Native.Representation.DatabaseFrom.packed represented.layout stored).startLower
  rw [zero] at id
  simp only [CDCL.watchClause, Nat.zero_div] at id
  omega

theorem rep_heads_unique {m : CDCL.Machine} {a b : LogicalState}
    {w v : RepresentationWitness} (left : Rep m a w) (right : Rep m b v) : w.heads = v.heads := by
  funext lit
  exact (watch_links left lit).chain.unique (watch_links right lit).chain
    (watch_nonzero left lit) (watch_nonzero right lit)
    ((left.watches.links lit).2.1.symm.trans (right.watches.links lit).2.1)

private def PointerChain (next : Nat → Nat) : List Nat → Prop
  | [] => True
  | ref :: rest => next ref = rest.headD 0 ∧ PointerChain next rest

private theorem chain_of_links (next : Nat → Nat) (refs : List Nat)
    (links : ∀ i, i < refs.length → next (refs.getD i 0) = refs.getD (i + 1) 0) :
    PointerChain next refs := by
  induction refs with
  | nil => trivial
  | cons ref rest ih =>
    refine ⟨?_, ih ?_⟩
    · simpa only [List.getD_cons_zero, List.getD_cons_succ, List.headD_eq_getD] using links 0 (by simp)
    · intro i bound
      simpa only [List.getD_cons_succ] using links (i + 1) (by simp; omega)

private theorem pointerChain_unique {next : Nat → Nat} {left right : List Nat}
    (first : PointerChain next left) (second : PointerChain next right)
    (leftNonzero : ∀ ref ∈ left, ref ≠ 0) (rightNonzero : ∀ ref ∈ right, ref ≠ 0)
    (head : left.headD 0 = right.headD 0) : left = right := by
  induction left generalizing right with
  | nil =>
    cases right with
    | nil => rfl
    | cons ref rest =>
      exact False.elim (rightNonzero ref (by simp) (by simpa using head.symm))
  | cons ref rest ih =>
    cases right with
    | nil => exact False.elim (leftNonzero ref (by simp) (by simpa using head))
    | cons other tail =>
      have equal : ref = other := by simpa using head
      subst other
      exact congrArg (ref :: ·) (ih first.2 second.2
        (fun old member => leftNonzero old (by simp [member]))
        (fun old member => rightNonzero old (by simp [member]))
        (first.1.symm.trans second.1))

theorem rep_order_unique {m : CDCL.Machine} {a b : LogicalState}
    {w v : RepresentationWitness} (left : Rep m a w) (right : Rep m b v) : w.order = v.order := by
  apply pointerChain_unique
    (chain_of_links (fun ref => m.solver.previous[ref]!) w.order (fun i bound => (left.order.2.2.2 i bound).1))
    (chain_of_links (fun ref => m.solver.previous[ref]!) v.order (fun i bound => (right.order.2.2.2 i bound).1))
  · intro ref member
    have positive := ((left.order.2.1 ref).mp member).1
    omega
  · intro ref member
    have positive := ((right.order.2.1 ref).mp member).1
    omega
  · exact left.order.2.2.1.symm.trans right.order.2.2.1

theorem rep_witness_unique {m : CDCL.Machine} {a b : LogicalState}
    {w v : RepresentationWitness} (left : Rep m a w) (right : Rep m b v) : w = v := by
  have entries := rep_entries_unique left right
  have heads := rep_heads_unique left right
  have order := rep_order_unique left right
  cases w
  cases v
  simp_all

end MicrosatLean.Verification.Implementation.Bridge
