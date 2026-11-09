import MicrosatLean.Faithful.Verification.Layout
import MicrosatLean.Faithful.Verification.Spec

/-!
# The clause database and its watch lists

Each clause is a record `[link0, link1, lit0, …, lit(k-1), 0]` in `DB` (C:59–66).
A `Record` is the pointer to `lit0` (C's `clause`) with its literals. Input
records fill `[clausesAt n, mem_fixed)` and learned ones `[mem_fixed, mem_used)`.
Watch lists are linked through the link cells: `first[lit]` and each link cell
hold the next link cell, or `END` (C:49–50).
-/

namespace MicrosatLean.Faithful.Verification

/-- A clause in `DB`: C's `clause` pointer (its first literal) and its literals. -/
abbrev Record := Ptr × List CInt

/-- A literal of a problem with `n` variables. -/
def InRange (n lit : CInt) : Prop := lit ≠ 0 ∧ abs lit ≤ n

/-- `abs` (C's `abs` on `int`) by cases, for `omega`. -/
theorem abs_cases (x : CInt) : (x < 0 ∧ abs x = -x) ∨ (0 ≤ x ∧ abs x = x) := by
  unfold abs; split <;> omega

/-- `abs` is `Int.natAbs`, as an integer. -/
theorem abs_eq_natAbs (x : CInt) : abs x = (x.natAbs : CInt) := by
  rcases abs_cases x with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> omega

/-- A literal and its negation have the same variable. -/
theorem abs_neg' (x : CInt) : abs (-x) = abs x := by
  rcases abs_cases x with ⟨_, e⟩ | ⟨_, e⟩ <;> rcases abs_cases (-x) with ⟨_, e'⟩ | ⟨_, e'⟩ <;> omega

/-- A literal of the problem, without `abs` (for `omega`). -/
theorem inRange_iff {n lit : CInt} : InRange n lit ↔ lit ≠ 0 ∧ -n ≤ lit ∧ lit ≤ n := by
  unfold InRange; rcases abs_cases lit with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h2] <;> omega

/-- `DB` holds `lits` from `c` on, followed by the terminating 0. -/
def ClauseAt (S : solver) (c : Ptr) (lits : List CInt) : Prop :=
  (∀ i (h : i < lits.length), S.ld (c + i) = lits[i]) ∧ S.ld (c + lits.length) = 0

/-- Records tile `[start, stop)` in order; `rs` lists them. -/
inductive Tiling (S : solver) : Ptr → Ptr → List Record → Prop
  | nil (p : Ptr) : Tiling S p p []
  | cons {p q : Ptr} {lits : List CInt} {rest : List Record} :
      ClauseAt S (p + 2) lits → Tiling S (p + 3 + lits.length) q rest →
      Tiling S p q ((p + 2, lits) :: rest)

/-- Following `head` and then each link cell visits `links` and ends at `END`. -/
def ListFrom (S : solver) (head : Ptr) : List Ptr → Prop
  | [] => S.ld head = END
  | link :: rest => S.ld head = link ∧ ListFrom S link rest

/-- `link` is a link cell watching `lit`: one of the two link cells of a record whose first
or second literal is `lit`. `addClause` links them straight, link 0 to the first literal
and link 1 to the second (C:62–63); `propagate` moves the literal it visits to position 1
without moving links (C:141–151), so a record's links may be crossed: `flip`. -/
def Watches (rs : List Record) (lit : CInt) (link : Ptr) (flip : Ptr → Bool := fun _ => false) : Prop :=
  ∃ r ∈ rs, 2 ≤ r.2.length ∧
    ((link = r.1 - 2 ∧ r.2[if flip r.1 then 1 else 0]? = some lit) ∨
     (link = r.1 - 1 ∧ r.2[if flip r.1 then 0 else 1]? = some lit))

/-- The two kinds of records, in `DB` order, and which records have crossed links. -/
structure Records where
  inputs : List Record
  lemmas : List Record
  flip : Ptr → Bool := fun _ => false

/-- All records, input clauses first. -/
def Records.all (db : Records) : List Record := db.inputs ++ db.lemmas

/-- Where the learned records start: `mem_fixed` once an input clause was added
(C:65). With no input clause C leaves `mem_fixed` unset, and there are no lemmas. -/
def lemmasStart (S : solver) (db : Records) : Ptr :=
  if db.inputs = [] then clausesAt S.nVars else S.mem_fixed

/-- The clause database is laid out as C lays it out, holds the input clauses (up
to the literal order, which `propagate` changes), and holds entailed, pairwise
distinct lemmas. Used by every proof that reads or writes clauses. -/
structure Database (input : Input) (S : solver) (db : Records) : Prop where
  inputs_tile : Tiling S (clausesAt S.nVars) (lemmasStart S db) db.inputs
  lemmas_tile : Tiling S (lemmasStart S db) S.mem_used db.lemmas
  /-- The input records are the input clauses in order, with permuted literals. -/
  inputs_length : db.inputs.length = input.clauses.size
  inputs_perm : ∀ i (h : i < db.inputs.length) (h' : i < input.clauses.size),
    db.inputs[i].2.Perm input.clauses[i].toList
  /-- No input record is empty (`parse` stops at an empty clause, C:236). -/
  inputs_nonempty : ∀ r ∈ db.inputs, r.2 ≠ []
  no_lemmas : db.inputs = [] → db.lemmas = []
  nLemmas : S.nLemmas = db.lemmas.length
  /-- Every lemma is a nonempty clause over distinct variables of the problem. -/
  lemma_shape : ∀ r ∈ db.lemmas, r.2 ≠ [] ∧ (r.2.map Int.natAbs).Nodup ∧ ∀ l ∈ r.2, InRange S.nVars l
  /-- Every lemma follows from the input (soundness of learning). -/
  lemma_entailed : ∀ r ∈ db.lemmas, input.Entails r.2
  /-- No lemma is a reordering of another (each conflict learns a new clause). -/
  lemma_distinct : db.lemmas.Pairwise (fun r s => ¬ r.2.Perm s.2)

/-- Each literal's watch list is exactly the set of link cells watching it, with no
repetition, and ends at `END`. Link cells of unit records are on no list. -/
def WatchLists (S : solver) (db : Records) : Prop :=
  ∀ lit, InRange S.nVars lit →
    ∃ links : List Ptr, ListFrom S (S.first + lit) links ∧ links.Nodup ∧
      ∀ link, link ∈ links ↔ Watches db.all lit link db.flip

end MicrosatLean.Faithful.Verification
