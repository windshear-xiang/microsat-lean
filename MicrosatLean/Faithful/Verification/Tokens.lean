import MicrosatLean.Faithful.Valid

/-!
# The literal tokens `parse` reads

`Input.tokens` lists each clause followed by `0`. These lemmas let `parse`'s proof
follow the token stream as "the tokens not read yet".
-/

namespace MicrosatLean.Faithful.Verification

/-- The tokens of a list of clauses: each clause, then `0`. -/
def tokList : List (Array CInt) → List CInt
  | [] => []
  | c :: cs => c.toList ++ 0 :: tokList cs

/-- `Input.tokens` as a list. -/
theorem tokens_toList (input : Input) : input.tokens.toList = tokList input.clauses.toList := by
  unfold Input.tokens
  rw [← Array.foldl_toList]
  suffices key : ∀ (acc : Array CInt) (l : List (Array CInt)),
      (l.foldl (fun acc clause => (acc ++ clause).push 0) acc).toList = acc.toList ++ tokList l by
    simpa using key #[] input.clauses.toList
  intro acc l
  induction l generalizing acc with
  | nil => simp [tokList]
  | cons c cs ih => rw [List.foldl_cons, ih]; simp [tokList]

/-- Token `next` is the first token not read yet. -/
theorem getElem?_eq_head?_drop (a : Array CInt) (next : Nat) :
    a[next]? = (a.toList.drop next).head? := by
  simp [List.head?_drop]

/-- Reading one more token drops it from the tokens not read yet. -/
theorem drop_succ_eq_tail (l : List CInt) (next : Nat) : l.drop (next + 1) = (l.drop next).tail := by
  simp [List.tail_drop]

end MicrosatLean.Faithful.Verification
