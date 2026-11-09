import MicrosatLean.Faithful.Verification.PropagateInv

/-!
# Entering and leaving `propagate`'s loops

The outer loop starts from `solve`'s invariant (with the `forced` flag of C:134), each
watch loop starts at the head of the processed literal's list (C:136–138), a finished
watch list gives back the outer invariant, and the final `forced` update (C:157) gives
`Settled`.
-/

namespace MicrosatLean.Faithful.Verification

/-- `processed` points at trail entry `processedPos`. -/
theorem Trail.ld_processed {S : solver} (h : Trail S) : S.ld S.processed = trailAt S (processedPos S) := by
  have := h.forced_le; have := h.processed_le
  simp only [trailAt, processedPos]
  rw [show S.falseStack + ((S.processed - S.falseStack).toNat : CInt) = S.processed by omega]

/-- A watched literal of a record has one of the record's links on its list. -/
theorem watches_of_slot {rs : List Record} {f : Ptr → Bool} {r : Record} (hr : r ∈ rs)
    (h2 : 2 ≤ r.2.length) {w : Nat} (hw : w = 0 ∨ w = 1) {lit : CInt} (he : r.2[w]! = lit) :
    ∃ link, (link = r.1 - 2 ∨ link = r.1 - 1) ∧ Watches rs lit link f := by
  have hg : r.2[w]? = some lit := by
    rw [List.getElem?_eq_getElem (by omega), ← he, getElem!_pos r.2 w (by omega)]
  cases hf : f r.1 <;> rcases hw with rfl | rfl
  · exact ⟨r.1 - 2, Or.inl rfl, r, hr, h2, Or.inl ⟨rfl, by simp only [hf]; exact hg⟩⟩
  · exact ⟨r.1 - 1, Or.inr rfl, r, hr, h2, Or.inr ⟨rfl, by simp only [hf]; exact hg⟩⟩
  · exact ⟨r.1 - 1, Or.inr rfl, r, hr, h2, Or.inr ⟨rfl, by simp only [hf]; exact hg⟩⟩
  · exact ⟨r.1 - 2, Or.inl rfl, r, hr, h2, Or.inl ⟨rfl, by simp only [hf]; exact hg⟩⟩

/-- The outer loop starts from `solve`'s invariant, with `forced` set from the reason of
the first unprocessed literal (C:134). -/
theorem OutInv.init {input : Input} {S0 : solver} {db0 : Records} {vs0 : List CInt}
    (core0 : Core input S0 db0 vs0) (watched0 : WatchedTrue S0 db0) (mode0 : Mode S0) :
    OutInv input S0 vs0 S0 (S0.ld (S0.reason + abs (S0.ld S0.processed))) := by
  have ht := core0.trail
  have hf0 : S0.ld (S0.reason + abs (S0.ld S0.processed)) = reasonOf S0 (trailAt S0 (processedPos S0)) := by
    rw [ht.ld_processed]; rfl
  refine ⟨db0, vs0, core0, watched0, ?_, rfl, Or.inl ⟨rfl, rfl, Nat.le_refl _, fun _ _ => rfl⟩⟩
  rw [hf0]
  rcases mode0 with ⟨hp0, hroot⟩ | ⟨hp1, hdec, hbelow⟩
  · refine ⟨?_, fun k _ hk hd => hroot k hk k (Nat.le_refl _) hd⟩
    by_cases hz : reasonOf S0 (trailAt S0 (processedPos S0)) = 0
    · refine Or.inr ⟨hz, fun i hi _ => ?_, fun hlt => ?_⟩
      · exact absurd hz (hroot 0 (by omega) 0 (Nat.le_refl _) |> fun h => by rw [hp0]; exact h)
      · exact absurd hz (by rw [hp0]; exact hroot 0 (by omega) 0 (Nat.le_refl _))
    · exact Or.inl ⟨hz, hroot⟩
  · refine ⟨Or.inr ⟨hdec, hbelow, fun _ => ⟨processedPos S0, ?_, Nat.le_refl _, hdec⟩⟩,
      fun k h1 h2 => by omega⟩
    simp only [forcedPos, processedPos]; have := ht.processed_le; omega

/-- A watch loop starts at the head of the list of the literal at `processed` (C:136–138). -/
theorem WInv.init {input : Input} {S0 : solver} {vs0 : List CInt} {S : solver} {f : CInt}
    (h : OutInv input S0 vs0 S f) (hlt : S.processed < S.assigned) :
    WInv input S0 vs0 (processedPos S) (S.ld S.processed) { S with processed := S.processed + 1 } f
      (S.first + S.ld S.processed) := by
  obtain ⟨db, vs, core, watched, pmode, rel⟩ := h
  have ht := core.trail
  have hl := core.layout; have hn := hl.num
  have hpp : processedPos S < trailLen S := by simp only [processedPos, trailLen]; have := ht.forced_le; have := ht.processed_le; omega
  have hlit := ht.lit _ hpp
  rw [ht.ld_processed]
  generalize hL : trailAt S (processedPos S) = lit at hlit
  obtain ⟨links, hlf, hnd, hmem⟩ := core.watches lit hlit
  have hlr := inRange_iff.mp hlit
  have hge : ∀ q ∈ links, clausesAt S.nVars ≤ q := fun q hq => Watches.link_ge core.database ((hmem q).mp hq)
  refine ⟨db, vs, [], links, core.withProcessed _ (by have := ht.processed_le; omega) (by omega), ?_, ?_, ?_,
    rfl, hlf.frame fun _ _ => rfl, ?_, by simpa using hmem, ?_, ?_, ?_⟩
  · simp only [processedPos]; have := ht.forced_le; have := ht.processed_le; omega
  · exact hpp
  · exact hL
  · refine List.nodup_cons.mpr ⟨fun hm => ?_, by simpa using hnd⟩
    have := hge _ (by simpa using hm); simp only [clausesAt] at this; omega
  · intro r hr h2 w o hwo p hp hfa hex
    have hp' : processedPos ({ S with processed := S.processed + 1 } : solver) = processedPos S + 1 := by
      simp only [processedPos]; have := ht.forced_le; have := ht.processed_le; omega
    rw [hp'] at hp
    rcases Nat.lt_or_ge p (processedPos S) with hpl | hpl
    · exact watched r hr h2 w o hwo p hpl hfa
    · have hpe : p = processedPos S := by omega
      obtain ⟨n0, n1⟩ := hex hpe
      subst hpe
      have hw : w = 0 ∨ w = 1 := by rcases hwo with ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> simp
      obtain ⟨link, hlink, hwl⟩ := watches_of_slot (f := db.flip) hr h2 hw (lit := lit) (by rw [← hL]; exact hfa.2.symm)
      exact absurd ((hmem link).mpr hwl) (by rcases hlink with rfl | rfl <;> assumption)
  · exact pmode
  · exact rel

/-- A finished watch list (C:138, `END`) gives back the outer invariant, one literal on. -/
theorem WInv.exit {input : Input} {S0 : solver} {vs0 : List CInt} {P : Nat} {lit : CInt} {S : solver}
    {f w : CInt} (h : WInv input S0 vs0 P lit S f w) (hend : S.ld w = END) :
    OutInv input S0 vs0 S f ∧ processedPos S = P + 1 := by
  obtain ⟨db, vs, visited, rest, core, hpp, hP, hlit, hpath, hlf, hnd, hmem, hwe, pmode, rel⟩ := h
  have hrest : rest = [] := by
    cases rest with
    | nil => rfl
    | cons x xs =>
      exfalso
      have hx := Watches.link_ge core.database ((hmem x).mp (by simp))
      have hx' := hlf.1; rw [hend] at hx'; have := core.layout.nVars_pos
      simp only [clausesAt, END] at hx hx'; omega
  subst hrest
  refine ⟨⟨db, vs, core, fun r hr h2 w o hwo p hp hfa => hwe r hr h2 w o hwo p hp hfa fun _ => ⟨by simp, by simp⟩,
    ⟨?_, fun k h1 h2 => pmode.2 k (by omega) h2⟩, rel⟩, hpp⟩
  rw [hpp]
  rcases pmode.1 with h1 | ⟨hf, hb, hd⟩
  · exact Or.inl h1
  · exact Or.inr ⟨hf, hb, fun _ => by obtain ⟨D, h1, h2, h3⟩ := hd hP; exact ⟨D, h1, by omega, h3⟩⟩

/-- After the outer loop (C:157): with everything processed, setting `forced` at the root
gives `Settled`. -/
theorem OutInv.post {input : Input} {S0 : solver} {vs0 : List CInt} {S : solver} {f : CInt}
    (h : OutInv input S0 vs0 S f) (hpa : S.assigned ≤ S.processed) :
    ∃ db vs, Settled input (if (f != 0) = true then { S with forced := S.processed } else S) db vs ∧
      Rel S0 vs0 (if (f != 0) = true then { S with forced := S.processed } else S) vs := by
  obtain ⟨db, vs, core, watched, pmode, rel⟩ := h
  have ht := core.trail
  have hpa' : S.processed = S.assigned := by have := ht.assigned_le; omega
  have hpt : processedPos S = trailLen S := by simp only [processedPos, trailLen, hpa']
  split
  · rename_i hf
    have hf' : f ≠ 0 := by simpa using hf
    have hroot : ∀ i < trailLen S, RootLevel S i := by
      rcases pmode.1 with ⟨_, h1⟩ | ⟨h0, -⟩
      · exact h1
      · exact absurd h0 hf'
    refine ⟨db, vs, ⟨core.withForced hpa' hroot, watched, hpa', fun i hi _ => ?_⟩, rel⟩
    simp only [forcedPos, trailLen] at hi ⊢; rw [hpa']; exact hi
  · rename_i hf
    have hf' : f = 0 := by simpa using hf
    have hb : ∀ i < trailLen S, RootLevel S i → i < forcedPos S := by
      rcases pmode.1 with ⟨h1, _⟩ | ⟨_, h2, _⟩
      · exact absurd hf' h1
      · exact h2
    exact ⟨db, vs, ⟨core, watched, hpa', hb⟩, rel⟩

end MicrosatLean.Faithful.Verification
