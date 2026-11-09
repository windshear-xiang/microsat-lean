import MicrosatLean.Faithful.Verification.AnalyzeBuild
import Std.Tactic.Do

/-!
# `analyze` meets its contract (C:102–129)

`mvcgen` splits `analyzeCore` into its six loops, with the invariants of
`AnalyzeState.lean`; each verification condition is one of the step lemmas of
`AnalyzeResolve.lean` and `AnalyzeBuild.lean`. `analyzeCore_spec` is used by
`Visit.conflict_step` (`Conflict.lean`).
-/

namespace MicrosatLean.Faithful.Verification

open Std.Do
set_option mvcgen.warning false
set_option linter.deprecated.syntax false

/-- The six loops of `analyzeCore` (C:103–129), from a conflict below the last decision `D`. -/
theorem analyzeCore_main {input : Input} {T : solver} {db : Records} {vs : List CInt} {D P : Nat}
    (ctx : ACtx input T db vs D) {r : Record} (hr : r ∈ db.all)
    (hfalse : ∀ l ∈ r.2, ∃ j < trailLen T, trailAt T j = l)
    (hmark : ∃ j, D ≤ j ∧ j < trailLen T ∧ trailAt T j ∈ r.2) (hDP : D ≤ P)
    (hwatched : ∀ s ∈ db.all, 2 ≤ s.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
      ∀ p < P, FalseAt T s.2[w]! p → ∃ q, FalseAt T (- s.2[o]!) q ∧ SameOrLowerLevel T p q) :
    ∃ L vs' B, Analyzed input T db (analyzeCore T r.1).1 (analyzeCore T r.1).2 L vs' B ∧ B ≤ D := by
  generalize hR : analyzeCore T r.1 = R
  apply Id.of_wp_run_eq hR
  mvcgen [analyzeCore]
  case inv1 => exact fun ⟨_, cl⟩ => ULift.up (T.mem_used - cl).toNat
  case inv2 => exact ⇓ x => match x with
    | .inl ⟨S, cl⟩ => ⌜BumpInv T S r.1 r.2 cl⌝
    | .inr ⟨S, cl⟩ => ⌜BumpInv T S r.1 r.2 cl ∧ S.ld cl = 0⌝
  case inv3 => exact fun ⟨S, _, _⟩ => ULift.up (S.assigned - T.falseStack).toNat
  case inv4 => exact ⇓ x => match x with
    | .inl ⟨S, _, g⟩ => ⌜g = false ∧ ∃ a, ResInv input T D S a⌝
    | .inr ⟨S, _, _⟩ => ⌜∃ u, BuildStart input T D S u⌝
  case inv5 => exact fun ⟨_, ck⟩ => ULift.up (ck - T.falseStack).toNat
  case inv6 =>
    rename_i S2 r0 h3 b mb S1' s cl g S1 h2 jp h1 h
    exact ⇓ x => match x with
      | .inl ⟨g, ck⟩ => ⌜g = false ∧ CheckInv T D S1 ck⌝
      | .inr ⟨g, _⟩ => ⌜CheckOut T D S1 g⌝
  case inv7 => exact fun ⟨_, cl⟩ => ULift.up (T.mem_used - cl).toNat
  case inv8 =>
    rename_i S2 r1 h5 b mb S1' s cl g1 S1 h4 jp h3 h2 r0 g h1 h
    exact ⇓ x => match x with
      | .inl ⟨S, cl⟩ => ⌜RBump T db S1 S cl⌝
      | .inr ⟨S, cl⟩ => ⌜RBump T db S1 S cl ∧ S.ld cl = 0⌝
  case inv9 => exact fun ⟨_, _, _, _, p⟩ => ULift.up (p + 1 - T.forced).toNat
  case inv10 =>
    rename_i S2 r1 h1 r0 Sb Sp p h
    exact ⇓ x => match x with
      | .inl ⟨S, size, _, _, p⟩ => ⌜BLoop input T D Sb S size p⌝
      | .inr ⟨S, size, _, _, p⟩ => ⌜BLoop input T D Sb S size p ∧ p < S.forced⌝
  case inv11 => exact fun S => ULift.up (S.assigned - S.processed).toNat
  case inv12 =>
    rename_i S7 r2 h2 r1 S6 S5 p h1 r0 S4 s1 size s0 lbd S3 S2 S1 Se h
    exact ⇓ x => match x with
      | .inl S => ⌜UInv T Se S⌝
      | .inr S => ⌜UInv T Se S ∧ ¬ S.assigned > S.processed⌝
  -- C:104: bump the conflict clause
  case vc1 =>
    rename_i cl0 S1 b mb S cl hc h
    obtain ⟨hvar, hinv⟩ := h
    simp [WhileVariant.eval] at hvar hc hinv
    obtain ⟨h1, h2, h3⟩ := BumpInv.step ctx hr hfalse (hinv : BumpInv T S r.1 r.2 cl) hc
    refine ⟨(T.mem_used - (cl + 1)).toNat, by simp [WhileVariant.eval], ?_, by simpa using h1⟩
    rw [hvar]; exact toNat_lt_toNat' h2 h3
  case vc2 =>
    rename_i cl0 S1 b mb S cl hc h
    obtain ⟨hvar, hinv⟩ := h
    simp [WhileVariant.eval] at hvar hc hinv ⊢
    exact ⟨hinv, hc⟩
  case vc3 =>
    simp
    exact ⟨RState.init ctx, rfl, 0, Nat.zero_le _, (by simp : r.1 = r.1 + ((0 : Nat) : CInt)),
      fun i _ _ hm => by simp at hm⟩
  -- C:105: start the resolution loop
  case vc15 =>
    rename_i cl0 S1 r0 h0
    simp at h0 ⊢
    exact ⟨_, ResInv.init ctx hr hfalse hmark h0.1 h0.2⟩
  case vc4 =>
    rename_i cl0 S1 r0 h0 b mb S2 s cl g S hz h
    simp [WhileVariant.eval] at h hz ⊢
    obtain ⟨-, -, a, hres⟩ := h
    have hz' : reasonOf T (trailAt T (a - 1)) = 0 := by rw [← (hres.reads ctx).2.2.2.2.1]; exact hz
    exact ⟨a - 1, hres.decision ctx hz'⟩
  -- C:108–109: the check loop
  case vc5 =>
    rename_i cl0 S0 r0 h5 b1 mb1 S1 s cl g1 S h4 jp h3 h2 b mb g ck1 ck h1 h
    simp [WhileVariant.eval] at h2 h1 h
    obtain ⟨-, -, a, hres⟩ := h2
    simp
    exact vc_check_mark ctx hres h.2 h1
  case vc6 =>
    rename_i cl0 S0 r0 h5 b1 mb1 S1 s cl g1 S h4 jp h3 h2 b mb g ck1 ck h1' h1 h
    simp [WhileVariant.eval] at h2 h1' h1 h
    obtain ⟨-, -, a, hres⟩ := h2
    simp
    exact vc_check_dec ctx hres h.2 h1' h1
  case vc7 =>
    rename_i cl0 S0 r0 h5 b1 mb1 S1 s cl g1 S h4 jp h3 h2 b mb g ck1 ck h1' h1 h
    simp [WhileVariant.eval] at h2 h1' h1 h
    obtain ⟨-, -, a, hres⟩ := h2
    obtain ⟨e1, e2, e3⟩ := vc_check_next ctx hres h.2 h1' h1
    refine ⟨(ck - T.falseStack).toNat, by simp [WhileVariant.eval], ?_, by simpa using ⟨e2, e3⟩⟩
    first | exact Nat.lt_of_lt_of_eq e1 h.1 | exact Nat.lt_of_lt_of_eq e1 h.1.symm
  case vc8 =>
    rename_i cl0 S0 r0 h5 b mb S1 s cl g S h4 jp h3 h
    simp [WhileVariant.eval] at h h4
    obtain ⟨-, hg, a, hres⟩ := h
    simp
    exact ⟨hg, vc_check_start ctx hres h4⟩
  case vc9 =>
    rename_i cl0 S0 r0 h5 b mb S1 s cl g1 S h4 jp h3 h2 rc g hg h
    simp [WhileVariant.eval] at h2 h3 h4 h hg
    obtain ⟨-, -, a, hres⟩ := h2
    simp
    exact vc_uip ctx hres h3 h hg
  -- C:111–112: bump the reason
  case vc10 =>
    rename_i cl0 S0 r1 h7 b1 mb1 S2 s cl1 g1 S1 h6 jp h5 h4 r0 g h3 h2 b mb S cl h1 h
    simp [WhileVariant.eval] at h1 h
    obtain ⟨e1, e2, e3⟩ := RBump.step ctx h.2 h1
    refine ⟨(T.mem_used - (cl + 1)).toNat, by simp [WhileVariant.eval], ?_, by simpa using e1⟩
    rw [h.1]; exact toNat_lt_toNat' e2 e3
  case vc11 =>
    rename_i cl0 S0 r1 h7 b1 mb1 S2 s cl1 g1 S1 h6 jp h5 h4 r0 g h3 h2 b mb S cl h1 h
    simp [WhileVariant.eval] at h1 h ⊢
    exact ⟨h.2, h1⟩
  case vc12 =>
    rename_i cl0 S0 r1 h5 b mb S2 s cl g1 S1 h4 jp h3 h2 r0 g h1 h
    simp [WhileVariant.eval] at h2 h4
    obtain ⟨-, -, a, hres⟩ := h2
    simp
    exact vc_rbump_start ctx hres h4
  -- C:113: resolve or skip the top literal, unassign it
  case vc13 =>
    rename_i cl0 S0 r2 h6 b mb S1' s cl g1 S1 h5 jp h4 h3 r1 g h2 h1 r0 h
    simp [WhileVariant.eval] at h3 h4 h2 h1 h
    obtain ⟨hv, -, a, hres⟩ := h3
    obtain ⟨e1, e2, e3⟩ := vc_resolve ctx hres h4 h1 h2 h
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e1 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · simp; exact ⟨e2, e3⟩
  case vc14 =>
    rename_i cl0 S0 r0 h3 b mb S1' s cl g S1 h2 jp h1 h
    simp [WhileVariant.eval] at h2 h1 h
    obtain ⟨hv, hg, a, hres⟩ := h
    obtain ⟨e1, e2, e3⟩ := vc_skip ctx hres hg h2 h1
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e1 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · simp; exact ⟨e2, e3⟩
  case vc16 =>
    rename_i cl0 S0 r1 h7 r0 Sb Sp p1 h6 b mb S s2 size s1 lbd1 s0 flg p hpf jp1 h4 h3 jp h2 lbd h1 h
    simp only [beq_iff_eq, bne_iff_ne, ne_eq] at h4 h3 h2 h1
    simp [WhileVariant.eval] at h
    obtain ⟨hv, hinv⟩ := h
    obtain ⟨e1, e2⟩ := vc_build ctx hinv hpf (Or.inr (Or.inr ⟨h4, h3, rfl, rfl⟩)) (Or.inl ⟨h2, by omega, rfl⟩)
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · exact e1
  case vc17 =>
    rename_i cl0 S0 r1 h7 r0 Sb Sp p1 h6 b mb S s2 size s1 lbd1 s0 flg p hpf jp1 h4 h3 jp h2 lbd h1 h
    simp only [beq_iff_eq, bne_iff_ne, ne_eq] at h4 h3 h2 h1
    simp [WhileVariant.eval] at h
    obtain ⟨hv, hinv⟩ := h
    obtain ⟨e1, e2⟩ := vc_build ctx hinv hpf (Or.inr (Or.inr ⟨h4, h3, rfl, rfl⟩)) (Or.inr ⟨fun ⟨_, e⟩ => h1 e, rfl⟩)
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · exact e1
  case vc18 =>
    rename_i cl0 S0 r1 h6 r0 Sb Sp p1 h5 b mb S s2 size s1 lbd s0 flg p hpf jp1 h3 h2 jp h1 h
    simp only [beq_iff_eq, bne_iff_ne, ne_eq] at h3 h2 h1
    simp [WhileVariant.eval] at h
    obtain ⟨hv, hinv⟩ := h
    obtain ⟨e1, e2⟩ := vc_build ctx hinv hpf (Or.inr (Or.inr ⟨h3, h2, rfl, rfl⟩)) (Or.inr ⟨fun ⟨e, _⟩ => h1 e, rfl⟩)
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · exact e1
  case vc19 =>
    rename_i cl0 S0 r1 h7 r0 Sb Sp p1 h6 b mb S s2 size s1 lbd1 s0 flg p hpf jp1 h4 h3 jp h2 lbd h1 h
    simp only [beq_iff_eq, bne_iff_ne, ne_eq] at h4 h3 h2 h1
    simp [WhileVariant.eval] at h
    obtain ⟨hv, hinv⟩ := h
    obtain ⟨e1, e2⟩ := vc_build ctx hinv hpf (Or.inr (Or.inl ⟨h4, h3, rfl, rfl⟩)) (Or.inl ⟨h2, by omega, rfl⟩)
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · exact e1
  case vc20 =>
    rename_i cl0 S0 r1 h7 r0 Sb Sp p1 h6 b mb S s2 size s1 lbd1 s0 flg p hpf jp1 h4 h3 jp h2 lbd h1 h
    simp only [beq_iff_eq, bne_iff_ne, ne_eq] at h4 h3 h2 h1
    simp [WhileVariant.eval] at h
    obtain ⟨hv, hinv⟩ := h
    obtain ⟨e1, e2⟩ := vc_build ctx hinv hpf (Or.inr (Or.inl ⟨h4, h3, rfl, rfl⟩)) (Or.inr ⟨fun ⟨_, e⟩ => h1 e, rfl⟩)
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · exact e1
  case vc21 =>
    rename_i cl0 S0 r1 h6 r0 Sb Sp p1 h5 b mb S s2 size s1 lbd s0 flg p hpf jp1 h3 h2 jp h1 h
    simp only [beq_iff_eq, bne_iff_ne, ne_eq] at h3 h2 h1
    simp [WhileVariant.eval] at h
    obtain ⟨hv, hinv⟩ := h
    obtain ⟨e1, e2⟩ := vc_build ctx hinv hpf (Or.inr (Or.inl ⟨h3, h2, rfl, rfl⟩)) (Or.inr ⟨fun ⟨e, _⟩ => h1 e, rfl⟩)
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · exact e1
  case vc22 =>
    rename_i cl0 S0 r1 h6 r0 Sb Sp p1 h5 b mb S s2 size s1 lbd1 s0 flg p hpf jp1 h3 jp h2 lbd h1 h
    simp only [beq_iff_eq, bne_iff_ne, ne_eq] at h3 h2 h1
    simp [WhileVariant.eval] at h
    obtain ⟨hv, hinv⟩ := h
    obtain ⟨e1, e2⟩ := vc_build ctx hinv hpf (Or.inl ⟨h3, rfl, rfl⟩) (Or.inl ⟨h2, by omega, rfl⟩)
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · exact e1
  case vc23 =>
    rename_i cl0 S0 r1 h6 r0 Sb Sp p1 h5 b mb S s2 size s1 lbd1 s0 flg p hpf jp1 h3 jp h2 lbd h1 h
    simp only [beq_iff_eq, bne_iff_ne, ne_eq] at h3 h2 h1
    simp [WhileVariant.eval] at h
    obtain ⟨hv, hinv⟩ := h
    obtain ⟨e1, e2⟩ := vc_build ctx hinv hpf (Or.inl ⟨h3, rfl, rfl⟩) (Or.inr ⟨fun ⟨_, e⟩ => h1 e, rfl⟩)
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · exact e1
  case vc24 =>
    rename_i cl0 S0 r1 h5 r0 Sb Sp p1 h4 b mb S s2 size s1 lbd s0 flg p hpf jp1 h2 jp h1 h
    simp only [beq_iff_eq, bne_iff_ne, ne_eq] at h2 h1
    simp [WhileVariant.eval] at h
    obtain ⟨hv, hinv⟩ := h
    obtain ⟨e1, e2⟩ := vc_build ctx hinv hpf (Or.inl ⟨h2, rfl, rfl⟩) (Or.inr ⟨fun ⟨e, _⟩ => h1 e, rfl⟩)
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact hv.symm | exact hv
    · exact e1
  case vc25 =>
    rename_i cl0 S0 r1 h3 r0 Sb Sp p1 h2 b mb S s2 size s1 lbd s0 flg p h1 h
    simp [WhileVariant.eval] at h1 h ⊢
    exact ⟨h.2, h1⟩
  case vc26 =>
    rename_i cl0 S0 r1 h1 r0 Sb Sp p h
    simp at h
    obtain ⟨u, hst⟩ := h
    exact ⟨u, u + 1, [], hst, BState.init ctx hst, by simp, by
      have := hst.2.1; show r0.1.assigned + 1 = _; push_cast; omega⟩
  -- C:124–128: the unassign loop
  case vc29 =>
    rename_i cl0 S0 r2 h2 r1 Sb Sp p h1 r0 Se0 s1 size s0 lbd S3 S2 S1 Se h
    simp at h
    obtain ⟨u, ps, -, hb, -, hf, -, hA, -, -, hpp⟩ := BLoop.exit ctx h (Se := Se)
      (fun hf => ((hf.setFast _).setFast _ |>.setSlow _).setSlow _) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun _ => rfl) rfl rfl
    exact UInv.init hf hA (by rw [hpp]; exact hb.B_le)
  case vc27 =>
    rename_i cl0 S0 r2 h4 r1 Sb Sp p h3 r0 Se0 s1 size s0 lbd S5 S4 S3 Se h2 b mb h1 S1 S h
    simp at h2
    simp [WhileVariant.eval] at h h1
    obtain ⟨u, ps, -, hb, -, hf, hl, hA, hu, hpr, hpp⟩ := BLoop.exit ctx h2 (Se := Se)
      (fun hf => ((hf.setFast _).setFast _ |>.setSlow _).setSlow _) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun _ => rfl) rfl rfl
    obtain ⟨e1, e2⟩ := UInv.step ctx hl hu hpr h.2 h1
    refine ⟨_, ?_, Nat.lt_of_lt_of_eq e2 ?_, ?_⟩
    · simp [WhileVariant.eval] <;> rfl
    · first | exact h.1.symm | exact h.1
    · exact e1
  case vc28 =>
    rename_i cl0 S0 r2 h4 r1 Sb Sp p h3 r0 Se0 s1 size s0 lbd S3 S2 S1 Se h2 b mb h1 h
    simp [WhileVariant.eval] at h h1 ⊢
    exact ⟨h.2, h1⟩
  case vc30 =>
    rename_i cl0 S0 r3 h3 r2 Sb Sp p h2 r1 Se0 s1 size s0 lbd S5 S4 S3 Se h1 r0 S1 S h
    simp at h1 h
    exact analyzed_final ctx hDP hwatched h1 (Se := Se)
      (fun hf => ((hf.setFast _).setFast _ |>.setSlow _).setSlow _) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      (fun _ => rfl) rfl rfl rfl h

/-- Below `P`, the last decision at or below `P`. -/
theorem last_decision {T : solver} {P : Nat} (h : ∃ D ≤ P, IsDecision T D) :
    ∃ D ≤ P, IsDecision T D ∧ ∀ k, D < k → k ≤ P → ¬ IsDecision T k := by
  induction P with
  | zero =>
    obtain ⟨D, hD, hd⟩ := h
    exact ⟨D, hD, hd, fun k h1 h2 => by omega⟩
  | succ P ih =>
    by_cases hP : IsDecision T (P + 1)
    · exact ⟨P + 1, Nat.le_refl _, hP, fun k h1 h2 => by omega⟩
    · obtain ⟨D, hD, hd⟩ := h
      have hD' : D ≤ P := by
        rcases Nat.lt_or_ge D (P + 1) with h1 | h1
        · omega
        · have : D = P + 1 := by omega
          subst this; exact absurd hd hP
      obtain ⟨D', hD'P, hd', hlast⟩ := ih ⟨D, hD', hd⟩
      refine ⟨D', by omega, hd', fun k h1 h2 => ?_⟩
      rcases Nat.lt_or_ge k (P + 1) with h3 | h3
      · exact hlast k h1 (by omega)
      · have : k = P + 1 := by omega
        subst this; exact hP

/-- `analyzeCore` from a conflict below the root (C:102–129): the record `r` is false, `lit`
(at position `P`, being processed) is one of its literals, the last decision is at or below
`P`, and the watched-literal invariant holds below `P`. The backjump point is at most `P`.
Used by `Visit.conflict_step`. -/
theorem analyzeCore_spec {input : Input} {T : solver} {db : Records} {vs : List CInt} {P : Nat}
    {lit : CInt} {r : Record} (core : Core input T db vs) (hr : r ∈ db.all)
    (hfalse : ∀ l ∈ r.2, ∃ j < trailLen T, trailAt T j = l) (hlit : lit ∈ r.2)
    (hP : P < trailLen T) (hlitP : trailAt T P = lit) (hmode : PMode T 0 P)
    (hwatched : ∀ s ∈ db.all, 2 ≤ s.2.length → ∀ w o, (w = 0 ∧ o = 1 ∨ w = 1 ∧ o = 0) →
      ∀ p < P, FalseAt T s.2[w]! p → ∃ q, FalseAt T (- s.2[o]!) q ∧ SameOrLowerLevel T p q) :
    ∃ L vs' B, Analyzed input T db (analyzeCore T r.1).1 (analyzeCore T r.1).2 L vs' B ∧ B ≤ P := by
  obtain ⟨hm1, hm2⟩ := hmode
  rcases hm1 with ⟨h0, -⟩ | ⟨-, hroot, hdec⟩
  · exact absurd rfl h0
  obtain ⟨D0, hD0f, hD0P, hD0⟩ := hdec hP
  obtain ⟨D, hDP, hD, hlast⟩ := last_decision ⟨D0, hD0P, hD0⟩
  have ctx : ACtx input T db vs D := by
    refine ⟨core, hD, ?_, by omega, fun k h1 h2 => ?_, hroot⟩
    · exact Classical.byContradiction fun hlt =>
        core.trail.forced_root D (by omega) D (Nat.le_refl _) hD
    · rcases Nat.lt_or_ge P k with h3 | h3
      · exact hm2 k h3 h2
      · exact hlast k h1 h3
  obtain ⟨L, vs', B, ha, hB⟩ := analyzeCore_main ctx hr hfalse ⟨P, hDP, hP, by rw [hlitP]; exact hlit⟩ hDP hwatched
  exact ⟨L, vs', B, ha, by omega⟩


end MicrosatLean.Faithful.Verification
