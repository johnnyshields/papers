/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewClassInflation.BoundaryCoreGeometry
import SkewJacobiNegative.FirstVariations

/-!
# Private suffix support of boundary cores

Formalizes the residue application in `eq:suffix-support-recovery` of
`shields-2026-skew-class-inflation.tex`.  The literal cores are proved
zero-free and Hessenberg.  Equality of their actual polynomials recovers
the full ordered row list and every proper suffix bit.  Sorry-free.
-/

namespace SkewClassInflation.BoundaryParameters

open SkewJacobiNegative

variable (B : BoundaryParameters)

/-- Distinct representatives strictly below the modulus have distinct residue classes. -/
theorem residue_ne {x y : ℕ} (hx : x < B.q) (hy : y < B.q) (hne : x ≠ y) :
    (x : ZMod B.q) ≠ (y : ZMod B.q) := by
  intro h
  have := (ZMod.natCast_eq_natCast_iff' x y B.q).mp h
  rw [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this
  exact hne this

/-- The two allowed upper residues are disjoint from the nonterminal difference residues. -/
theorem residue_separation :
    ∀ x ∈ ({0, (B.p : ZMod B.q)} : Set (ZMod B.q)),
      ∀ y ∈ ({-(B.a : ZMod B.q)} : Set (ZMod B.q)),
        x - y ∉ ({0, (B.p : ZMod B.q)} : Set (ZMod B.q)) := by
  have hp := B.p_pos
  have hpa := B.p_lt_a
  have haq := B.ap_lt_q
  intro x hx y hy
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy ⊢
  subst y
  simp only [not_or]
  rcases hx with rfl | rfl
  · simp only [zero_sub, neg_neg]
    constructor
    · simpa only [Nat.cast_zero] using
        B.residue_ne (x := B.a) (y := 0) (by omega) (by omega) (by omega)
    · exact B.residue_ne (x := B.a) (y := B.p) (by omega) (by omega) (by omega)
  · rw [sub_neg_eq_add, add_comm, ← Nat.cast_add]
    constructor
    · simpa only [Nat.cast_zero] using
        B.residue_ne (x := B.a + B.p) (y := 0) haq (by omega) (by omega)
    · exact B.residue_ne (x := B.a + B.p) (y := B.p) haq (by omega) (by omega)

theorem core_row_residue (M : ℕ) (hM : 0 < M) (T : Finset ℕ) (i : Fin (M + 1)) :
    ((B.core M hM T).row i : ZMod B.q) ∈ ({0, (B.p : ZMod B.q)} : Set (ZMod B.q)) := by
  change (B.upper M T i : ZMod B.q) ∈ _
  unfold upper bit
  split_ifs <;> simp

theorem core_col_residue (M : ℕ) (hM : 0 < M) (T : Finset ℕ) (j : Fin (M + 1))
    (hj : j ≠ Fin.last M) :
    ((B.core M hM T).col j : ZMod B.q) ∈ ({-(B.a : ZMod B.q)} : Set (ZMod B.q)) := by
  have hj' : j.val ≠ M := by intro h; apply hj; exact Fin.ext h
  simp [core, lower, hj']

/-- Zero-freeness is proved for the full retained lists, not obtained by cancellation. -/
theorem core_zeroFree (M : ℕ) (hM : 0 < M) (T : Finset ℕ) :
    (B.core M hM T).ZeroFree := by
  intro i j he
  by_cases hj : j = Fin.last M
  · have hcol := (B.core M hM T).col_strictAnti.antitone (Fin.le_last i)
    have hrow := (B.core M hM T).row_nonempty i
    rw [hj, B.core_last_col M hM T] at he
    rw [B.core_last_col M hM T] at hcol
    omega
  · have hs := B.residue_separation _ (B.core_row_residue M hM T i)
      _ (B.core_col_residue M hM T j hj)
    have hd : ((B.core M hM T).row i : ZMod B.q) -
        ((B.core M hM T).col j : ZMod B.q) = 0 := by rw [he, sub_self]
    rw [hd] at hs
    exact hs (by simp)

/-- Every forbidden lower entry is genuinely negative. -/
theorem core_hessenberg (M : ℕ) (hM : 0 < M) (T : Finset ℕ) :
    ∀ i j : Fin (M + 1), j.val + 1 < i.val →
      (B.core M hM T).row i - (B.core M hM T).col j < 0 := by
  intro i j hij
  have hi := i.isLt
  have hj := j.isLt
  have hp := B.p_pos
  have hpa := B.p_lt_a
  have haq := B.ap_lt_q
  have hb := B.bit_le T (M + 1 - i.val)
  have hm : (B.q : ℤ) ≤ (B.q : ℤ) * ((i.val : ℤ) - j.val - 1) := by
    nlinarith [mul_nonneg (show (0 : ℤ) ≤ B.q by omega)
      (show (0 : ℤ) ≤ (i.val : ℤ) - j.val - 2 by omega)]
  change B.upper M T i - B.lower M j < 0
  rw [upper, ite_eq_right (by omega), ite_eq_right (by omega), lower,
    ite_eq_right (by omega)]
  nlinarith

/-- Equality of boundary-core functions determines the entire ordered upper beta list. -/
theorem core_rows_eq_of_schur_eq (M : ℕ) (hM : 0 < M) (T U : Finset ℕ)
    (he : (B.core M hM T).schur = (B.core M hM U).schur) :
    B.upper M T = B.upper M U := by
  exact BetaDiagram.row_list_eq_of_private_residues _ _
    (B.core_connected M hM T) (B.core_connected M hM U)
    {0, (B.p : ZMod B.q)} {-(B.a : ZMod B.q)}
    (B.core_row_residue M hM T) (B.core_row_residue M hM U)
    (B.core_col_residue M hM T) (B.core_col_residue M hM U)
    B.residue_separation (B.core_last_col M hM T) (B.core_last_col M hM U) he

/-- Every proper suffix bit is read without assuming equality of row words. -/
theorem core_suffix_mem_iff (M : ℕ) (hM : 0 < M) (T U : Finset ℕ)
    (he : (B.core M hM T).schur = (B.core M hM U).schur)
    (k : ℕ) (hk : 0 < k) (hkM : k < M) : k ∈ T ↔ k ∈ U := by
  have hr := B.core_rows_eq_of_schur_eq M hM T U he
  let i : Fin (M + 1) := ⟨M + 1 - k, by omega⟩
  have hi0 : i.val ≠ 0 := by dsimp [i]; omega
  have hi1 : i.val ≠ 1 := by dsimp [i]; omega
  have hik : M + 1 - i.val = k := by dsimp [i]; omega
  have hh := congrFun hr i
  simp only [upper, ite_eq_right hi0, ite_eq_right hi1, hik] at hh
  have hb : B.bit T k = B.bit U k := by omega
  have hp := B.p_pos
  unfold bit at hb
  split_ifs at hb <;> simp_all

/-- On proper suffix subsets, the boundary-core Schur function is injective. -/
theorem core_suffix_set_injective (M : ℕ) (hM : 0 < M) (T U : Finset ℕ)
    (hT : T ⊆ Finset.Ioo 0 M) (hU : U ⊆ Finset.Ioo 0 M)
    (he : (B.core M hM T).schur = (B.core M hM U).schur) : T = U := by
  ext k
  by_cases hk : k ∈ Finset.Ioo 0 M
  · exact B.core_suffix_mem_iff M hM T U he k
      (Finset.mem_Ioo.mp hk).1 (Finset.mem_Ioo.mp hk).2
  · exact iff_of_false (fun h => hk (hT h)) (fun h => hk (hU h))

/-- The exact support reading of `eq:suffix-support-recovery`: for a proper suffix position
`k`, the generator indexed by `q * k + p` occurs in the boundary core exactly when `k` is a
retained suffix. -/
theorem core_support_iff_mem_suffix (M : ℕ) (hM : 0 < M) (T : Finset ℕ) (k : ℕ)
    (hk : 0 < k) (hkM : k < M) :
    (⟨B.q * k + B.p, Nat.lt_of_lt_of_le B.p_pos (Nat.le_add_left _ _)⟩ : ℕ+) ∈
      (B.core M hM T).schur.vars ↔ k ∈ T := by
  classical
  have hp := B.p_pos
  have hpa := B.p_lt_a
  have haq := B.ap_lt_q
  have hq : 0 < B.q := by omega
  have hm : (k : ℤ) + 1 ≤ M := by exact_mod_cast hkM
  have hqz : (0 : ℤ) < B.q := by exact_mod_cast hq
  refine (BetaDiagram.private_residue_support (B.core M hM T) (B.core_connected M hM T)
    {0, (B.p : ZMod B.q)} {-(B.a : ZMod B.q)} (B.core_row_residue M hM T)
    (B.core_col_residue M hM T) B.residue_separation (B.core_last_col M hM T) _ ?_).trans ?_
  · simp
  · constructor
    · rintro ⟨i, hi⟩
      have hi' := i.isLt
      change B.upper M T i = ((B.q * k + B.p : ℕ) : ℤ) at hi
      unfold upper at hi
      push_cast at hi
      by_cases h0 : i.val = 0
      · rw [ite_eq_left h0] at hi
        exfalso
        nlinarith [mul_pos hqz (show (0 : ℤ) < (M : ℤ) - k by omega)]
      · by_cases h1 : i.val = 1
        · rw [ite_eq_right h0, ite_eq_left h1] at hi
          exfalso
          nlinarith [mul_le_mul_of_nonneg_left (show (1 : ℤ) ≤ (M : ℤ) - k by omega) hqz.le]
        · rw [ite_eq_right h0, ite_eq_right h1] at hi
          by_cases hT : M + 1 - i.val ∈ T
          · have hb : B.bit T (M + 1 - i.val) = B.p := by simp [bit, hT]
            rw [hb] at hi
            have hmul : (B.q : ℤ) * ((M : ℤ) + 1 - i.val) = B.q * k := by linarith
            have hj := mul_left_cancel₀ hqz.ne' hmul
            have hnat : M + 1 - i.val = k := by omega
            rw [hnat] at hT
            exact hT
          · have hb : B.bit T (M + 1 - i.val) = 0 := by simp [bit, hT]
            rw [hb] at hi
            push_cast at hi
            exfalso
            rcases le_or_gt ((M : ℤ) + 1 - i.val) k with hle | hgt
            · nlinarith [mul_le_mul_of_nonneg_left hle hqz.le]
            · nlinarith [mul_le_mul_of_nonneg_left
                (show (k : ℤ) + 1 ≤ (M : ℤ) + 1 - i.val by omega) hqz.le]
    · intro hkT
      have h0 : ¬ M + 1 - k = 0 := by omega
      have h1 : ¬ M + 1 - k = 1 := by omega
      have hk' : M + 1 - (M + 1 - k) = k := by omega
      refine ⟨⟨M + 1 - k, by omega⟩, ?_⟩
      change B.upper M T ⟨M + 1 - k, by omega⟩ = ((B.q * k + B.p : ℕ) : ℤ)
      have hb : B.bit T (M + 1 - (M + 1 - k)) = B.p := by
        rw [hk']
        simp [bit, hkT]
      have e : ((M + 1 - k : ℕ) : ℤ) = (M : ℤ) + 1 - k := by omega
      unfold upper
      dsimp only
      rw [ite_eq_right h0, ite_eq_right h1, hb]
      push_cast
      rw [e]
      ring

end SkewClassInflation.BoundaryParameters
