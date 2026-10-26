/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.Hessenberg

/-!
# Exact adjacent entries of the full upper triangular inverse

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full inverse equations and triangular support supply the diagonal reciprocals
and adjacent pair entries. No diagonal inverse approximation is made.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι] [LinearOrder ι]

/-- A full triangular inverse has the exact reciprocal diagonal, with nonvanishing
produced from its actual inverse equation. -/
theorem upper_triangular_inverse_diagonal (T : Matrix ι ι F) [Invertible T]
    (hT : T.IsUpperTriangular) (i : ι) : T⁻¹ i i = (T i i)⁻¹ := by
  classical
  have hI := Matrix.blockTriangular_inv_of_blockTriangular hT
  have hm := congrFun (congrFun (Matrix.mul_nonsing_inv T
    (Matrix.isUnit_det_of_invertible T)) i) i
  rw [Matrix.mul_apply, Matrix.one_apply_eq] at hm
  have hs : (∑ k, T i k * T⁻¹ k i) = T i i * T⁻¹ i i := by
    apply Finset.sum_eq_single i
    · intro k _ hki
      rcases lt_or_gt_of_ne hki with hlt | hgt
      · rw [hT hlt, zero_mul]
      · rw [hI hgt, mul_zero]
    · simp
  rw [hs] at hm
  have ha : T i i ≠ 0 := by
    intro he
    rw [he, zero_mul] at hm
    exact zero_ne_one hm
  have he := congrArg (fun x : F => (T i i)⁻¹ * x) hm
  simpa only [← mul_assoc, inv_mul_cancel₀ ha, one_mul, mul_one] using he

/-- The actual adjacent entry of the complete triangular inverse retains the
original upper pair and both produced diagonal reciprocals. -/
theorem upper_triangular_inverse_adjacent {n : ℕ}
    (T : Matrix (Fin (n + 1)) (Fin (n + 1)) F) [Invertible T]
    (hT : T.IsUpperTriangular) (i : Fin n) :
    T⁻¹ i.castSucc i.succ =
      -T i.castSucc i.succ * (T i.castSucc i.castSucc)⁻¹ * (T i.succ i.succ)⁻¹ := by
  classical
  have hI := Matrix.blockTriangular_inv_of_blockTriangular hT
  have hne : i.castSucc ≠ i.succ := by
    intro he
    have h := congrArg Fin.val he
    simp only [Fin.val_castSucc, Fin.val_succ] at h
    omega
  have hm := congrFun (congrFun (Matrix.mul_nonsing_inv T
    (Matrix.isUnit_det_of_invertible T)) i.castSucc) i.succ
  rw [Matrix.mul_apply, Matrix.one_apply_ne hne] at hm
  have hs : (∑ k, T i.castSucc k * T⁻¹ k i.succ) =
      T i.castSucc i.castSucc * T⁻¹ i.castSucc i.succ +
        T i.castSucc i.succ * T⁻¹ i.succ i.succ := by
    calc
      _ = ∑ k ∈ ({i.castSucc, i.succ} : Finset (Fin (n + 1))),
          T i.castSucc k * T⁻¹ k i.succ := by
        symm
        apply Finset.sum_subset (by simp)
        intro k _ hk
        have hki : k ≠ i.castSucc := by intro he; apply hk; simp [he]
        have hkj : k ≠ i.succ := by intro he; apply hk; simp [he]
        by_cases hlt : k < i.castSucc
        · exact mul_eq_zero.mpr (Or.inl (hT hlt))
        · have hgt : i.succ < k := by
            have hki' : k.val ≠ i.val := fun he => hki (Fin.ext he)
            have hkj' : k.val ≠ i.val + 1 := fun he => hkj (Fin.ext he)
            change i.val + 1 < k.val
            change ¬ k.val < i.val at hlt
            omega
          exact mul_eq_zero.mpr (Or.inr (hI hgt))
      _ = _ := by simp [hne]
  rw [hs, upper_triangular_inverse_diagonal T hT i.succ] at hm
  have ha : T i.castSucc i.castSucc ≠ 0 := by
    have hd := (Matrix.isUnit_det_of_invertible T).ne_zero
    rw [Matrix.det_of_isUpperTriangular hT] at hd
    exact (Finset.prod_ne_zero_iff.mp hd) i.castSucc (Finset.mem_univ _)
  apply mul_left_cancel₀ ha
  calc
    _ = -T i.castSucc i.succ * (T i.succ i.succ)⁻¹ := by linear_combination hm
    _ = _ := by field_simp [ha]

end SkewCornerDescent.Matrix
