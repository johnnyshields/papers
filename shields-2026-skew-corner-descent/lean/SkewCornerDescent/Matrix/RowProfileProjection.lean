/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.RowBlockInverse
import SkewCornerDescent.Matrix.ProfileInverseProjection

/-!
# Full inverse projections of literal row inventories count unit vertices

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
Unit endpoint weights project the complete inverse onto equal physical row and
column coordinates. Actual singleton block support removes only cross-block
entries, and the actual inverse identity supplies each unit diagonal value.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {ν α F : Type*} [Fintype ν] [DecidableEq ν] [LinearOrder α] [CommRing F]

/-- With unit endpoint profiles and literal singleton blocks, the complete
inverse projection counts exactly the original unit vertices at that position.
Off-diagonal inverse entries at other positions are not deleted. -/
theorem row_profile_inverse_projection_count (M : Matrix ν ν F) [Invertible M]
    (row col : ν → ℤ) (label : ν → α) (hlabel : Function.Injective label)
    (hM : M.BlockTriangular label)
    (hseparation : ∀ i j, label i < label j → row j < col i)
    (hunit : ∀ i, row i = col i → M i i = 1) (z : ℤ) :
    profileInverseProjection row col (⅟M) 1 1 z =
      ((Finset.univ.filter fun i => row i = z ∧ col i = z).card : F) := by
  classical
  have hI := Matrix.blockTriangular_inv_of_blockTriangular hM
  have hOne (k : ℤ) : (1 : LaurentPolynomial F).coeff k = if k = 0 then 1 else 0 := by
    simp only [AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single,
      Finsupp.single_apply, eq_comm (a := (0 : ℤ))]
  have hleft (i : ν) : (1 : LaurentPolynomial F).coeff (z - col i) =
      if col i = z then 1 else 0 := by
    rw [hOne]
    have h : (z - col i = 0) ↔ col i = z := by omega
    simp only [h]
  have hright (j : ν) : (1 : LaurentPolynomial F).coeff (row j - z) =
      if row j = z then 1 else 0 := by simp only [hOne, sub_eq_zero]
  have hinner (i : ν) :
      (∑ j, (if col i = z then 1 else 0 : F) * (⅟M) i j *
        (if row j = z then 1 else 0)) = if row i = z ∧ col i = z then 1 else 0 := by
    rw [Finset.sum_eq_single i]
    · by_cases hb : row i = z ∧ col i = z
      · have hd := row_block_inverse_unit_diagonal M label hlabel hM i
          (hunit i (hb.1.trans hb.2.symm))
        simp only [ite_eq_left hb.1, ite_eq_left hb.2, ite_eq_left hb, hd, mul_one]
      · rcases not_and_or.mp hb with hr | hc
        · simp only [ite_eq_right hr, mul_zero, ite_eq_right hb]
        · simp only [ite_eq_right hc, zero_mul, ite_eq_right hb]
    · intro j _ hji
      by_cases hc : col i = z
      · by_cases hr : row j = z
        · have hz : (⅟M) i j = 0 := by
            simpa only [Matrix.invOf_eq_nonsing_inv] using
              row_block_inverse_equal_coordinate_zero M⁻¹ row col label hlabel hI hseparation
                i j hji.symm (hr.trans hc.symm)
          simp only [hz, mul_zero, zero_mul]
        · simp only [ite_eq_right hr, mul_zero]
      · simp only [ite_eq_right hc, zero_mul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  unfold profileInverseProjection
  simp only [hleft, hright, hinner]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

end SkewCornerDescent.Matrix
