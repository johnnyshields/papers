/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalDeterminantFirstJet
import SkewCornerDescent.Matrix.HessenbergFirstTrace
import SkewCornerDescent.Matrix.TriangularAdjacentInverse

/-!
# Complete first-normal Hessenberg slope is onsite minus adjacent pairs

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete determinant trace, full triangular inverse and exact selected
subdiagonal supply both terms. Higher normal jets and all upper entries remain
in the matrix; no first-slope or inverse-entry identity is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

/-- The genuine full normal determinant has its onsite slopes minus every
adjacent pair activity, with the actual subdiagonal normalization retained. -/
theorem hessenberg_normal_first_slope {F : Type*} [Field F] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (PowerSeries F))
    [Invertible (A.map PowerSeries.constantCoeff)] (hA : IsUpperHessenberg A)
    (a : F) (hsub : ∀ i j, i.val = j.val + 1 → A i j = PowerSeries.X * PowerSeries.C a) :
    PowerSeries.coeff 1 A.det * (PowerSeries.constantCoeff A.det)⁻¹ =
      (∑ i, PowerSeries.coeff 1 (A i i) * (PowerSeries.constantCoeff (A i i))⁻¹) -
      ∑ i : Fin n, a * PowerSeries.constantCoeff (A i.castSucc i.succ) *
        (PowerSeries.constantCoeff (A i.castSucc i.castSucc))⁻¹ *
        (PowerSeries.constantCoeff (A i.succ i.succ))⁻¹ := by
  classical
  let T := A.map PowerSeries.constantCoeff
  let B := A.map (PowerSeries.coeff 1)
  have hT : T.IsUpperTriangular := by
    intro i j hji
    change j.val < i.val at hji
    change PowerSeries.constantCoeff (A i j) = 0
    by_cases hfar : j.val + 1 < i.val
    · rw [hA i j hfar, map_zero]
    · have hnear : i.val = j.val + 1 := by omega
      rw [hsub i j hnear, map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hB : IsUpperHessenberg B := by
    intro i j hij
    change PowerSeries.coeff 1 (A i j) = 0
    rw [hA i j hij, map_zero]
  have hI : T⁻¹.IsUpperTriangular := Matrix.blockTriangular_inv_of_blockTriangular hT
  have hpair (i : Fin n) : B i.succ i.castSucc = a := by
    change PowerSeries.coeff 1 (A i.succ i.castSucc) = a
    rw [hsub i.succ i.castSucc rfl, PowerSeries.coeff_mul_C, PowerSeries.coeff_one_X, one_mul]
  rw [normal_det_first_slope]
  change Matrix.trace (T⁻¹ * B) = _
  rw [upper_hessenberg_trace _ _ hI hB]
  have hdiag : (∑ i, T⁻¹ i i * B i i) =
      ∑ i, PowerSeries.coeff 1 (A i i) * (PowerSeries.constantCoeff (A i i))⁻¹ := by
    apply Finset.sum_congr rfl
    intro i _
    rw [upper_triangular_inverse_diagonal T hT]
    exact mul_comm _ _
  rw [hdiag]
  have hpairs : (∑ i : Fin n, T⁻¹ i.castSucc i.succ * B i.succ i.castSucc) =
      -(∑ i : Fin n, a * PowerSeries.constantCoeff (A i.castSucc i.succ) *
        (PowerSeries.constantCoeff (A i.castSucc i.castSucc))⁻¹ *
        (PowerSeries.constantCoeff (A i.succ i.succ))⁻¹) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [upper_triangular_inverse_adjacent T hT, hpair]
    change -PowerSeries.constantCoeff (A i.castSucc i.succ) *
      (PowerSeries.constantCoeff (A i.castSucc i.castSucc))⁻¹ *
      (PowerSeries.constantCoeff (A i.succ i.succ))⁻¹ * a = _
    ring
  rw [hpairs, sub_eq_add_neg]

end SkewCornerDescent.Matrix
