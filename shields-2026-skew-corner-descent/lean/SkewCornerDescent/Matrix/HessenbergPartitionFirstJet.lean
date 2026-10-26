/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.HessenbergFirstSlope
import SkewCornerDescent.Matrix.NormalInverseProductJets

/-!
# First normal coefficient after complete diagonal normalization

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full onsite jets cancel against the full reciprocal diagonal jets.
Every adjacent-pair residue remains with its actual two diagonal weights.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The full diagonal-normalized determinant's first coefficient consists exactly
of its adjacent pair activities; no diagonal series is frozen at its residue. -/
theorem hessenberg_partition_coeff_one {F : Type*} [Field F] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) (PowerSeries F))
    (hA : IsUpperHessenberg A) (a : F)
    (hsub : ∀ i j, i.val = j.val + 1 → A i j = PowerSeries.X * PowerSeries.C a)
    (hunit : ∀ i, PowerSeries.constantCoeff (A i i) ≠ 0) :
    PowerSeries.coeff 1 (A.det * ∏ i, (A i i)⁻¹) =
      -(∑ i : Fin n, a * PowerSeries.constantCoeff (A i.castSucc i.succ) *
        (PowerSeries.constantCoeff (A i.castSucc i.castSucc))⁻¹ *
        (PowerSeries.constantCoeff (A i.succ i.succ))⁻¹) := by
  let T := A.map PowerSeries.constantCoeff
  have hT : T.IsUpperTriangular := by
    intro i j hji
    change j.val < i.val at hji
    change PowerSeries.constantCoeff (A i j) = 0
    by_cases hfar : j.val + 1 < i.val
    · rw [hA i j hfar, map_zero]
    · rw [hsub i j (by omega), map_mul, PowerSeries.constantCoeff_X, zero_mul]
  have hdet : PowerSeries.constantCoeff A.det = ∏ i, PowerSeries.constantCoeff (A i i) := by
    rw [RingHom.map_det]
    exact Matrix.det_of_isUpperTriangular hT
  have hp0 : PowerSeries.constantCoeff A.det ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hunit i)
  have hT0 : T.det ≠ 0 := by
    rw [Matrix.det_of_isUpperTriangular hT]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hunit i)
  let := Matrix.invertibleOfIsUnitDet T (isUnit_iff_ne_zero.mpr hT0)
  have hs := hessenberg_normal_first_slope A hA a hsub
  let U := ∏ i, (A i i)⁻¹
  have hinvprod : (∏ i, (PowerSeries.constantCoeff (A i i))⁻¹) =
      (PowerSeries.constantCoeff A.det)⁻¹ := by
    rw [hdet, Finset.prod_inv_distrib]
  have hU0 : PowerSeries.constantCoeff U = (PowerSeries.constantCoeff A.det)⁻¹ := by
    simpa only [U, map_prod, PowerSeries.constantCoeff_inv] using hinvprod
  have hU1 := normal_inverse_product_coeff_one Finset.univ (fun i => A i i)
    (fun i _ => hunit i)
  change PowerSeries.coeff 1 U = _ at hU1
  rw [hinvprod] at hU1
  change PowerSeries.coeff 1 (A.det * U) = _
  rw [PowerSeries.coeff_one_mul, hU0, hU1]
  have hcancel : PowerSeries.constantCoeff A.det *
      (PowerSeries.constantCoeff A.det)⁻¹ = 1 := mul_inv_cancel₀ hp0
  linear_combination hs -
    (∑ i, PowerSeries.coeff 1 (A i i) * (PowerSeries.constantCoeff (A i i))⁻¹) * hcancel

end SkewCornerDescent.Matrix
