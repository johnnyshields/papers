/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ProfileInverseProjection

/-!
# Finite endpoint jets determine a supported inverse projection

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
A full inverse entry can contribute only at offsets whose sum is its actual
row-minus-column difference. A produced span bound therefore lets low proper-core
jets replace complete profiles without dropping an inverse entry. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {ν F : Type*} [Fintype ν] [CommRing F]

/-- Full profile inverse projections depend only on low endpoint jets when
nonzero inverse entries have the stated actual row-minus-column bound. -/
theorem profile_inverse_projection_low_jets (row col : ν → ℤ) (I : Matrix ν ν F)
    (N : ℤ) (hspan : ∀ i j, I i j ≠ 0 → row j - col i ≤ N)
    (A B C D : LaurentPolynomial F)
    (hA : ∀ k, k < 0 → A.coeff k = 0) (hB : ∀ k, k < 0 → B.coeff k = 0)
    (hC : ∀ k, k < 0 → C.coeff k = 0) (hD : ∀ k, k < 0 → D.coeff k = 0)
    (hAC : ∀ k, 0 ≤ k → k ≤ N → A.coeff k = C.coeff k)
    (hBD : ∀ k, 0 ≤ k → k ≤ N → B.coeff k = D.coeff k) (z : ℤ) :
    profileInverseProjection row col I A B z = profileInverseProjection row col I C D z := by
  classical
  unfold profileInverseProjection
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hI : I i j = 0
  · rw [hI, mul_zero, mul_zero, zero_mul, zero_mul]
  · have hs := hspan i j hI
    by_cases ha : z - col i < 0
    · simp only [hA _ ha, hC _ ha, zero_mul]
    · by_cases hb : row j - z < 0
      · rw [hB _ hb, hD _ hb, mul_zero, mul_zero]
      · rw [hAC _ (by omega) (by omega), hBD _ (by omega) (by omega)]

end SkewCornerDescent.Matrix
