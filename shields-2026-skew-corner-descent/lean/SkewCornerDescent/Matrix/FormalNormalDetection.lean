/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.FormalLogProduct

/-!
# Finite-order detection through a genuine unit prefactor

Formalizes the order-transfer step in `shields-2026-skew-corner-descent.tex`,
`prop:normal-interface`.  A nonzero normalized logarithmic coefficient detects
a positive original ratio coefficient no later.  A complete unit prefactor
cannot hide every such coefficient through the same order; the proof retains
its full inverse and the whole coefficient convolution.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- A nonzero logarithmic coefficient of a residue-one series detects an
actual positive coefficient of its difference from one no later. -/
theorem log_coeff_ne_zero_imp_ratio_detection {F : Type*} [CommRing F] [Algebra ℚ F]
    (R : PowerSeries F) (hR : PowerSeries.constantCoeff R = 1) (n : ℕ)
    (hlog : PowerSeries.coeff n (PowerSeries.logOf R) ≠ 0) :
    ∃ j : ℕ, 0 < j ∧ j ≤ n ∧ PowerSeries.coeff j (R - 1) ≠ 0 := by
  classical
  by_contra hn
  have hjet (k : ℕ) (hk : k ≤ n) : PowerSeries.coeff k R = PowerSeries.coeff k 1 := by
    by_cases hk0 : k = 0
    · subst k
      simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, map_one] using hR
    · have hz : PowerSeries.coeff k (R - 1) = 0 := by
        by_contra he
        exact hn ⟨k, Nat.pos_of_ne_zero hk0, hk, he⟩
      exact sub_eq_zero.mp (by simpa only [map_sub] using hz)
  have h := logOf_coeff_congr R 1 hR (by simp) n hjet n le_rfl
  apply hlog
  rw [h]
  simp [PowerSeries.logOf_eq]

/-- A genuine unit prefactor cannot hide every positive coefficient detected
by the normalized logarithm through the same finite order.  The full inverse
and coefficient convolution are retained.

**Differs from the paper's route.** Finite logarithmic-jet congruence and the
full unit inverse replace the formal exponential in the order transfer. -/
theorem log_coeff_ne_zero_imp_prefactor_detection {F : Type*} [Field F] [Algebra ℚ F]
    (R U : PowerSeries F) (hR : PowerSeries.constantCoeff R = 1)
    (hU : PowerSeries.constantCoeff U ≠ 0) (n : ℕ)
    (hlog : PowerSeries.coeff n (PowerSeries.logOf R) ≠ 0) :
    ∃ j : ℕ, 0 < j ∧ j ≤ n ∧ PowerSeries.coeff j (U * (R - 1)) ≠ 0 := by
  classical
  obtain ⟨j, hj, hjn, hjR⟩ := log_coeff_ne_zero_imp_ratio_detection R hR n hlog
  by_contra hn
  have hzero (k : ℕ) (hk : k ≤ n) : PowerSeries.coeff k (U * (R - 1)) = 0 := by
    by_cases hk0 : k = 0
    · subst k
      simp [PowerSeries.coeff_zero_eq_constantCoeff_apply, hR]
    · by_contra he
      exact hn ⟨k, Nat.pos_of_ne_zero hk0, hk, he⟩
  have hinv : U⁻¹ * (U * (R - 1)) = R - 1 := by
    rw [← mul_assoc, PowerSeries.inv_mul_cancel U hU, one_mul]
  apply hjR
  rw [← hinv, PowerSeries.coeff_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
  rw [hzero p.2 (by omega), mul_zero]

end SkewCornerDescent.Matrix
