/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalCoefficientLeibniz

/-!
# Exact next-fresh coefficient calculus for complete normal products

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
One order after the first possible generator dependence, two zero-constant
series contribute their complete first coefficients. Higher powers contribute
nothing; the quadratic power remains at order two. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F M : Type*} [Field F] [Algebra ℚ F]
  [AddCommGroup M] [Module F M] [Module ℚ M]

/-- At the next fresh order, a product of two zero-constant series has exactly two
first-coefficient contributions. The full series, not frozen constants, are used. -/
theorem coeff_deriv_mul_next (D : Derivation ℚ F M) (p q : PowerSeries F) (n : ℕ)
    (hn : 2 ≤ n) (hp0 : PowerSeries.constantCoeff p = 0)
    (hq0 : PowerSeries.constantCoeff q = 0)
    (hp : ∀ k, k < n - 1 → D (PowerSeries.coeff k p) = 0)
    (hq : ∀ k, k < n - 1 → D (PowerSeries.coeff k q) = 0) :
    D (PowerSeries.coeff n (p * q)) =
      PowerSeries.coeff 1 p • D (PowerSeries.coeff (n - 1) q) +
        PowerSeries.coeff 1 q • D (PowerSeries.coeff (n - 1) p) := by
  rw [PowerSeries.coeff_mul, map_sum]
  simp only [Derivation.leibniz]
  rw [Finset.sum_add_distrib]
  congr 1
  · apply Finset.sum_eq_single (1, n - 1)
    · intro j hj hne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
      by_cases he : j.2 < n - 1
      · rw [hq _ he, smul_zero]
      · have hj0 : j.1 = 0 := by
          by_contra h
          apply hne
          apply Prod.ext <;> omega
        rw [hj0, PowerSeries.coeff_zero_eq_constantCoeff_apply, hp0, zero_smul]
    · intro hnot
      apply False.elim
      apply hnot
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)
  · apply Finset.sum_eq_single (n - 1, 1)
    · intro j hj hne
      have hs := Finset.HasAntidiagonal.mem_antidiagonal.mp hj
      by_cases he : j.1 < n - 1
      · rw [hp _ he, smul_zero]
      · have hj0 : j.2 = 0 := by
          by_contra h
          apply hne
          apply Prod.ext <;> omega
        rw [hj0, PowerSeries.coeff_zero_eq_constantCoeff_apply, hq0, zero_smul]
    · intro hnot
      apply False.elim
      apply hnot
      exact Finset.HasAntidiagonal.mem_antidiagonal.mpr (by omega)

/-- Only the linear and quadratic powers of a complete zero-constant series contribute
at the next fresh order. This includes the full self-square at order two. -/
theorem coeff_deriv_pow_next (D : Derivation ℚ F M) (p : PowerSeries F) (n : ℕ)
    (hn : 2 ≤ n) (h0 : PowerSeries.constantCoeff p = 0)
    (hp : ∀ k, k < n - 1 → D (PowerSeries.coeff k p) = 0) (a : ℕ) :
    D (PowerSeries.coeff n (p ^ a)) =
      if a = 1 then D (PowerSeries.coeff n p)
      else if a = 2 then (2 : F) •
        (PowerSeries.coeff 1 p • D (PowerSeries.coeff (n - 1) p)) else 0 := by
  obtain (_ | _ | _ | a) := a
  · simp [show n ≠ 0 by omega]
  · simp
  · rw [pow_two, coeff_deriv_mul_next D p p n hn h0 h0 hp hp]
    simp [two_smul]
  · rw [pow_succ]
    have hpa : ∀ k, k < n - 1 → D (PowerSeries.coeff k (p ^ (a + 2))) = 0 := by
      intro k hk
      exact coeff_deriv_pow_zero D p k (fun l hl => hp l (hl.trans_lt hk)) _
    have hp0 : PowerSeries.constantCoeff (p ^ (a + 2)) = 0 := by simp [map_pow, h0]
    rw [coeff_deriv_mul_next D _ p n hn hp0 h0 hpa hp,
      coeff_deriv_pow_first D p (n - 1) (by omega) h0 hp,
      PowerSeries.coeff_one_pow]
    simp [h0]

end SkewCornerDescent.Matrix
