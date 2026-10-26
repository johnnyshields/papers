/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalCoefficientLeibniz

/-!
# Fresh-generator coefficients of the complete formal logarithm

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The full logarithmic substitution keeps every nonlinear term. Its first fresh
coefficient derivative is the original coefficient derivative because all
higher powers have zero fresh derivative at that order.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F M : Type*} [Field F] [Algebra ℚ F]
  [AddCommGroup M] [Module F M] [Module ℚ M]

/-- At the first generator-dependent order, logging a unit-normalized complete series
preserves the generator derivative of its original coefficient. -/
theorem coeff_deriv_log_first (D : Derivation ℚ F M) (f : PowerSeries F) (n : ℕ)
    (hn : 0 < n) (hf : PowerSeries.constantCoeff f = 1)
    (hprev : ∀ k, k < n → D (PowerSeries.coeff k f) = 0) :
    D (PowerSeries.coeff n (PowerSeries.logOf f)) = D (PowerSeries.coeff n f) := by
  classical
  have h0 : PowerSeries.constantCoeff (f - 1) = 0 := by simp [hf]
  have hb := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hp : ∀ k, k < n → D (PowerSeries.coeff k (f - 1)) = 0 := by
    intro k hk
    simp only [map_sub, PowerSeries.coeff_one]
    split_ifs <;> simp [hprev k hk]
  rw [PowerSeries.logOf_eq, PowerSeries.coeff_subst' hb]
  change D.toLinearMap.toAddMonoidHom
    (∑ᶠ a, PowerSeries.coeff a (PowerSeries.log F) •
      PowerSeries.coeff n ((f - 1) ^ a)) = _
  rw [D.toLinearMap.toAddMonoidHom.map_finsum
    (PowerSeries.coeff_subst_finite' hb (PowerSeries.log F) n)]
  change (∑ᶠ a, D (PowerSeries.coeff a (PowerSeries.log F) •
    PowerSeries.coeff n ((f - 1) ^ a))) = _
  have hterm (a : ℕ) :
      D (PowerSeries.coeff a (PowerSeries.log F) •
        PowerSeries.coeff n ((f - 1) ^ a)) =
        if a = 1 then D (PowerSeries.coeff n f) else 0 := by
    rw [smul_eq_mul, Derivation.leibniz]
    have hc : D (PowerSeries.coeff a (PowerSeries.log F)) = 0 := by
      rw [PowerSeries.coeff_log]
      split_ifs
      · exact map_zero D
      · exact D.map_algebraMap _
    rw [hc, smul_zero, add_zero, coeff_deriv_pow_first D _ n hn h0 hp]
    by_cases ha : a = 1
    · subst a
      simp [PowerSeries.coeff_one, hn.ne']
    · simp [ha]
  simp_rw [hterm]
  rw [finsum_eq_single _ 1]
  · simp
  · intro a ha
    simp [ha]

/-- The complete normalization is constructed from the actual unit constant. Its first
fresh logarithmic derivative is the inverse constant times the original derivative. -/
theorem coeff_deriv_normalized_log_first (D : Derivation ℚ F M)
    (p : PowerSeries F) (n : ℕ) (hn : 0 < n)
    (hunit : PowerSeries.constantCoeff p ≠ 0)
    (hprev : ∀ k, k < n → D (PowerSeries.coeff k p) = 0) :
    D (PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
        (PowerSeries.constantCoeff p)⁻¹ • D (PowerSeries.coeff n p) := by
  have h0 : D (PowerSeries.constantCoeff p) = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hprev 0 hn
  have hinv : D (PowerSeries.constantCoeff p)⁻¹ = 0 := by
    rw [Derivation.leibniz_inv, h0, smul_zero]
  have hnorm : PowerSeries.constantCoeff
      (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p) = 1 := by
    simp [hunit]
  have hp : ∀ k, k < n → D (PowerSeries.coeff k
      (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)) = 0 := by
    intro k hk
    rw [PowerSeries.coeff_C_mul, Derivation.leibniz, hprev k hk, hinv,
      smul_zero, smul_zero, add_zero]
  rw [coeff_deriv_log_first D _ n hn hnorm hp, PowerSeries.coeff_C_mul,
    Derivation.leibniz, hinv, smul_zero, add_zero]

end SkewCornerDescent.Matrix
