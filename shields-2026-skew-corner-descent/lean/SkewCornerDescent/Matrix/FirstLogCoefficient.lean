/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Mathlib.RingTheory.PowerSeries.Log

/-!
# Exact first coefficient of the complete normalized logarithm

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The held formal derivative chain rule computes the first logarithmic coefficient.
Every original first jet remains, and the unit constant supplies normalization.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The first coefficient of the complete logarithm of a residue-one series
is its actual first coefficient, by the full substitution chain rule. -/
theorem normal_log_coeff_one {F : Type*} [CommRing F] [Algebra ℚ F]
    (p : PowerSeries F) (hp : PowerSeries.constantCoeff p = 1) :
    PowerSeries.coeff 1 (PowerSeries.logOf p) = PowerSeries.coeff 1 p := by
  have hd (f : PowerSeries F) :
      PowerSeries.constantCoeff (PowerSeries.derivative f) = PowerSeries.coeff 1 f := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero, zero_add,
      Nat.cast_one, mul_one] using PowerSeries.coeff_derivative f 0
  have h0 : PowerSeries.constantCoeff (p - 1) = 0 := by simp [hp]
  have hs : PowerSeries.constantCoeff
      ((PowerSeries.derivative (PowerSeries.log F)).subst (p - 1)) =
      PowerSeries.constantCoeff (PowerSeries.derivative (PowerSeries.log F)) := by
    change MvPowerSeries.constantCoeff
      ((PowerSeries.derivative (PowerSeries.log F)).subst (p - 1)) = _
    simpa only [Algebra.algebraMap_self_apply] using
      PowerSeries.constantCoeff_subst_of_constantCoeff_zero h0
        (PowerSeries.derivative (PowerSeries.log F))
  rw [← hd (PowerSeries.logOf p), PowerSeries.logOf_eq,
    PowerSeries.derivative_subst (PowerSeries.HasSubst.of_constantCoeff_zero h0), map_mul, hs]
  simp only [hd, PowerSeries.coeff_one_log,
    one_mul, map_sub, PowerSeries.coeff_one, Nat.one_ne_zero, ↓reduceIte, sub_zero]

/-- The complete first normalized logarithmic coefficient is the actual slope,
with division justified by its nonzero constant. -/
theorem normalized_log_coeff_one {F : Type*} [Field F] [Algebra ℚ F]
    (p : PowerSeries F) (hp : PowerSeries.constantCoeff p ≠ 0) :
    PowerSeries.coeff 1 (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)) =
      PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹ := by
  rw [normal_log_coeff_one _ (by simp [hp]), PowerSeries.coeff_C_mul, mul_comm]

end SkewCornerDescent.Matrix
