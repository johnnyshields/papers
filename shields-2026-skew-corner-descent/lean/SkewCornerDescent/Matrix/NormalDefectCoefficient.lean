/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalLogCoefficient

/-!
# Normalized defect coefficients with nonzero earlier intrinsic terms

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The complete defect is a series times the difference of a residue-one ratio
from one. At the first fresh order its derivative is the residue prefactor
times the complete logarithmic coefficient derivative. Earlier intrinsic
coefficients need not vanish.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F M : Type*} [Field F] [Algebra ℚ F]
  [AddCommGroup M] [Module F M] [Module ℚ M]

/-- A residue-one ratio transfers its first fresh logarithmic coefficient to the original
normalized defect without discarding earlier intrinsic terms.

**Differs from the paper's route.** Uses the exact factorization `rho * (ratio - 1)`
directly rather than substituting the exponential of its logarithm. -/
theorem coeff_deriv_normal_defect (D : Derivation ℚ F M)
    (rho ratio : PowerSeries F) (n : ℕ) (hn : 0 < n)
    (hratio : PowerSeries.constantCoeff ratio = 1)
    (hpref : ∀ k, k < n → D (PowerSeries.coeff k rho) = 0)
    (hprev : ∀ k, k < n → D (PowerSeries.coeff k ratio) = 0) :
    D (PowerSeries.coeff n (rho * (ratio - 1))) =
      PowerSeries.constantCoeff rho • D (PowerSeries.coeff n (PowerSeries.logOf ratio)) := by
  have hsub : ∀ k, k < n → D (PowerSeries.coeff k (ratio - 1)) = 0 := by
    intro k hk
    simp only [map_sub, PowerSeries.coeff_one]
    split_ifs <;> simp [hprev k hk]
  rw [coeff_deriv_mul_first D rho (ratio - 1) n hpref hsub]
  have h0 : PowerSeries.constantCoeff (ratio - 1) = 0 := by simp [hratio]
  rw [h0, zero_smul, add_zero]
  rw [coeff_deriv_log_first D ratio n hn hratio hprev]
  simp [PowerSeries.coeff_one, hn.ne']

end SkewCornerDescent.Matrix
