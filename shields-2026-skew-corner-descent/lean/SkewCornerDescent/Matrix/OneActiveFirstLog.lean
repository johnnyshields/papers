/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OneActiveFirstCoefficient
import SkewCornerDescent.Matrix.FirstLogCoefficient

/-!
# The complete one-active first defect is its weighted first logarithm

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The exact residue-matched ratio retains every original first jet. The whole
normalized logarithms, not their partition factors, give its first defect.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Residue matching identifies the complete first defect with the weighted
normalized logarithms of the three full series, including its closure denominator. -/
theorem one_active_comparison_first_log {F : Type*} [Field F] [Algebra ℚ F]
    (E f T : PowerSeries F) (κ : F) (b a d : ℕ)
    (hE : PowerSeries.constantCoeff E ≠ 0)
    (hf : PowerSeries.constantCoeff f ≠ 0)
    (hT : PowerSeries.constantCoeff T ≠ 0)
    (hmatch : PowerSeries.constantCoeff E ^ b =
      κ * (PowerSeries.constantCoeff f ^ a * PowerSeries.constantCoeff T ^ d)) :
    let logNorm := fun p : PowerSeries F =>
      PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)
    PowerSeries.coeff 1 (PowerSeries.C κ⁻¹ * (E ^ b * (f ^ a * T ^ d)⁻¹) - 1) =
      PowerSeries.coeff 1 (b • logNorm E - a • logNorm f - d • logNorm T) := by
  dsimp only
  rw [map_sub, PowerSeries.coeff_one, ite_eq_right (by decide : (1 : ℕ) ≠ 0), sub_zero,
    one_active_comparison_coeff_one E f T κ b a d hE hf hT hmatch,
    map_sub, map_sub, map_nsmul, map_nsmul, map_nsmul,
    normalized_log_coeff_one E hE, normalized_log_coeff_one f hf,
    normalized_log_coeff_one T hT]
  simp only [nsmul_eq_mul]

end SkewCornerDescent.Matrix
