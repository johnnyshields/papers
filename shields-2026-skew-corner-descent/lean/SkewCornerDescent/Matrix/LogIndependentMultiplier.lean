/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.FormalLogProduct
import SkewCornerDescent.Matrix.NormalLogCoefficient

/-!
# Logarithmic invariance under complete independent unit factors

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The whole unit series is retained. Independence is required at each coefficient,
not merely at its residue or first normal jet.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F M : Type*} [Field F] [Algebra ℚ F]
    [AddCommGroup M] [Module F M] [Module ℚ M]

/-- Multiplying by a complete generator-independent normal unit changes no positive
coefficient derivative of the normalized logarithm. -/
theorem normalized_log_deriv_mul_independent (D : Derivation ℚ F M)
    (p q : PowerSeries F) (hp : PowerSeries.constantCoeff p ≠ 0)
    (hq : PowerSeries.constantCoeff q ≠ 0)
    (hqi : ∀ k, D (PowerSeries.coeff k q) = 0) (n : ℕ) (hn : 0 < n) :
    D (PowerSeries.coeff n (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff (p * q))⁻¹ * (p * q)))) =
    D (PowerSeries.coeff n (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) := by
  rw [normalized_log_mul_complete p q hp hq, map_add, map_add]
  rw [coeff_deriv_normalized_log_first D q n hn hq (fun k _ => hqi k),
    hqi n, smul_zero, add_zero]

end SkewCornerDescent.Matrix
