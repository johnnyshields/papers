/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalRationalFactorization

/-!
# Retaining the orientation unit in normal coefficient transfer

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
A constant unit leaves the normalized series unchanged, but remains in exact residue
matching and the rational defect prefactor. Earlier intrinsic terms are retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F]

/-- Normalization cancels a nonzero constant unit exactly, at every coefficient. -/
theorem normalizedSeries_constant_unit_mul (p : PowerSeries F) (u : F) (hu : u ≠ 0) :
    PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.C u * p))⁻¹ *
      (PowerSeries.C u * p) = PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p := by
  rw [map_mul, PowerSeries.constantCoeff_C, mul_inv_rev, map_mul]
  have hc : PowerSeries.C u⁻¹ * PowerSeries.C u = (1 : PowerSeries F) := by
    rw [← map_mul, inv_mul_cancel₀ hu, map_one]
  calc
    _ = PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ *
        (PowerSeries.C u⁻¹ * PowerSeries.C u) * p := by ring
    _ = _ := by rw [hc, mul_one]

variable [CharZero F] [Module ℚ F]

/-- The orientation-scaled ratio transfers its logarithmic derivative with its exact
residue prefactor. The constant unit need only omit the resolving generator. -/
theorem coeff_deriv_oriented_normal_defect (D : Derivation ℚ F F)
    (rho ratio : PowerSeries F) (u : F) (hu : u ≠ 0) (hDu : D u = 0)
    (n : ℕ) (hn : 0 < n)
    (hmatch : PowerSeries.constantCoeff ratio = u⁻¹)
    (hpref : ∀ k, k < n → D (PowerSeries.coeff k rho) = 0)
    (hprev : ∀ k, k < n → D (PowerSeries.coeff k ratio) = 0) :
    D (PowerSeries.coeff n (rho * (PowerSeries.C u * ratio - 1))) =
      PowerSeries.constantCoeff rho * D (PowerSeries.coeff n
        (PowerSeries.logOf
          (PowerSeries.C (PowerSeries.constantCoeff ratio)⁻¹ * ratio))) := by
  have hR : PowerSeries.constantCoeff (PowerSeries.C u * ratio) = 1 := by
    rw [map_mul, PowerSeries.constantCoeff_C, hmatch, mul_inv_cancel₀ hu]
  have hprevR : ∀ k, k < n →
      D (PowerSeries.coeff k (PowerSeries.C u * ratio)) = 0 := by
    intro k hk
    rw [PowerSeries.coeff_C_mul, Derivation.leibniz, hDu, hprev k hk,
      smul_zero, smul_zero, add_zero]
  have he := coeff_deriv_normal_defect D rho (PowerSeries.C u * ratio) n hn
    hR hpref hprevR
  have hnorm := normalizedSeries_constant_unit_mul ratio u hu
  rw [hR, inv_one, map_one, one_mul] at hnorm
  rw [he, hnorm, smul_eq_mul]

end SkewCornerDescent.Matrix
