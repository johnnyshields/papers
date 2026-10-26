/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalNormalStructure
import SkewCornerDescent.Matrix.FirstLogCoefficient

/-!
# Complete original determinant logarithm splits into internal and true-cap parts

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Actual source support, selected subdiagonals and unit residues supply the complete
four-minor decomposition. The first-normal specialization retains every genuine
internal and boundary inverse jet, including higher-generator-dependent cap entries.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full original logarithmic coefficient is its complete internal coefficient
plus both actual true-cap coefficients below the whole selected cost. -/
theorem original_normal_log_internal_caps {n : ℕ} (P : Profile n)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (k : ℕ) (hk : k < originalSelectedCount (hD := hD) P) :
    let p := c.normalSeries (c.originalHessenbergResponse P).det
    let q := c.normalSeries (c.originalInternalResponseMatrix P).det
    PowerSeries.coeff k (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)) =
      PowerSeries.coeff k (PowerSeries.logOf
        (PowerSeries.C (PowerSeries.constantCoeff q)⁻¹ * q)) +
      PowerSeries.coeff k (leftCap (c.originalNormalExtension P)
        (originalSelectedCount (hD := hD) P)) +
      PowerSeries.coeff k (rightCap (c.originalNormalExtension P) 0
        (originalSelectedCount (hD := hD) P)) := by
  have hB : 0 < originalSelectedCount (hD := hD) P := by omega
  have h := normLog_internal_caps (c.originalNormalExtension P) c.normalCoefficient⁻¹
    (c.originalNormalExtension_shape P) (c.originalNormalExtension_subdiag P)
    (c.originalNormalExtension_regular P hB hmax) _ k hk
  unfold normLog at h
  rw [c.originalNormalExtension_det P, ← c.originalInternal_normal_det_interval P] at h
  exact h

/-- The original first-normal slope splits into the complete internal slope
and both true-cap first coefficients. Every unit premise comes from the source. -/
theorem original_first_slope_internal_caps {n : ℕ} (P : Profile n)
    (hB : 2 ≤ originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    let p := c.normalSeries (c.originalHessenbergResponse P).det
    let q := c.normalSeries (c.originalInternalResponseMatrix P).det
    PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹ =
      PowerSeries.coeff 1 q * (PowerSeries.constantCoeff q)⁻¹ +
      PowerSeries.coeff 1 (leftCap (c.originalNormalExtension P)
        (originalSelectedCount (hD := hD) P)) +
      PowerSeries.coeff 1 (rightCap (c.originalNormalExtension P) 0
        (originalSelectedCount (hD := hD) P)) := by
  have hp := c.originalHessenberg_normalSeries_constant_ne_zero P (by omega) hmax
  have hq := c.originalInternal_normal_constant_ne_zero P (by omega) hmax
  have h := c.original_normal_log_internal_caps P hmax 1 (by omega)
  dsimp only at h ⊢
  rw [normalized_log_coeff_one _ hp, normalized_log_coeff_one _ hq] at h
  exact h

end SkewCornerDescent.Matrix.SelectedCoordinate
