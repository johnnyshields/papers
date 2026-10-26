/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalCoefficientDerivatives
import SkewCornerDescent.Matrix.OriginalCapNormalization
import SkewCornerDescent.Matrix.NormalLogCoefficient

/-!
# Complete original determinant logarithm normalization

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The original ordered response determinant supplies its own nonzero normal
constant, retaining both caps and every repeated internal occurrence.
The geometric first-fresh coefficient assembly is a separate obligation.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The entire actual response determinant is a normal unit. Its nonzero constant is
produced from all original diagonal occurrences, including coincident caps. -/
theorem originalHessenberg_normalSeries_constant_ne_zero {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    PowerSeries.constantCoeff (c.normalSeries (c.originalHessenbergResponse P).det) ≠ 0 := by
  classical
  rw [c.normalSeries_constant_apply, RingHom.map_det]
  change ((c.originalHessenbergResponse P).map c.regularResidue).det ≠ 0
  rw [c.originalHessenbergResponse_residue_det]
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact c.originalHessenberg_residue_ne_zero P hB hmax i

/-- The actual determinant's produced normal unit transfers a first fresh coefficient into
its full normalized logarithm. The earlier-independence premise is DERIVED: the complete
geometric interval-cost assembly must supply it before this lemma closes the transfer. -/
theorem originalHessenberg_normalized_log_derivative {n : ℕ} (P : Profile n)
    (hB : 0 < originalSelectedCount (hD := hD) P)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (K : ℕ+) (hK : c.top < K) (m : ℕ) (hm : 0 < m)
    (hprev : ∀ k, k < m → residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff k (c.normalSeries (c.originalHessenbergResponse P).det)) = 0) :
    let p := c.normalSeries (c.originalHessenbergResponse P).det
    residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩
      (PowerSeries.coeff m
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
        (PowerSeries.constantCoeff p)⁻¹ *
          residueGeneratorDeriv c.top ⟨K, ne_of_gt hK⟩ (PowerSeries.coeff m p) := by
  exact coeff_deriv_normalized_log_first _ _ m hm
    (c.originalHessenberg_normalSeries_constant_ne_zero P hB hmax) hprev

end SkewCornerDescent.Matrix.SelectedCoordinate
