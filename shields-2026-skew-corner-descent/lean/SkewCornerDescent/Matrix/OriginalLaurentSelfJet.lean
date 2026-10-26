/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueChartGradient

/-!
# Complete self-profile raw/chart correction at every resolving offset

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete correction keeps the actual first normal jet and all cyclic
occurrences. Negative profile offsets are not truncated to zero degrees.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing MvPolynomial
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete raw/chart self-product correction at every original generator.
The resolving offset is kept in the Laurent domain, so a negative offset does
not become a spurious constant coefficient by natural subtraction. -/
theorem originalLocalResponse_raw_chart_laurent_first_jet {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (j : ℕ+) (l : ℕ)
    (hl : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (c.top : ℤ) = (l : ℤ)) :
    ((c.originalResidueLeftEndpointPolynomial P b d *
      c.originalResidueRightEndpointPolynomial P b d).toLaurent).coeff
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (j : ℤ)) =
    residueChartDeriv c.top j (c.regularResidue (c.originalLocalResponse P b d)) +
      c.residueMap (pderiv j (cellSchur D hD.1)) *
        PowerSeries.coeff 1 (c.normalSeries (c.originalLocalResponse P b d)) := by
  have h := c.originalLocalResponse_residue_chart_profile_gradient P b d j
  have hcast : ((c.originalResidueLeftEndpointPolynomial P b d *
      c.originalResidueRightEndpointPolynomial P b d).toLaurent).coeff (l : ℤ) =
      (c.originalResidueLeftEndpointPolynomial P b d *
        c.originalResidueRightEndpointPolynomial P b d).coeff l := by
    change (Finsupp.mapDomain (fun z : ℕ => (z : ℤ))
      (c.originalResidueLeftEndpointPolynomial P b d *
        c.originalResidueRightEndpointPolynomial P b d).toFinsupp.coeff) (l : ℤ) = _
    exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ l
  rw [hl, hcast, ← c.originalLocalResponse_first_jet_profile P b d l hl] at h
  have hc : (c.normalCoefficient⁻¹ * c.residueMap (pderiv j (cellSchur D hD.1))) *
      (c.normalCoefficient * PowerSeries.coeff 1
        (c.normalSeries (c.originalLocalResponse P b d))) =
      c.residueMap (pderiv j (cellSchur D hD.1)) *
        PowerSeries.coeff 1 (c.normalSeries (c.originalLocalResponse P b d)) := by
    field_simp [c.normalCoefficient_ne_zero]
  rw [hc] at h
  linear_combination -h

end SkewCornerDescent.Matrix.SelectedCoordinate
