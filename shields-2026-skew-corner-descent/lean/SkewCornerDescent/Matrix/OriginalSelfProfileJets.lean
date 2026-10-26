/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueChartGradient

/-!
# Higher self-profile jets from equal actual residue responses

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Equality of the actual rational residue responses gives equality of their
complete self-profile product coefficients in each surviving direction above
the selected span. The raw/chart correction is proved zero at that index,
not omitted or replaced by a proper selected-core product.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal actual residue responses have matching complete self-profile product
jets at an aligned degree whose resolving generator is above the selected span. -/
theorem original_self_profile_coeff_eq_of_residue_eq {n m : ℕ}
    (P : Profile n) (Q : Profile m)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (b' d' : Option (OriginalSelectedBlocks (hD := hD) Q))
    (j : ℕ+) (hj : c.top < j) (k : ℕ)
    (hkP : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (j : ℤ) = (k : ℤ))
    (hkQ : Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl b')) -
      Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl d')) - (j : ℤ) = (k : ℤ))
    (hS : c.regularResidue (c.originalLocalResponse P b d) =
      c.regularResidue (c.originalLocalResponse Q b' d')) :
    (c.originalResidueLeftEndpointPolynomial P b d *
      c.originalResidueRightEndpointPolynomial P b d).coeff k =
    (c.originalResidueLeftEndpointPolynomial Q b' d' *
      c.originalResidueRightEndpointPolynomial Q b' d').coeff k := by
  have hps : polynomialSpan (cellSchur D hD.1) = (c.top : ℕ) := by
    rw [polynomialSpan_cellSchur hD, ← c.span_eq]
  have hnot : j ∉ (cellSchur D hD.1).vars := by
    intro hmem
    have hle : (j : ℕ) ≤ polynomialSpan (cellSchur D hD.1) := Finset.le_sup hmem
    rw [hps] at hle
    exact (not_le_of_gt hj) hle
  have hψ : c.residueMap (pderiv j (cellSchur D hD.1)) = 0 := by
    rw [pderiv_eq_zero_of_notMem_vars hnot, map_zero]
  let l := k + ((j : ℕ) - (c.top : ℕ))
  have hjval : (c.top : ℕ) < (j : ℕ) := hj
  have hlP : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (c.top : ℤ) = (l : ℤ) := by
    dsimp only [l]
    omega
  have hlQ : Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl b')) -
      Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl d')) - (c.top : ℤ) = (l : ℤ) := by
    dsimp only [l]
    omega
  have hp := c.originalLocalResponse_raw_chart_first_jet P b d j k l hkP hlP
  have hq := c.originalLocalResponse_raw_chart_first_jet Q b' d' j k l hkQ hlQ
  rw [hψ, zero_mul, add_zero] at hp hq
  exact hp.trans ((congrArg (residueChartDeriv c.top j) hS).trans hq.symm)

end SkewCornerDescent.Matrix.SelectedCoordinate
