/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.EndpointVariation
import SkewCornerDescent.Matrix.OriginalResiduePolynomialChain
import SkewCornerDescent.Matrix.OriginalNormalDirectionGradient

/-!
# Full raw/chart correction for actual retained responses

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The chart direction is defined at fixed selected normal coordinate. All original
indices, including the selected index itself, retain the exact raw correction.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The chart derivative of every actual JT entry includes its selected raw partial. -/
theorem residue_hh_chart_derivative (j : ℕ+) (z : ℤ) :
    residueChartDeriv c.top j (c.residueMap (hh z)) =
      (if z = (j : ℤ) then 1 else 0) -
        (c.normalCoefficient⁻¹ * c.residueMap (pderiv j (cellSchur D hD.1))) *
          (if z = (c.top : ℤ) then 1 else 0) := by
  rw [c.original_residue_chart_polynomial_chain]
  simp only [pderiv_hh, apply_ite, map_one, map_zero]
  split_ifs <;> ring

/-- Chart differentiation of a complete residue response is the difference of the
raw profile coefficient and its exact selected-coordinate correction. -/
theorem residue_interval_chart_profile_gradient {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x y : ℤ) (j : ℕ+)
    [Invertible (vertexBetaMatrix c.residueMap row col)] :
    residueChartDeriv c.top j
        (c.residueMap (hh (x - y)) -
          (vertexOutgoing c.residueMap col x * ⅟(vertexBetaMatrix c.residueMap row col) *
            vertexIncoming c.residueMap row y) () ()) =
      (endpointProfile (fun i => x - row i)
          (fun i => (vertexOutgoing c.residueMap col x *
            ⅟(vertexBetaMatrix c.residueMap row col)) () i) *
        endpointProfile (fun i => col i - y)
          (fun i => (⅟(vertexBetaMatrix c.residueMap row col) *
            vertexIncoming c.residueMap row y) i ())).coeff (x - y - (j : ℤ)) -
      (c.normalCoefficient⁻¹ * c.residueMap (pderiv j (cellSchur D hD.1))) *
      (endpointProfile (fun i => x - row i)
          (fun i => (vertexOutgoing c.residueMap col x *
            ⅟(vertexBetaMatrix c.residueMap row col)) () i) *
        endpointProfile (fun i => col i - y)
          (fun i => (⅟(vertexBetaMatrix c.residueMap row col) *
            vertexIncoming c.residueMap row y) i ())).coeff (x - y - (c.top : ℤ)) := by
  let δ₀ := residueChartDeriv c.top j
  let dhom : OtherField c.top →+ OtherField c.top := δ₀.toLinearMap.toAddMonoidHom
  have hadd (f g : OtherField c.top) : δ₀ (f + g) = δ₀ f + δ₀ g := δ₀.map_add f g
  have hone : δ₀ 1 = 0 := δ₀.map_one_eq_zero
  have hmul (f g : OtherField c.top) : δ₀ (f * g) = f * δ₀ g + g * δ₀ f := by
    simpa only [smul_eq_mul] using δ₀.leibniz f g
  let : Module ℚ (OtherField c.top) :=
    (DivisionRing.toRatAlgebra : Algebra ℚ (OtherField c.top)).toModule
  let δ : Derivation ℚ (OtherField c.top) (OtherField c.top) :=
    { toFun := δ₀
      map_add' := hadd
      map_smul' := map_rat_smul dhom
      map_one_eq_zero' := hone
      leibniz' := by intro f g; exact hmul f g }
  refine (retainedResponse_endpointVariation δ c.residueMap row col x y).trans ?_
  have hd : (fun z => δ (c.residueMap (hh z))) =
      (fun z => if z = (j : ℤ) then (1 : OtherField c.top) else 0) -
      (c.normalCoefficient⁻¹ * c.residueMap (pderiv j (cellSchur D hD.1))) •
        (fun z => if z = (c.top : ℤ) then (1 : OtherField c.top) else 0) := by
    funext z
    exact c.residue_hh_chart_derivative j z
  rw [hd, map_sub, map_smul, endpointVariation_indicator, endpointVariation_indicator,
    smul_eq_mul]

/-- The complete actual local response has the full raw/chart endpoint correction. -/
theorem originalLocalResponse_residue_chart_profile_gradient {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (j : ℕ+) :
    residueChartDeriv c.top j (c.regularResidue (c.originalLocalResponse P b d)) =
      ((c.originalResidueLeftEndpointPolynomial P b d *
        c.originalResidueRightEndpointPolynomial P b d).toLaurent).coeff
          (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
            P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (j : ℤ)) -
      (c.normalCoefficient⁻¹ * c.residueMap (pderiv j (cellSchur D hD.1))) *
      ((c.originalResidueLeftEndpointPolynomial P b d *
        c.originalResidueRightEndpointPolynomial P b d).toLaurent).coeff
          (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
            P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (c.top : ℤ)) := by
  let := c.originalResponseResidueIntervalInverse P b d
  let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
  have hL : endpointProfile (fun i => x - row i)
      (fun i => (vertexOutgoing c.residueMap col x * ⅟(vertexBetaMatrix c.residueMap row col))
        () i) = (c.originalResidueLeftEndpointPolynomial P b d).toLaurent := by
    apply endpointProfile_eq_toLaurent_of_nonneg
    intro i
    have hrow : row i < x := originalResponse_row_lt P b i.1.1 i.2
    omega
  have hR : endpointProfile (fun i => col i - y)
      (fun i => (⅟(vertexBetaMatrix c.residueMap row col) * vertexIncoming c.residueMap row y)
        i ()) = (c.originalResidueRightEndpointPolynomial P b d).toLaurent := by
    apply endpointProfile_eq_toLaurent_of_nonneg
    intro i
    have hcol : y < col i := originalResponse_col_gt P d i.1.1 i.1.2
    omega
  rw [c.originalLocalResponse_residue_pruned]
  have h := c.residue_interval_chart_profile_gradient row col x y j
  rw [hL, hR, ← map_mul] at h
  exact h

private theorem chart_profile_coeff_toLaurent {R : Type*} [CommRing R]
    (p : Polynomial R) (k : ℕ) : p.toLaurent.coeff (k : ℤ) = p.coeff k := by
  change (Finsupp.mapDomain (fun z : ℕ => (z : ℤ)) p.toFinsupp.coeff) (k : ℤ) = _
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k

/-- Full self-profile correction at every original generator, including the selected
one. The first normal jet is produced from the complete response, not supplied as
a separate slope or replaced by a proper selected-core response. -/
theorem originalLocalResponse_raw_chart_first_jet {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (j : ℕ+) (k l : ℕ)
    (hk : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (j : ℤ) = (k : ℤ))
    (hl : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (c.top : ℤ) = (l : ℤ)) :
    (c.originalResidueLeftEndpointPolynomial P b d *
      c.originalResidueRightEndpointPolynomial P b d).coeff k =
    residueChartDeriv c.top j (c.regularResidue (c.originalLocalResponse P b d)) +
      c.residueMap (pderiv j (cellSchur D hD.1)) *
        PowerSeries.coeff 1 (c.normalSeries (c.originalLocalResponse P b d)) := by
  have h := c.originalLocalResponse_residue_chart_profile_gradient P b d j
  rw [hk, hl, chart_profile_coeff_toLaurent, chart_profile_coeff_toLaurent,
    ← c.originalLocalResponse_first_jet_profile P b d l hl] at h
  have hc : (c.normalCoefficient⁻¹ * c.residueMap (pderiv j (cellSchur D hD.1))) *
      (c.normalCoefficient * PowerSeries.coeff 1
        (c.normalSeries (c.originalLocalResponse P b d))) =
      c.residueMap (pderiv j (cellSchur D hD.1)) *
        PowerSeries.coeff 1 (c.normalSeries (c.originalLocalResponse P b d)) := by
    field_simp [c.normalCoefficient_ne_zero]
  rw [hc] at h
  linear_combination -h

end SkewCornerDescent.Matrix.SelectedCoordinate
