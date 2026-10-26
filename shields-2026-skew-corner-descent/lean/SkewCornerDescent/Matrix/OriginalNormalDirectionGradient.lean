/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalDirectionEndpointGradient
import SkewCornerDescent.Matrix.OriginalNormalProfileGradient
import SkewCornerDescent.Matrix.BetaEndpointNaturality

/-!
# Actual normal-direction derivatives and complete residue endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The first normal jet uses the actual complete inverse and its derivative.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The genuine normal-direction derivative of the complete original response. -/
theorem originalLocalResponse_normal_direction_gradient {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    PowerSeries.C c.normalCoefficient * PowerSeries.derivative (R := OtherField c.top)
        (c.normalSeries (c.originalLocalResponse P b d)) =
      ((c.originalNormalLeftEndpointPolynomial P b d *
        c.originalNormalRightEndpointPolynomial P b d).toLaurent).coeff
          (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
            P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (c.top : ℤ)) := by
  classical
  let := c.originalResponseNormalIntervalInverse P b d
  let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
  have hl : endpointProfile (fun i => x - row i)
      (fun i => (vertexOutgoing c.normalPolynomialSeries col x *
        ⅟(vertexBetaMatrix c.normalPolynomialSeries row col)) () i) =
      (c.originalNormalLeftEndpointPolynomial P b d).toLaurent := by
    have h := endpointProfile_eq_toLaurent_of_nonneg (fun i => x - row i)
      (fun i => (vertexOutgoing c.normalPolynomialSeries col x *
        ⅟(vertexBetaMatrix c.normalPolynomialSeries row col)) () i)
      (fun i => by
        have h := originalResponse_row_lt P b i.1.1 i.2
        change row i < x at h
        omega)
    simpa only [originalNormalLeftEndpointPolynomial, betaEndpointLeftPolynomial,
      Matrix.invOf_eq_nonsing_inv] using h
  have hr : endpointProfile (fun i => col i - y)
      (fun i => (⅟(vertexBetaMatrix c.normalPolynomialSeries row col) *
        vertexIncoming c.normalPolynomialSeries row y) i ()) =
      (c.originalNormalRightEndpointPolynomial P b d).toLaurent := by
    have h := endpointProfile_eq_toLaurent_of_nonneg (fun i => col i - y)
      (fun i => (⅟(vertexBetaMatrix c.normalPolynomialSeries row col) *
        vertexIncoming c.normalPolynomialSeries row y) i ())
      (fun i => by
        have h := originalResponse_col_gt P d i.1.1 i.1.2
        change y < col i at h
        omega)
    simpa only [originalNormalRightEndpointPolynomial, betaEndpointRightPolynomial,
      Matrix.invOf_eq_nonsing_inv] using h
  have h := c.normal_interval_profile_normal_gradient row col x y
  rw [hl, hr, ← map_mul] at h
  rw [c.originalLocalResponse_normal_pruned]
  simpa only [Matrix.invOf_eq_nonsing_inv] using h

/-- The constant normal coefficient transports the complete incoming inverse profile. -/
theorem originalNormalLeftEndpointPolynomial_residue {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    (c.originalNormalLeftEndpointPolynomial P b d).map PowerSeries.constantCoeff =
      c.originalResidueLeftEndpointPolynomial P b d := by
  let := c.originalResponseNormalIntervalInverse P b d
  have he : PowerSeries.constantCoeff.comp c.normalPolynomialSeries = c.residueMap := by
    apply RingHom.ext
    intro f
    exact c.normalPolynomialSeries_constant f
  have h := betaEndpointLeftPolynomial_map c.normalPolynomialSeries PowerSeries.constantCoeff
    (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
    (fun i => originalResponseCols P i.1.1)
    (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)))
  rw [he] at h
  simpa only [originalNormalLeftEndpointPolynomial, originalResidueLeftEndpointPolynomial,
    residueIntervalLeftPolynomial, betaEndpointLeftPolynomial,
    Matrix.invOf_eq_nonsing_inv] using h

/-- The same projection transports the complete outgoing inverse profile. -/
theorem originalNormalRightEndpointPolynomial_residue {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    (c.originalNormalRightEndpointPolynomial P b d).map PowerSeries.constantCoeff =
      c.originalResidueRightEndpointPolynomial P b d := by
  let := c.originalResponseNormalIntervalInverse P b d
  have he : PowerSeries.constantCoeff.comp c.normalPolynomialSeries = c.residueMap := by
    apply RingHom.ext
    intro f
    exact c.normalPolynomialSeries_constant f
  have h := betaEndpointRightPolynomial_map c.normalPolynomialSeries PowerSeries.constantCoeff
    (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
    (fun i => originalResponseCols P i.1.1)
    (P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)))
  rw [he] at h
  simpa only [originalNormalRightEndpointPolynomial, originalResidueRightEndpointPolynomial,
    residueIntervalRightPolynomial, betaEndpointRightPolynomial,
    Matrix.invOf_eq_nonsing_inv] using h

private theorem normal_direction_coeff_toLaurent {R : Type*} [CommRing R]
    (p : Polynomial R) (k : ℕ) : p.toLaurent.coeff (k : ℤ) = p.coeff k := by
  change (Finsupp.mapDomain (fun x : ℕ => (x : ℤ)) p.toFinsupp.coeff) (k : ℤ) = _
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k

/-- The first normal jet equals the selected-index coefficient of the full residue
profile product, divided by the genuine nonzero affine normal coefficient. -/
theorem originalLocalResponse_first_jet_profile {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℕ)
    (hk : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (c.top : ℤ) = (k : ℤ)) :
    c.normalCoefficient * PowerSeries.coeff 1 (c.normalSeries (c.originalLocalResponse P b d)) =
      (c.originalResidueLeftEndpointPolynomial P b d *
        c.originalResidueRightEndpointPolynomial P b d).coeff k := by
  have h := c.originalLocalResponse_normal_direction_gradient P b d
  rw [hk, normal_direction_coeff_toLaurent] at h
  have hz := congrArg (PowerSeries.constantCoeff (R := OtherField c.top)) h
  have hd (p : PowerSeries (OtherField c.top)) :
      PowerSeries.constantCoeff (PowerSeries.derivative p) = PowerSeries.coeff 1 p := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_derivative]
    simp
  simp only [map_mul, PowerSeries.constantCoeff_C, hd] at hz
  rw [← Polynomial.coeff_map, Polynomial.map_mul,
    c.originalNormalLeftEndpointPolynomial_residue,
    c.originalNormalRightEndpointPolynomial_residue] at hz
  exact hz

end SkewCornerDescent.Matrix.SelectedCoordinate
