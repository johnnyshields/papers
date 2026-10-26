/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalSeriesEndpointGradient
import SkewCornerDescent.Matrix.OriginalNormalSelectedCores

/-!
# Complete actual normal response gradients from original endpoint polynomials

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The actual complete response, interval inverse and positive endpoint distances
supply the full polynomial-product gradient. Its low selected-core window is
constant at every normal order, with no frozen-unit or supplied gradient premise.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every actual complete normal response has its original full endpoint-product gradient.
The source supplies the complete interval inverse and both natural-exponent bridges. -/
theorem originalLocalResponse_normal_profile_gradient {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (H : ℕ+) (hH : c.top < H) :
    residueSeriesGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
        (c.normalSeries (c.originalLocalResponse P b d)) =
      ((c.originalNormalLeftEndpointPolynomial P b d *
        c.originalNormalRightEndpointPolynomial P b d).toLaurent).coeff
          (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
            P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (H : ℤ)) := by
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
  have h := c.normal_interval_profile_gradient row col x y H hH
  rw [hl, hr, ← map_mul] at h
  rw [c.originalLocalResponse_normal_pruned]
  simpa only [Matrix.invOf_eq_nonsing_inv] using h

private theorem coeff_toLaurent_nat {R : Type*} [CommRing R] (p : Polynomial R) (k : ℕ) :
    p.toLaurent.coeff (k : ℤ) = p.coeff k := by
  change (Finsupp.mapDomain (fun x : ℕ => (x : ℤ)) p.toFinsupp.coeff) (k : ℤ) = _
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k

/-- At a low endpoint offset, the complete higher-generator gradient of the actual response
is its own proper-core product as a constant normal series. All normal orders are covered. -/
theorem originalLocalResponse_normal_low_core_gradient {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (horder : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (H : ℕ+) (hH : c.top < H) (k : ℕ) (hk : k ≤ (c.top : ℕ))
    (hdegree : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) - (H : ℤ) = (k : ℤ)) :
    residueSeriesGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
        (c.normalSeries (c.originalLocalResponse P (some b) (some d))) =
      PowerSeries.C ((c.selectedCoreLeftPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm *
        c.selectedCoreRightPolynomial
        (interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property))
        (originalSelectedProfile_schur P d).symm).coeff k) := by
  rw [c.originalLocalResponse_normal_profile_gradient P (some b) (some d) H hH,
    hdegree, coeff_toLaurent_nat,
    c.original_normal_profile_product_low_cores P b d horder k hk]

/-- Every positive normal jet of the low higher-generator gradient vanishes; the zeroth
jet is the actual complete cross-core product, not an assumed common gradient. -/
theorem originalLocalResponse_normal_low_core_jets {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (horder : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (H : ℕ+) (hH : c.top < H) (k : ℕ) (hk : k ≤ (c.top : ℕ))
    (hdegree : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) - (H : ℤ) = (k : ℤ))
    (m : ℕ) :
    residueGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (PowerSeries.coeff m (c.normalSeries (c.originalLocalResponse P (some b) (some d)))) =
      if m = 0 then (c.selectedCoreLeftPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm *
        c.selectedCoreRightPolynomial
        (interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property))
        (originalSelectedProfile_schur P d).symm).coeff k else 0 := by
  rw [← residueSeriesGeneratorDeriv_coeff,
    c.originalLocalResponse_normal_low_core_gradient P b d horder H hH k hk hdegree,
    PowerSeries.coeff_C]

private theorem coeff_toLaurent_negative {R : Type*} [CommRing R] (p : Polynomial R)
    (w : ℤ) (hw : w < 0) : p.toLaurent.coeff w = 0 := by
  apply Finsupp.notMem_support_iff.mp
  rw [LaurentPolynomial.support_coeff_toLaurent]
  intro h
  obtain ⟨n, _, he⟩ := Finset.mem_map.mp h
  change (n : ℤ) = w at he
  omega

/-- A higher generator beyond the actual endpoint span has zero derivative at every
normal order. Ordinary source profiles, not a frozen denominator, supply the exclusion. -/
theorem originalLocalResponse_normal_gradient_above_span {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (H : ℕ+) (hH : c.top < H)
    (hspan : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) < (H : ℤ)) :
    residueSeriesGeneratorDeriv c.top ⟨H, ne_of_gt hH⟩
      (c.normalSeries (c.originalLocalResponse P b d)) = 0 := by
  rw [c.originalLocalResponse_normal_profile_gradient P b d H hH]
  apply coeff_toLaurent_negative
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
