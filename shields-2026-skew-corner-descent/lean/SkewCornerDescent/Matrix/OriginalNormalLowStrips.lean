/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalEndpointProfiles

/-!
# Complete all-normal-order low strip jets of original endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Actual block locality and strict endpoint distances identify the low endpoint
coefficients while retaining every full normal-series inverse and unit jet.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete incoming normal profile agrees with its actual selected strip
through selected-span endpoint degree, at every normal order. -/
theorem original_normal_left_profile_low_strip {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalNormalLeftEndpointPolynomial P (some b) d).coeff k =
      (c.originalNormalLeftStripPolynomial P b d).coeff k := by
  classical
  let := c.originalResponseNormalIntervalInverse P (some b) d
  let row := fun i : OriginalResponseInterval (hD := hD) P (some b) d =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P (some b) d =>
    originalResponseCols P i.1.1
  let M := vertexBetaMatrix c.normalPolynomialSeries row col
  let label := fun i : OriginalResponseInterval (hD := hD) P (some b) d =>
    (interiorBlock P i.1.1.1.val : ℤ)
  let cut := (interiorBlock P b.val.val : ℤ) + 1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
  have htri : M.BlockTriangular label :=
    c.originalResponseInterval_normal_blockTriangular P (some b) d
  have hweights (i : OriginalLeftStripIndex (hD := hD) P b d) :
      (vertexOutgoing c.normalPolynomialSeries col x * M⁻¹) () i.1 =
        (vertexOutgoing c.normalPolynomialSeries (fun j : OriginalLeftStripIndex (hD := hD) P b d =>
          col j.1) x * (vertexBetaMatrix c.normalPolynomialSeries
            (fun j : OriginalLeftStripIndex (hD := hD) P b d => row j.1)
            (fun j => col j.1))⁻¹) () i := by
    simp only [Matrix.mul_apply, vertexOutgoing, Matrix.of_apply]
    exact incoming_inverse_prefix (fun j => c.normalPolynomialSeries (hh (x - col j)))
      M label htri cut i.1 i.2
  have habsent (i : OriginalResponseInterval (hD := hD) P (some b) d)
      (hi : ¬label i < cut) : (x - row i).toNat ≠ k := by
    have hlt : interiorBlock P b.val.val < interiorBlock P i.1.1.1.val := by
      dsimp only [label, cut] at hi
      omega
    have h := c.original_row_distance_gt_top_of_later_block P b i.1.1 hlt
    change (c.top : ℤ) < x - row i at h
    exact ne_of_gt (hk.trans_lt (Int.lt_toNat.mpr h))
  simp only [originalNormalLeftEndpointPolynomial, originalNormalLeftStripPolynomial,
    betaEndpointLeftPolynomial, ordinaryEndpointProfile, Polynomial.coeff_sub,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply congrArg (fun z : PowerSeries (OtherField c.top) =>
    (1 : Polynomial (PowerSeries (OtherField c.top))).coeff k - z)
  apply Finset.sum_congr_set {i | label i < cut}
  · intro i hi
    split_ifs
    · exact hweights ⟨i, hi⟩
    · rfl
  · intro i hi
    exact ite_eq_right (habsent i hi)

/-- The complete outgoing normal profile agrees with its actual selected strip
through selected-span endpoint degree, at every normal order. -/
theorem original_normal_right_profile_low_strip {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P) (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalNormalRightEndpointPolynomial P b (some d)).coeff k =
      (c.originalNormalRightStripPolynomial P b d).coeff k := by
  classical
  let := c.originalResponseNormalIntervalInverse P b (some d)
  let row := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
    originalResponseCols P i.1.1
  let M := vertexBetaMatrix c.normalPolynomialSeries row col
  let label := fun i : OriginalResponseInterval (hD := hD) P b (some d) =>
    (interiorBlock P i.1.1.1.val : ℤ)
  let cut := (interiorBlock P d.val.val : ℤ) - 1
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  have htri : M.BlockTriangular label :=
    c.originalResponseInterval_normal_blockTriangular P b (some d)
  have hweights (i : OriginalRightStripIndex (hD := hD) P b d) :
      (M⁻¹ * vertexIncoming c.normalPolynomialSeries row y) i.1 () =
        ((vertexBetaMatrix c.normalPolynomialSeries
            (fun j : OriginalRightStripIndex (hD := hD) P b d => row j.1)
            (fun j => col j.1))⁻¹ *
          vertexIncoming c.normalPolynomialSeries
            (fun j : OriginalRightStripIndex (hD := hD) P b d => row j.1) y) i () := by
    simp only [Matrix.mul_apply, vertexIncoming, Matrix.of_apply]
    exact outgoing_inverse_suffix (fun j => c.normalPolynomialSeries (hh (row j - y)))
      M label htri cut i.1 i.2
  have habsent (i : OriginalResponseInterval (hD := hD) P b (some d))
      (hi : ¬cut < label i) : (col i - y).toNat ≠ k := by
    have hlt : interiorBlock P i.1.1.1.val < interiorBlock P d.val.val := by
      dsimp only [label, cut] at hi
      omega
    have h := c.original_col_distance_gt_top_of_earlier_block P d i.1.1 hlt
    change (c.top : ℤ) < col i - y at h
    exact ne_of_gt (hk.trans_lt (Int.lt_toNat.mpr h))
  simp only [originalNormalRightEndpointPolynomial, originalNormalRightStripPolynomial,
    betaEndpointRightPolynomial, ordinaryEndpointProfile, Polynomial.coeff_sub,
    Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  apply congrArg (fun z : PowerSeries (OtherField c.top) =>
    (1 : Polynomial (PowerSeries (OtherField c.top))).coeff k - z)
  apply Finset.sum_congr_set {i | cut < label i}
  · intro i hi
    split_ifs
    · exact hweights ⟨i, hi⟩
    · rfl
  · intro i hi
    exact ite_eq_right (habsent i hi)

end SkewCornerDescent.Matrix.SelectedCoordinate
