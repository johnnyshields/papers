/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueEndpointProfiles

/-!
# Actual endpoint profile coefficients expose their complete inverse values

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Original source partitions and strict beta lists make endpoint exponents distinct.
Each positive endpoint coefficient is therefore the negative full inverse value
at its actual source row or column, not a sum over an assumed matching inventory.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- Distinct positive distances expose exactly one full endpoint coefficient. -/
theorem ordinary_profile_coeff_at_index {R ι : Type*} [CommRing R] [Fintype ι]
    (d : ι → ℕ) (v : ι → R) (hd : Function.Injective d) (i : ι) (hi : d i ≠ 0) :
    (ordinaryEndpointProfile d v).coeff (d i) = -v i := by
  classical
  simp only [ordinaryEndpointProfile, Polynomial.coeff_sub, Polynomial.coeff_one,
    ite_eq_right hi, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
  have hs : (∑ j, if d j = d i then v j else 0) = v i := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      rw [ite_eq_right (fun he => hji (hd he))]
    · intro hnot
      exact (hnot (Finset.mem_univ i)).elim
  rw [hs, zero_sub]

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual surviving row list is injective by the complete original row partition. -/
theorem original_response_rows_injective {n : ℕ} (P : Profile n) :
    Function.Injective (originalResponseRows (hD := hD) P) := by
  intro i j he
  have hidx : originalRowSplitEquiv (hD := hD) P (.inr i) =
      originalRowSplitEquiv (hD := hD) P (.inr j) := by
    apply P.xi_strictAnti.injective
    rw [originalRowSplitEquiv_removed, originalRowSplitEquiv_removed]
    exact he
  exact Sum.inr.inj ((originalRowSplitEquiv (hD := hD) P).injective hidx)

/-- The entire surviving column list is injective by its own original column partition. -/
theorem original_response_cols_injective {n : ℕ} (P : Profile n) :
    Function.Injective (originalResponseCols (hD := hD) P) := by
  intro i j he
  have hidx : originalColSplitEquiv (hD := hD) P (.inr i) =
      originalColSplitEquiv (hD := hD) P (.inr j) := by
    apply P.zeta_strictAnti.injective
    rw [originalColSplitEquiv_removed, originalColSplitEquiv_removed]
    exact he
  exact Sum.inr.inj ((originalColSplitEquiv (hD := hD) P).injective hidx)

/-- Every actual incoming profile position exposes its unique complete interval inverse value.
The positive distance and its injectivity are produced from the original source. -/
theorem original_left_profile_coeff_at_row {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (i : OriginalResponseInterval (hD := hD) P b d) :
    let row := fun j : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P j.1.1
    let col := fun j : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P j.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
    (c.originalResidueLeftEndpointPolynomial P b d).coeff (x - row i).toNat =
      -(vertexOutgoing c.residueMap col x * (vertexBetaMatrix c.residueMap row col)⁻¹) () i := by
  classical
  let := c.originalResponseResidueIntervalInverse P b d
  let row := fun j : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P j.1.1
  let col := fun j : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P j.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
  have hpos (j : OriginalResponseInterval (hD := hD) P b d) : 0 < x - row j := by
    have h := originalResponse_row_lt P b j.1.1 j.2
    change row j < x at h
    omega
  have hinj : Function.Injective (fun j : OriginalResponseInterval (hD := hD) P b d =>
      (x - row j).toNat) := by
    intro j k he
    have h := congrArg (fun t : ℕ => (t : ℤ)) he
    rw [Int.toNat_of_nonneg (hpos j).le, Int.toNat_of_nonneg (hpos k).le] at h
    have hr : row j = row k := by omega
    have hv := original_response_rows_injective (hD := hD) P hr
    exact Subtype.ext (Subtype.ext hv)
  have h := ordinary_profile_coeff_at_index
    (fun j : OriginalResponseInterval (hD := hD) P b d => (x - row j).toNat)
    (fun j => (vertexOutgoing c.residueMap col x *
      (vertexBetaMatrix c.residueMap row col)⁻¹) () j) hinj i (by have := hpos i; omega)
  simpa only [originalResidueLeftEndpointPolynomial, residueIntervalLeftPolynomial,
    Matrix.invOf_eq_nonsing_inv] using h

/-- The dual actual outgoing profile position exposes its unique full inverse value. -/
theorem original_right_profile_coeff_at_col {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (i : OriginalResponseInterval (hD := hD) P b d) :
    let row := fun j : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P j.1.1
    let col := fun j : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P j.1.1
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
    (c.originalResidueRightEndpointPolynomial P b d).coeff (col i - y).toNat =
      -((vertexBetaMatrix c.residueMap row col)⁻¹ * vertexIncoming c.residueMap row y) i () := by
  classical
  let := c.originalResponseResidueIntervalInverse P b d
  let row := fun j : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P j.1.1
  let col := fun j : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P j.1.1
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
  have hpos (j : OriginalResponseInterval (hD := hD) P b d) : 0 < col j - y := by
    have h := originalResponse_col_gt P d j.1.1 j.1.2
    change y < col j at h
    omega
  have hinj : Function.Injective (fun j : OriginalResponseInterval (hD := hD) P b d =>
      (col j - y).toNat) := by
    intro j k he
    have h := congrArg (fun t : ℕ => (t : ℤ)) he
    rw [Int.toNat_of_nonneg (hpos j).le, Int.toNat_of_nonneg (hpos k).le] at h
    have hc : col j = col k := by omega
    have hv := original_response_cols_injective (hD := hD) P hc
    exact Subtype.ext (Subtype.ext hv)
  have h := ordinary_profile_coeff_at_index
    (fun j : OriginalResponseInterval (hD := hD) P b d => (col j - y).toNat)
    (fun j => ((vertexBetaMatrix c.residueMap row col)⁻¹ *
      vertexIncoming c.residueMap row y) j ()) hinj i (by have := hpos i; omega)
  simpa only [originalResidueRightEndpointPolynomial, residueIntervalRightPolynomial,
    Matrix.invOf_eq_nonsing_inv] using h

end SelectedCoordinate
end SkewCornerDescent.Matrix
