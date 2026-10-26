/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVisibleProfileCoefficients

/-!
# Nonzero full profile coefficients expose original positions

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Every nonzero positive coefficient has a genuine original retained row or
column at its exact integer distance. No nonvanishing of unrelated inverse
entries or profile coefficients is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

private theorem ordinary_profile_nonzero_position {F ι : Type*} [CommRing F] [Fintype ι]
    (distance : ι → ℕ) (v : ι → F) (k : ℕ) (hk : k ≠ 0)
    (hc : (ordinaryEndpointProfile distance v).coeff k ≠ 0) : ∃ i, distance i = k := by
  classical
  by_contra hn
  have hd (i) : distance i ≠ k := fun he => hn ⟨i, he⟩
  have hz : (ordinaryEndpointProfile distance v).coeff k = 0 := by
    simp only [ordinaryEndpointProfile, Polynomial.coeff_sub, Polynomial.coeff_one,
      ite_eq_right hk, Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    have hs : (∑ i, if distance i = k then v i else 0) = 0 :=
      Finset.sum_eq_zero (fun i _ => ite_eq_right (hd i))
    rw [hs, sub_self]
  exact hc hz

namespace SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every nonzero positive coefficient of the full actual incoming profile has
an original retained row at that exact integer distance. No global nonvanishing
of the other profile coefficients is needed. -/
theorem original_left_profile_nonzero_position {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℕ) (hk : k ≠ 0)
    (hc : (c.originalResidueLeftEndpointPolynomial P b d).coeff k ≠ 0) :
    ∃ i : OriginalResponseInterval (hD := hD) P b d,
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
        originalResponseRows P i.1.1 = (k : ℤ) := by
  let ν := OriginalResponseInterval (hD := hD) P b d
  let := c.originalResponseResidueIntervalInverse P b d
  let row := fun i : ν => originalResponseRows P i.1.1
  let col := fun i : ν => originalResponseCols P i.1.1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
  change (ordinaryEndpointProfile (fun i : ν => (x - row i).toNat)
    (fun i => (vertexOutgoing c.residueMap col x * ⅟(vertexBetaMatrix c.residueMap row col))
      () i)).coeff k ≠ 0 at hc
  obtain ⟨i, hi⟩ := ordinary_profile_nonzero_position _ _ k hk hc
  refine ⟨i, ?_⟩
  have hp : 0 < x - row i := by
    have h := originalResponse_row_lt P b i.1.1 i.2
    change row i < x at h
    omega
  have he := congrArg (fun t : ℕ => (t : ℤ)) hi
  rwa [Int.toNat_of_nonneg hp.le] at he

/-- Every nonzero positive outgoing coefficient similarly exposes one complete
actual retained column, with natural and integer offsets identified exactly. -/
theorem original_right_profile_nonzero_position {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (k : ℕ) (hk : k ≠ 0)
    (hc : (c.originalResidueRightEndpointPolynomial P b d).coeff k ≠ 0) :
    ∃ i : OriginalResponseInterval (hD := hD) P b d,
      originalResponseCols P i.1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (k : ℤ) := by
  let ν := OriginalResponseInterval (hD := hD) P b d
  let := c.originalResponseResidueIntervalInverse P b d
  let row := fun i : ν => originalResponseRows P i.1.1
  let col := fun i : ν => originalResponseCols P i.1.1
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
  change (ordinaryEndpointProfile (fun i : ν => (col i - y).toNat)
    (fun i => (⅟(vertexBetaMatrix c.residueMap row col) * vertexIncoming c.residueMap row y)
      i ())).coeff k ≠ 0 at hc
  obtain ⟨i, hi⟩ := ordinary_profile_nonzero_position _ _ k hk hc
  refine ⟨i, ?_⟩
  have hp : 0 < col i - y := by
    have h := originalResponse_col_gt P d i.1.1 i.1.2
    change y < col i at h
    omega
  have he := congrArg (fun t : ℕ => (t : ℤ)) hi
  rwa [Int.toNat_of_nonneg hp.le] at he

end SelectedCoordinate
end SkewCornerDescent.Matrix
