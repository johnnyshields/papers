/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalEndpointProfiles
import SkewCornerDescent.Matrix.OriginalResidueResponses
import SkewCornerDescent.Matrix.ResidueProfileDifference

/-!
# Complete original interval profiles on the selected residue chart

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). The
source's actual retained index interval supplies its complete residue inverse.
Both endpoint profiles use the original row and column parameters, with every
off-diagonal coupling preserved. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete original removed matrix is upper block triangular at residue. -/
theorem originalResponse_residue_blockTriangular {n : ℕ} (P : Profile n) :
    (vertexBetaMatrix c.residueMap (originalResponseRows (hD := hD) P)
      (originalResponseCols (hD := hD) P)).BlockTriangular
        (fun j => (interiorBlock P j.1.val : ℤ)) := by
  intro i j hij
  change (interiorBlock P j.1.val : ℤ) < (interiorBlock P i.1.val : ℤ) at hij
  exact (originalRemovedMatrix_blockTriangular (hD := hD) P).map c.residueMap
    (by exact_mod_cast hij)

/-- The full original residue inverse constructs the ordered interval inverse;
no invertibility assumption is added for the pruned interval. -/
@[instance_reducible]
noncomputable def originalResponseResidueIntervalInverse {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    Invertible (vertexBetaMatrix c.residueMap
      (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1)) := by
  let : Invertible (vertexBetaMatrix c.residueMap (originalResponseRows (hD := hD) P)
      (originalResponseCols (hD := hD) P)) := c.originalRemovedResidueInverse P
  exact orderedIntervalInverse _ _ (c.originalResponse_residue_blockTriangular P) _ _

/-- The actual original local residue response equals its complete ordered
interval response. Both exterior support cutoffs and the interval inverse are
produced from the source; no entries of the full inverse are deleted by value. -/
theorem originalLocalResponse_residue_pruned {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    letI := c.originalResponseResidueIntervalInverse P b d
    let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
    c.regularResidue (c.originalLocalResponse P b d) =
      c.residueMap (hh (x - y)) -
        (vertexOutgoing c.residueMap col x * ⅟(vertexBetaMatrix c.residueMap row col) *
          vertexIncoming c.residueMap row y) () () := by
  let : Invertible (vertexBetaMatrix c.residueMap (originalResponseRows (hD := hD) P)
      (originalResponseCols (hD := hD) P)) := c.originalRemovedResidueInverse P
  let := c.originalResponseResidueIntervalInverse P b d
  dsimp only
  rw [c.originalLocalResponse_residue_contraction, vertex_boundary_contraction_eq]
  congr 1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
  let row := originalResponseRows (hD := hD) P
  let col := originalResponseCols (hD := hD) P
  let M := vertexBetaMatrix c.residueMap row col
  let label := fun j : OriginalRemainingIndices (hD := hD) P => (interiorBlock P j.1.val : ℤ)
  let lo := originalResponseLowerCut P b
  let hi := originalResponseUpperCut P d
  have hr : (fun j : OriginalRemainingIndices (hD := hD) P =>
      c.residueMap ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j))) =
      fun j => c.residueMap (hh (x - col j)) := by
    funext j
    change c.residueMap (hh (x - P.zeta (originalColSplitEquiv (hD := hD) P (.inr j)))) = _
    rw [originalColSplitEquiv_removed]
    rfl
  have hs : (fun j : OriginalRemainingIndices (hD := hD) P =>
      c.residueMap ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d))) =
      fun j => c.residueMap (hh (row j - y)) := by
    funext j
    change c.residueMap (hh (P.xi (originalRowSplitEquiv (hD := hD) P (.inr j)) - y)) = _
    rw [originalRowSplitEquiv_removed]
    rfl
  rw [hr, hs]
  change inverseContraction (fun j => c.residueMap (hh (x - col j)))
    (fun j => c.residueMap (hh (row j - y))) M = _
  rw [inverseContraction_interval _ _ M label (c.originalResponse_residue_blockTriangular P) lo hi]
  · rfl
  · intro j hj
    have hcut : x < col j := originalResponse_incoming_cutoff P b j hj
    rw [hh_of_neg (by omega), map_zero]
  · intro j hj
    have hcut : row j < y := originalResponse_outgoing_cutoff P d j hj
    rw [hh_of_neg (by omega), map_zero]

/-- The ordinary incoming profile of an actual original retained interval. -/
noncomputable def originalResidueLeftEndpointPolynomial {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) : Polynomial (OtherField c.top) :=
  letI := c.originalResponseResidueIntervalInverse P b d
  c.residueIntervalLeftPolynomial
    (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
    (fun i => originalResponseCols P i.1.1)
    (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)))

/-- The ordinary outgoing profile, with the same complete original residue inverse. -/
noncomputable def originalResidueRightEndpointPolynomial {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) : Polynomial (OtherField c.top) :=
  letI := c.originalResponseResidueIntervalInverse P b d
  c.residueIntervalRightPolynomial
    (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
    (fun i => originalResponseCols P i.1.1)
    (P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)))

/-- Higher-generator differentiation of the complete actual local response is
the coefficient of its two produced ordinary endpoint profiles. The source
supplies all interval support and invertibility premises. -/
theorem originalLocalResponse_residue_profile_gradient {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (j : ℕ+) (hj : c.top < j) :
    residueGeneratorDeriv c.top ⟨j, ne_of_gt hj⟩
        (c.regularResidue (c.originalLocalResponse P b d)) =
      ((c.originalResidueLeftEndpointPolynomial P b d *
        c.originalResidueRightEndpointPolynomial P b d).toLaurent).coeff
          (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
            P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (j : ℤ)) := by
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
  have h := c.residue_interval_profile_gradient row col x y j hj
  rw [hL, hR, ← map_mul] at h
  exact h

/-- The actual incoming endpoint profile is normalized at degree zero. -/
theorem originalResidueLeftEndpointPolynomial_coeff_zero {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    (c.originalResidueLeftEndpointPolynomial P b d).coeff 0 = 1 := by
  let := c.originalResponseResidueIntervalInverse P b d
  have hd (i : OriginalResponseInterval (hD := hD) P b d) :
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
        originalResponseRows P i.1.1).toNat ≠ 0 := by
    have h := originalResponse_row_lt P b i.1.1 i.2
    change originalResponseRows P i.1.1 < _ at h
    omega
  simp [originalResidueLeftEndpointPolynomial, residueIntervalLeftPolynomial,
    ordinaryEndpointProfile, Polynomial.coeff_monomial, hd]

/-- The actual outgoing endpoint profile has the same normalization. -/
theorem originalResidueRightEndpointPolynomial_coeff_zero {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    (c.originalResidueRightEndpointPolynomial P b d).coeff 0 = 1 := by
  let := c.originalResponseResidueIntervalInverse P b d
  have hd (i : OriginalResponseInterval (hD := hD) P b d) :
      (originalResponseCols P i.1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))).toNat ≠ 0 := by
    have h := originalResponse_col_gt P d i.1.1 i.1.2
    change _ < originalResponseCols P i.1.1 at h
    omega
  simp [originalResidueRightEndpointPolynomial, residueIntervalRightPolynomial,
    ordinaryEndpointProfile, Polynomial.coeff_monomial, hd]

private theorem coeff_toLaurent_nat {F : Type*} [CommRing F] (p : Polynomial F) (k : ℕ) :
    p.toLaurent.coeff (k : ℤ) = p.coeff k := by
  change (Finsupp.mapDomain (fun x : ℕ => (x : ℤ)) p.toFinsupp.coeff) (k : ℤ) = _
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k

/-- The first endpoint differences of two equal actual original responses of
equal span are opposite. The complete source inverse supplies the profile
gradient; equality of the product is not an additional hypothesis. -/
theorem original_response_first_differences_opposite {n m : ℕ}
    (P : Profile n) (Q : Profile m)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (b' d' : Option (OriginalSelectedBlocks (hD := hD) Q))
    (hspan : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) =
      Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl b')) -
        Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl d')))
    (hresponse : c.regularResidue (c.originalLocalResponse P b d) =
      c.regularResidue (c.originalLocalResponse Q b' d'))
    (w : ℕ) (hw : (c.top : ℤ) <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) - (w : ℤ))
    (hleft : ∀ k < w, (c.originalResidueLeftEndpointPolynomial P b d).coeff k =
      (c.originalResidueLeftEndpointPolynomial Q b' d').coeff k)
    (hright : ∀ k < w, (c.originalResidueRightEndpointPolynomial P b d).coeff k =
      (c.originalResidueRightEndpointPolynomial Q b' d').coeff k) :
    (c.originalResidueLeftEndpointPolynomial P b d).coeff w -
        (c.originalResidueLeftEndpointPolynomial Q b' d').coeff w =
      -((c.originalResidueRightEndpointPolynomial P b d).coeff w -
        (c.originalResidueRightEndpointPolynomial Q b' d').coeff w) := by
  let K := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
  have hN := c.top.pos
  let j : ℕ+ := ⟨(K - (w : ℤ)).toNat, by dsimp only [K]; omega⟩
  have hj : (j : ℤ) = K - (w : ℤ) := Int.toNat_of_nonneg (by dsimp only [K]; omega)
  have hNj : c.top < j := by
    have he : ((c.top : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by
      rw [hj]
      exact hw
    exact_mod_cast he
  have hp := congrArg (residueGeneratorDeriv c.top ⟨j, ne_of_gt hNj⟩) hresponse
  rw [c.originalLocalResponse_residue_profile_gradient P b d j hNj,
    c.originalLocalResponse_residue_profile_gradient Q b' d' j hNj] at hp
  have hdegree : K - (j : ℤ) = (w : ℤ) := by omega
  change (_ : LaurentPolynomial (OtherField c.top)).coeff (K - (j : ℤ)) = _ at hp
  rw [hdegree, ← hspan, hdegree, coeff_toLaurent_nat, coeff_toLaurent_nat] at hp
  have h := SkewCornerDescent.first_profile_differences_opposite
    (c.originalResidueLeftEndpointPolynomial P b d : PowerSeries (OtherField c.top))
    (c.originalResidueRightEndpointPolynomial P b d)
    (c.originalResidueLeftEndpointPolynomial Q b' d')
    (c.originalResidueRightEndpointPolynomial Q b' d') w
    (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using
      c.originalResidueLeftEndpointPolynomial_coeff_zero P b d)
    (by simpa only [← PowerSeries.coeff_zero_eq_constantCoeff, Polynomial.coeff_coe] using
      c.originalResidueRightEndpointPolynomial_coeff_zero Q b' d')
    (by simpa only [Polynomial.coeff_coe] using hleft)
    (by simpa only [Polynomial.coeff_coe] using hright)
    (by simpa only [← Polynomial.coe_mul, Polynomial.coeff_coe] using hp)
  simpa only [map_sub, Polynomial.coeff_coe] using h

end SkewCornerDescent.Matrix.SelectedCoordinate
