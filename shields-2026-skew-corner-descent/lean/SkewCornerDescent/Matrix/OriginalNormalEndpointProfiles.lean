/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.BetaEndpointPolynomial
import SkewCornerDescent.Matrix.OriginalResidueLowStrips
import SkewCornerDescent.Matrix.SelectedCoreNormalProfiles

/-!
# Complete original endpoint polynomials in the normal-series ring

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The complete actual removed-matrix inverse is transported through the genuine
normal chart. Original block order produces every interval and endpoint-strip
inverse without discarding any nonselected normal jets. Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The whole actual normal removed matrix receives its inverse from the actual local ring. -/
@[instance_reducible]
def originalNormalRemovedInverse {n : ℕ} (P : Profile n) :
    Invertible (vertexBetaMatrix c.normalPolynomialSeries
      (originalResponseRows (hD := hD) P) (originalResponseCols (hD := hD) P)) := by
  let M := (originalRemovedMatrix (hD := hD) P).map (algebraMap Lambda c.RegularRing)
  let : Invertible M := c.originalRemovedLocalInverse P
  let inv := Invertible.map c.normalSeries.mapMatrix M
  have he : vertexBetaMatrix c.normalPolynomialSeries
      (originalResponseRows (hD := hD) P) (originalResponseCols (hD := hD) P) =
      c.normalSeries.mapMatrix M := by
    ext i j : 1
    exact (c.normalSeries_polynomial _).symm
  exact he.symm ▸ inv

/-- The complete original normal matrix has the same source-produced block order. -/
theorem originalResponse_normal_blockTriangular {n : ℕ} (P : Profile n) :
    (vertexBetaMatrix c.normalPolynomialSeries
      (originalResponseRows (hD := hD) P) (originalResponseCols (hD := hD) P)).BlockTriangular
      (fun i => (interiorBlock P i.1.val : ℤ)) := by
  intro i j hij
  change (interiorBlock P j.1.val : ℤ) < (interiorBlock P i.1.val : ℤ) at hij
  change c.normalPolynomialSeries (originalRemovedMatrix (hD := hD) P i j) = 0
  rw [originalRemovedMatrix_blockTriangular P (by
    change interiorBlock P j.1.val < interiorBlock P i.1.val
    exact_mod_cast hij), map_zero]

/-- The actual complete normal interval has a produced inverse, including every unit block. -/
@[instance_reducible]
def originalResponseNormalIntervalInverse {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    Invertible (vertexBetaMatrix c.normalPolynomialSeries
      (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1)) := by
  let := c.originalNormalRemovedInverse P
  exact orderedIntervalInverse _ _ (c.originalResponse_normal_blockTriangular P) _ _

/-- Original interval order remains triangular in the complete normal series. -/
theorem originalResponseInterval_normal_blockTriangular {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    (vertexBetaMatrix c.normalPolynomialSeries
      (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
      (fun i => originalResponseCols P i.1.1)).BlockTriangular
      (fun i => (interiorBlock P i.1.1.1.val : ℤ)) :=
  (c.originalResponse_normal_blockTriangular P).submatrix.submatrix

/-- Full original incoming polynomial, with complete normal-series inverse coefficients. -/
def originalNormalLeftEndpointPolynomial {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    Polynomial (PowerSeries (OtherField c.top)) :=
  betaEndpointLeftPolynomial c.normalPolynomialSeries
    (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
    (fun i => originalResponseCols P i.1.1)
    (P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)))

/-- Full original outgoing polynomial, with the same complete normal inverse. -/
def originalNormalRightEndpointPolynomial {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    Polynomial (PowerSeries (OtherField c.top)) :=
  betaEndpointRightPolynomial c.normalPolynomialSeries
    (fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1)
    (fun i => originalResponseCols P i.1.1)
    (P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)))

/-- Genuine complete normal inverse of the first original selected strip. -/
@[instance_reducible]
def originalLeftStripNormalInverse {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    Invertible (vertexBetaMatrix c.normalPolynomialSeries
      (fun i : OriginalLeftStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
      (fun i => originalResponseCols P i.1.1.1)) := by
  let := c.originalResponseNormalIntervalInverse P (some b) d
  exact (c.originalResponseInterval_normal_blockTriangular P (some b) d).invertibleToBlock _

/-- Genuine complete normal inverse of the last original selected strip. -/
@[instance_reducible]
def originalRightStripNormalInverse {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P) :
    Invertible (vertexBetaMatrix c.normalPolynomialSeries
      (fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
      (fun i => originalResponseCols P i.1.1.1)) := by
  let := c.originalResponseNormalIntervalInverse P b (some d)
  have ht := c.originalResponseInterval_normal_blockTriangular P b (some d)
  let inv := ht.transpose.invertibleToBlock
    (OrderDual.toDual ((interiorBlock P d.val.val : ℤ) - 1))
  change Invertible (Matrix.transpose (vertexBetaMatrix c.normalPolynomialSeries
    (fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
    (fun i => originalResponseCols P i.1.1.1))) at inv
  let := inv
  exact Matrix.invertibleOfInvertibleTranspose _

/-- Complete normal incoming polynomial of the actual first selected boundary strip. -/
def originalNormalLeftStripPolynomial {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    Polynomial (PowerSeries (OtherField c.top)) :=
  betaEndpointLeftPolynomial c.normalPolynomialSeries
    (fun i : OriginalLeftStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
    (fun i => originalResponseCols P i.1.1.1)
    (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))))

/-- Complete normal outgoing polynomial of the actual last selected boundary strip. -/
def originalNormalRightStripPolynomial {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P) :
    Polynomial (PowerSeries (OtherField c.top)) :=
  betaEndpointRightPolynomial c.normalPolynomialSeries
    (fun i : OriginalRightStripIndex (hD := hD) P b d => originalResponseRows P i.1.1.1)
    (fun i => originalResponseCols P i.1.1.1)
    (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))))

end SkewCornerDescent.Matrix.SelectedCoordinate
