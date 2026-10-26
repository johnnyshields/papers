/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalHessianProjection
import SkewCornerDescent.Matrix.ProfileProjectionBlocks

/-!
# Original source inverse projections retain full individual components

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The source supplies triangular inverse support, strict separation of complete
original components and nonnegative endpoint-profile offsets. Cross-component
terms vanish; every within-component inverse entry remains. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every ordinary polynomial pair of weights contracts only within actual
original blocks. Triangular inverse support and strict endpoint separation are
produced from the unchanged source, not supplied as extra hypotheses. -/
theorem original_interval_inverse_projection_same_blocks {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (z : ℤ)
    (A T : LaurentPolynomial (OtherField c.top))
    (hA : ∀ k, k < 0 → A.coeff k = 0) (hT : ∀ k, k < 0 → T.coeff k = 0) :
    letI := c.originalResponseResidueIntervalInverse P b d
    let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
    let I := ⅟(vertexBetaMatrix c.residueMap row col)
    profileInverseProjection row col I A T z =
      ∑ i, ∑ j, if interiorBlock P i.1.1.1.val = interiorBlock P j.1.1.1.val then
        A.coeff (z - col i) * I i j * T.coeff (row j - z) else 0 := by
  let := c.originalResponseResidueIntervalInverse P b d
  let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
  let M := vertexBetaMatrix c.residueMap row col
  let label := fun i : OriginalResponseInterval (hD := hD) P b d =>
    interiorBlock P i.1.1.1.val
  have hM : M.BlockTriangular label := by
    intro i j hij
    apply c.originalResponse_residue_blockTriangular P
    dsimp only [label] at hij
    dsimp only
    exact_mod_cast hij
  have hI : (⅟M).BlockTriangular label := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hM
  have hsep (i j : OriginalResponseInterval (hD := hD) P b d)
      (hij : label i < label j) : row j < col i := by
    exact interior_block_endpoint_separation P
      (originalRemovedRow (hD := hD) P j.1.1.1 j.1.1.2)
      (originalRemovedCol (hD := hD) P i.1.1.1 i.1.1.2)
      (by rw [originalRemovedRow_block, originalRemovedCol_block]; exact hij)
  dsimp only
  exact profile_inverse_projection_same_blocks row col (⅟M) label hI hsep A T hA hT z

/-- The full original interval inverse projection has only same-component
contractions, with every internal inverse entry retained. Its support and
separation premises are produced from the actual original source. -/
theorem original_interval_projection_same_blocks {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (z : ℤ) :
    letI := c.originalResponseResidueIntervalInverse P b d
    let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
    let I := ⅟(vertexBetaMatrix c.residueMap row col)
    let B := vertexOutgoing c.residueMap col x
    let C := vertexIncoming c.residueMap row y
    let A := endpointProfile (fun i => x - row i) (fun i => (B * I) () i)
    let T := endpointProfile (fun i => col i - y) (fun i => (I * C) i ())
    profileInverseProjection row col I A T z =
      ∑ i, ∑ j, if interiorBlock P i.1.1.1.val = interiorBlock P j.1.1.1.val then
        A.coeff (z - col i) * I i j * T.coeff (row j - z) else 0 := by
  let := c.originalResponseResidueIntervalInverse P b d
  let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
  dsimp only
  apply c.original_interval_inverse_projection_same_blocks P b d z
  · intro k hk
    apply endpointProfile_coeff_negative _ _ _ k hk
    intro i
    have h := originalResponse_row_lt P b i.1.1 i.2
    change row i < P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) at h
    exact sub_nonneg.mpr h.le
  · intro k hk
    apply endpointProfile_coeff_negative _ _ _ k hk
    intro i
    have h := originalResponse_col_gt P d i.1.1 i.1.2
    change P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) < col i at h
    exact sub_nonneg.mpr h.le

end SkewCornerDescent.Matrix.SelectedCoordinate
