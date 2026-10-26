/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalEndpointProfiles
import SkewCornerDescent.Matrix.ResidueSeriesGeneratorDerivation

/-!
# Complete original normal response contractions and endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The genuine local response maps with its entire normal-dependent removed inverse.
Actual ordered support restricts the complete contraction to its literal interval;
no inverse entry is deleted by value or replaced by its residue. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full original local response retains its complete actual normal inverse contraction. -/
theorem originalLocalResponse_normal_contraction {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    c.normalSeries (c.originalLocalResponse P b d) =
      c.normalPolynomialSeries ((originalSplitMatrix (hD := hD) P) (.inl b) (.inl d)) -
      inverseContraction
        (fun j => c.normalPolynomialSeries ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j)))
        (fun j => c.normalPolynomialSeries ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d)))
        ((originalRemovedMatrix (hD := hD) P).map c.normalPolynomialSeries) := by
  classical
  let := c.originalRemovedLocalInverse P
  rw [c.originalLocalResponse_entry, map_sub, c.normalSeries_polynomial]
  have hm : ((originalRemovedMatrix (hD := hD) P).map
      (algebraMap Lambda c.RegularRing)).map c.normalSeries =
      (originalRemovedMatrix (hD := hD) P).map c.normalPolynomialSeries := by
    ext i j : 1
    exact c.normalSeries_polynomial _
  rw [map_inverseContraction, hm]
  have hr : (c.normalSeries ∘ fun j : OriginalRemainingIndices (hD := hD) P =>
      algebraMap Lambda c.RegularRing
        ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j))) =
      fun j => c.normalPolynomialSeries ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j)) := by
    funext j
    exact c.normalSeries_polynomial _
  have hs : (c.normalSeries ∘ fun j : OriginalRemainingIndices (hD := hD) P =>
      algebraMap Lambda c.RegularRing
        ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d))) =
      fun j => c.normalPolynomialSeries ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d)) := by
    funext j
    exact c.normalSeries_polynomial _
  rw [hr, hs]

/-- The complete original normal response is exactly its actual ordered interval contraction.
The source supplies both support cutoffs and the full interval inverse. -/
theorem originalLocalResponse_normal_pruned {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) :
    let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
    c.normalSeries (c.originalLocalResponse P b d) =
      c.normalPolynomialSeries (hh (x - y)) -
        (vertexOutgoing c.normalPolynomialSeries col x *
          (vertexBetaMatrix c.normalPolynomialSeries row col)⁻¹ *
            vertexIncoming c.normalPolynomialSeries row y) () () := by
  classical
  let := c.originalNormalRemovedInverse P
  let := c.originalResponseNormalIntervalInverse P b d
  dsimp only
  rw [c.originalLocalResponse_normal_contraction, ← Matrix.invOf_eq_nonsing_inv,
    vertex_boundary_contraction_eq]
  congr 1
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
  let row := originalResponseRows (hD := hD) P
  let col := originalResponseCols (hD := hD) P
  let M := vertexBetaMatrix c.normalPolynomialSeries row col
  let label := fun j : OriginalRemainingIndices (hD := hD) P => (interiorBlock P j.1.val : ℤ)
  let lo := originalResponseLowerCut P b
  let hi := originalResponseUpperCut P d
  have hr : (fun j : OriginalRemainingIndices (hD := hD) P =>
      c.normalPolynomialSeries ((originalSplitMatrix (hD := hD) P) (.inl b) (.inr j))) =
      fun j => c.normalPolynomialSeries (hh (x - col j)) := by
    funext j
    change c.normalPolynomialSeries (hh (x - P.zeta (originalColSplitEquiv P (.inr j)))) = _
    rw [originalColSplitEquiv_removed]
    rfl
  have hs : (fun j : OriginalRemainingIndices (hD := hD) P =>
      c.normalPolynomialSeries ((originalSplitMatrix (hD := hD) P) (.inr j) (.inl d))) =
      fun j => c.normalPolynomialSeries (hh (row j - y)) := by
    funext j
    change c.normalPolynomialSeries (hh (P.xi (originalRowSplitEquiv P (.inr j)) - y)) = _
    rw [originalRowSplitEquiv_removed]
    rfl
  rw [hr, hs]
  change inverseContraction (fun j => c.normalPolynomialSeries (hh (x - col j)))
    (fun j => c.normalPolynomialSeries (hh (row j - y))) M = _
  rw [inverseContraction_interval _ _ M label (c.originalResponse_normal_blockTriangular P) lo hi]
  · rfl
  · intro j hj
    have hcut : x < col j := originalResponse_incoming_cutoff P b j hj
    rw [hh_of_neg (by omega), map_zero]
  · intro j hj
    have hcut : row j < y := originalResponse_outgoing_cutoff P d j hj
    rw [hh_of_neg (by omega), map_zero]

end SkewCornerDescent.Matrix.SelectedCoordinate
