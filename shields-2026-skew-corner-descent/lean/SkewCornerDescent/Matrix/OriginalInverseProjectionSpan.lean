/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalBlockSpanCoordinates
import SkewCornerDescent.Matrix.ProfileProjectionJets

/-!
# Full original residue inverse entry support span

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
A nonzero complete interval inverse entry is either within one original
component, bounded by its actual content span, or above the block diagonal,
where its row-minus-column difference is negative. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Geometric maximal component span supplies the full original inverse entry
bound required to replace endpoint profiles by their proper-core jets. No
bound on opaque inverse entries is supplied as a hypothesis. -/
theorem original_interval_inverse_entry_span {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P)) (N : ℕ)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ N) :
    letI := c.originalResponseResidueIntervalInverse P b d
    let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
    let I := ⅟(vertexBetaMatrix c.residueMap row col)
    ∀ i j, I i j ≠ 0 → row j - col i ≤ (N : ℤ) := by
  let := c.originalResponseResidueIntervalInverse P b d
  let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
  let M := vertexBetaMatrix c.residueMap row col
  let label := fun i : OriginalResponseInterval (hD := hD) P b d => interiorBlock P i.1.1.1.val
  have hM : M.BlockTriangular label := by
    intro i j hij
    apply c.originalResponse_residue_blockTriangular P
    dsimp only [label] at hij
    dsimp only
    exact_mod_cast hij
  have hI : (⅟M).BlockTriangular label := by
    rw [Matrix.invOf_eq_nonsing_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hM
  dsimp only
  intro i j hne
  rcases lt_trichotomy (label i) (label j) with hij | he | hji
  · have hs := interior_block_endpoint_separation P
      (originalRemovedRow (hD := hD) P j.1.1.1 j.1.1.2)
      (originalRemovedCol (hD := hD) P i.1.1.1 i.1.1.2)
      (by rw [originalRemovedRow_block, originalRemovedCol_block]; exact hij)
    change row j < col i at hs
    exact (sub_neg.mpr hs).le.trans (by exact_mod_cast Nat.zero_le N)
  · have hs := interior_same_block_entry_span_le P N hmax
      (originalRemovedCol (hD := hD) P i.1.1.1 i.1.1.2)
      (originalRemovedRow (hD := hD) P j.1.1.1 j.1.1.2)
      (by rw [originalRemovedRow_block, originalRemovedCol_block]; exact he.symm)
    exact hs
  · exact (hne (hI hji)).elim

end SkewCornerDescent.Matrix.SelectedCoordinate
