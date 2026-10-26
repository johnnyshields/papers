/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRowRemaining
import SkewCornerDescent.Matrix.OriginalCoreHessianProjection
import SkewCornerDescent.Matrix.RowProfileProjection

/-!
# Original all-row response projections count literal unit vertices

Supports `shields-2026-skew-corner-descent.tex` (`cor:row-pencil`).
The geometric all-row inventory supplies singleton actual remaining blocks
and empty selected proper cores. Complete original inverse support and its
unit pivots then identify each full endpoint projection with the actual
literal vertex count. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every full endpoint projection on an actual all-row source inventory is
the number of literal unit vertices at that position. The source supplies the
singleton block, strict separation, inverse unit and proper-core premises. -/
theorem original_interval_row_projection_count {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (horder : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hrows : ∀ C ∈ edgeComponents (diagramInterior P.cells), (C.image Prod.fst).card = 1)
    (z : ℤ) :
    letI := c.originalResponseResidueIntervalInverse P (some b) (some d)
    let row := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      originalResponseCols P i.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
    let I := ⅟(vertexBetaMatrix c.residueMap row col)
    let B := vertexOutgoing c.residueMap col x
    let C := vertexIncoming c.residueMap row y
    let A := endpointProfile (fun i => x - row i) (fun i => (B * I) () i)
    let T := endpointProfile (fun i => col i - y) (fun i => (I * C) i ())
    profileInverseProjection row col I A T z =
      ((Finset.univ.filter fun i => row i = z ∧ col i = z).card : OtherField c.top) := by
  let := c.originalResponseResidueIntervalInverse P (some b) (some d)
  let row := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseRows P i.1.1
  let col := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    originalResponseCols P i.1.1
  let M := vertexBetaMatrix c.residueMap row col
  let label := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
    interiorBlock P i.1.1.1.val
  have hlabel : Function.Injective label := by
    intro i j he
    apply Subtype.ext
    apply Subtype.ext
    exact originalRemaining_label_injective_of_all_rows P hrows he
  have hM : M.BlockTriangular label := by
    intro i j hij
    apply c.originalResponse_residue_blockTriangular P
    dsimp only [label] at hij
    dsimp only
    exact_mod_cast hij
  have hsep (i j : OriginalResponseInterval (hD := hD) P (some b) (some d))
      (hij : label i < label j) : row j < col i := by
    have hs := interior_block_endpoint_separation P
      (originalRemovedRow (hD := hD) P j.1.1.1 j.1.1.2)
      (originalRemovedCol (hD := hD) P i.1.1.1 i.1.1.2)
      (by rw [originalRemovedRow_block, originalRemovedCol_block]; exact hij)
    exact hs
  have hunit (i : OriginalResponseInterval (hD := hD) P (some b) (some d))
      (he : row i = col i) : M i i = 1 := by
    change c.residueMap (hh (row i - col i)) = 1
    rw [he, sub_self, hh_zero, map_one]
  have hp := c.original_interval_projection_proper_cores P b d horder hmax z
  have hb := c.original_selected_core_polynomials_eq_one_of_all_rows P hrows b
  have hd := c.original_selected_core_polynomials_eq_one_of_all_rows P hrows d
  dsimp only at hp hb hd ⊢
  rw [hb.1, hd.2, map_one] at hp
  exact hp.trans (row_profile_inverse_projection_count M row col label hlabel hM hsep hunit z)

end SkewCornerDescent.Matrix.SelectedCoordinate
