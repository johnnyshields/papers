/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCoreHessianProjection

/-!
# Full actual inverse contractions with selected proper-core weights

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The actual selected core polynomials supply their nonnegative Laurent support.
The unchanged original interval supplies triangular inverse support and strict
block separation. Every within-component inverse entry remains. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing
open scoped BigOperators

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete projection weighted by its actual selected proper cores
contains only full same-component contractions, including nonrow unit blocks. -/
theorem original_interval_core_projection_same_blocks {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P) (z : ℤ) :
    letI := c.originalResponseResidueIntervalInverse P (some b) (some d)
    let row := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      originalResponseCols P i.1.1
    let I := ⅟(vertexBetaMatrix c.residueMap row col)
    let Qb := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    let Qd := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
    let A := (c.selectedCoreLeftPolynomial Qb (originalSelectedProfile_schur P b).symm).toLaurent
    let T := (c.selectedCoreRightPolynomial Qd (originalSelectedProfile_schur P d).symm).toLaurent
    profileInverseProjection row col I A T z =
      ∑ i, ∑ j, if interiorBlock P i.1.1.1.val = interiorBlock P j.1.1.1.val then
        A.coeff (z - col i) * I i j * T.coeff (row j - z) else 0 := by
  let Qb := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  let Qd := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
  have hQb : cellSchur D hD.1 = Qb.schur := (originalSelectedProfile_schur P b).symm
  have hQd : cellSchur D hD.1 = Qd.schur := (originalSelectedProfile_schur P d).symm
  dsimp only
  apply c.original_interval_inverse_projection_same_blocks P (some b) (some d) z
  · intro k hk
    rw [c.selected_core_left_toLaurent Qb hQb]
    exact endpointProfile_coeff_negative _ _
      (fun i => (c.selected_core_left_distances Qb hQb i).1.le) k hk
  · intro k hk
    rw [c.selected_core_right_toLaurent Qd hQd]
    exact endpointProfile_coeff_negative _ _
      (fun i => (c.selected_core_right_distances Qd hQd i).1.le) k hk

end SkewCornerDescent.Matrix.SelectedCoordinate
