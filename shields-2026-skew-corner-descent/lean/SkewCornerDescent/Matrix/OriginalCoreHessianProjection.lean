/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCoreProjection

/-!
# Complete actual Hessian with the original selected proper-core weights

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The actual original mixed jet is the two inverse projections weighted by its
own selected proper cores. The source supplies the full inverse, its entry-span
bound and all profile-jet bridges. Complete nonrow unit inverses remain in the
formula. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Actual higher generators summing to the complete selected-to-selected
span give the two proper-core-weighted full inverse projections. Every within
component entry remains, including nonrow unit components and coincident high
generators. -/
theorem originalLocalResponse_proper_core_hessian {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (horder : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hsum : (p : ℤ) + (q : ℤ) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))) :
    letI := c.originalResponseResidueIntervalInverse P (some b) (some d)
    let row := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P (some b) (some d) =>
      originalResponseCols P i.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b)))
    let I := ⅟(vertexBetaMatrix c.residueMap row col)
    let Qb := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    let Qd := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
    let A := (c.selectedCoreLeftPolynomial Qb (originalSelectedProfile_schur P b).symm).toLaurent
    let T := (c.selectedCoreRightPolynomial Qd (originalSelectedProfile_schur P d).symm).toLaurent
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.regularResidue (c.originalLocalResponse P (some b) (some d)))) =
      -profileInverseProjection row col I A T (x - (q : ℤ)) -
        profileInverseProjection row col I A T (x - (p : ℤ)) := by
  let := c.originalResponseResidueIntervalInverse P (some b) (some d)
  dsimp only
  rw [c.originalLocalResponse_hessian_projection P (some b) (some d) p q hp hq hsum]
  rw [c.original_interval_projection_proper_cores P b d horder hmax,
    c.original_interval_projection_proper_cores P b d horder hmax]

end SkewCornerDescent.Matrix.SelectedCoordinate
