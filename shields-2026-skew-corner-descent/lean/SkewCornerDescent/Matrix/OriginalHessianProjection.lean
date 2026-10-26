/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueResponseHessian
import SkewCornerDescent.Matrix.ResidueHessianProjection

/-!
# Complete original response Hessian projections

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The complete original source supplies its inverse, endpoint profiles and the
full mixed jet. Two generators summing to the actual response span give exactly
the two full inverse projections, with both copies at a coincident square.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual full response has the two complete projected inverse Hessian
terms at the original intermediate positions. No core-only approximation or
independent-variable assignment is substituted for the actual source. -/
theorem originalLocalResponse_hessian_projection {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q)
    (hsum : (p : ℤ) + (q : ℤ) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))) :
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
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.regularResidue (c.originalLocalResponse P b d))) =
      -profileInverseProjection row col I A T (x - (q : ℤ)) -
        profileInverseProjection row col I A T (x - (p : ℤ)) := by
  let := c.originalResponseResidueIntervalInverse P b d
  dsimp only
  rw [c.originalLocalResponse_residue_hessian P b d p q hp hq]
  exact c.residue_hessian_profile_projection _ _ _ _ p q hsum

end SkewCornerDescent.Matrix.SelectedCoordinate
