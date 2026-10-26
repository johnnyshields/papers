/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.ResidueResponseHessian
import SkewCornerDescent.Matrix.OriginalResidueEndpointProfiles

/-!
# Actual original response higher-generator Hessian

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The source constructs its complete ordered residue inverse and both endpoint
support cutoffs. Its actual response has the full eight-path higher-generator
Hessian, not a frozen or diagonal inverse approximation. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual original retained response supplies its complete mixed higher
jet from the constructed full interval inverse. Every off-diagonal inverse
coupling and both internal derivative orders remain in the result. -/
theorem originalLocalResponse_residue_hessian {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q) :
    letI := c.originalResponseResidueIntervalInverse P b d
    let row := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseRows P i.1.1
    let col := fun i : OriginalResponseInterval (hD := hD) P b d => originalResponseCols P i.1.1
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl b))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl d))
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.regularResidue (c.originalLocalResponse P b d))) =
      c.residueIntervalHessian row col x y p q := by
  let := c.originalResponseResidueIntervalInverse P b d
  dsimp only
  rw [c.originalLocalResponse_residue_pruned P b d]
  exact c.residue_interval_response_hessian _ _ _ _ p q hp hq

end SkewCornerDescent.Matrix.SelectedCoordinate
