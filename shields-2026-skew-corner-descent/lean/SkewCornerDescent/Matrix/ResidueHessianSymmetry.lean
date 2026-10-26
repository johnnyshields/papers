/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueResponseHessian

/-!
# Higher-generator mixed jets commute on actual full responses

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
The full eight-path Hessian is symmetric in the two generators, so mixed
surviving-generator derivatives commute on complete original responses. This
includes both true caps and coincident generators. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The complete inverse Hessian retains both internal orders and is symmetric
in its two generator-entry selectors. -/
theorem residueIntervalHessian_symm {ν : Type*} [Fintype ν] [DecidableEq ν]
    (row col : ν → ℤ) (x y : ℤ) (p q : ℕ+)
    [Invertible (vertexBetaMatrix c.residueMap row col)] :
    c.residueIntervalHessian row col x y p q = c.residueIntervalHessian row col x y q p := by
  simp only [residueIntervalHessian, Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply]
  abel

/-- Mixed higher jets commute on the actual original retained response,
without treating a full inverse entry as constant on the selected chart. -/
theorem originalLocalResponse_higher_commute {n : ℕ} (P : Profile n)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q) :
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.regularResidue (c.originalLocalResponse P b d))) =
    residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
      (residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
        (c.regularResidue (c.originalLocalResponse P b d))) := by
  let := c.originalResponseResidueIntervalInverse P b d
  rw [c.originalLocalResponse_residue_hessian P b d p q hp hq,
    c.originalLocalResponse_residue_hessian P b d q p hq hp]
  exact c.residueIntervalHessian_symm _ _ _ _ p q

/-- Mixed higher jets commute on every complete original matrix response,
including the two actual diagonal caps. -/
theorem originalHessenbergResponse_higher_commute {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P + 1))
    (p q : ℕ+) (hp : c.top < p) (hq : c.top < q) :
    residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
      (residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
        (c.regularResidue (c.originalHessenbergResponse P i j))) =
    residueGeneratorDeriv c.top ⟨q, ne_of_gt hq⟩
      (residueGeneratorDeriv c.top ⟨p, ne_of_gt hp⟩
        (c.regularResidue (c.originalHessenbergResponse P i j))) := by
  exact c.originalLocalResponse_higher_commute P (originalHessenbergRows P i)
    (originalHessenbergCols P j) p q hp hq

end SkewCornerDescent.Matrix.SelectedCoordinate
