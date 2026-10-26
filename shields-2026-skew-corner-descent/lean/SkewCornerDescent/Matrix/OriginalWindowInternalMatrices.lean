/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowOrderedResponses
import SkewCornerDescent.Matrix.OriginalWindowOrderedLowerResponses
import SkewCornerDescent.Matrix.OriginalInternalNormalFrontiers

/-!
# Complete internal normal matrices in actual end windows

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal full-window geometry supplies every ordered retained entry. The exact
internal row/column offset and all normal coefficients are transported together.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The whole upper-window internal normal matrix is the unshifted source
submatrix. No entry, inverse, or normal coefficient match is an input. -/
theorem originalWindow_upper_internal_matrix {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1),
        ((c.originalInternalResponseMatrix P).map c.normalSeries)
            ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ =
          ((c.originalInternalResponseMatrix Q).map c.normalSeries) i j := by
  obtain ⟨hc, he⟩ := c.originalWindow_upper_ordered_responses P Q q v hwindow hq hL
  refine ⟨hc, fun i j => ?_⟩
  let a : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) Q) := ⟨j.val + 1, by have := j.isLt; omega⟩
  have hraw : c.originalInternalResponseMatrix P
        ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ =
      c.originalInternalResponseMatrix Q i j := by
    change c.originalHessenbergResponse P _ _ = c.originalHessenbergResponse Q _ _
    convert (he a b).symm using 1 <;> congr 1
  exact congrArg c.normalSeries hraw

/-- The whole lower-window internal normal matrix is the complete shifted source
submatrix, including every coefficient of all original denominator inverses. -/
theorem originalWindow_lower_internal_matrix {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i j : Fin (originalSelectedCount (hD := hD) Q - 1),
        ((c.originalInternalResponseMatrix P).map c.normalSeries)
            ⟨(originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) Q) + i.val,
              by have := i.isLt; omega⟩
            ⟨(originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) Q) + j.val,
              by have := j.isLt; omega⟩ =
          ((c.originalInternalResponseMatrix Q).map c.normalSeries) i j := by
  obtain ⟨hc, he⟩ := c.originalWindow_lower_ordered_responses P Q q v hwindow hq hL
  refine ⟨hc, fun i j => ?_⟩
  let a : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) Q) := ⟨j.val + 1, by have := j.isLt; omega⟩
  have hraw : c.originalInternalResponseMatrix P
        ⟨(originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) Q) + i.val,
          by have := i.isLt; omega⟩
        ⟨(originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) Q) + j.val,
          by have := j.isLt; omega⟩ = c.originalInternalResponseMatrix Q i j := by
    change c.originalHessenbergResponse P _ _ = c.originalHessenbergResponse Q _ _
    convert (he a b).symm using 1 <;> congr 1 <;> apply Fin.ext <;>
      simp only [a, b, originalInternalStateIndex, Fin.val_succ, Fin.val_castSucc] <;> omega
  exact congrArg c.normalSeries hraw

end SkewCornerDescent.Matrix.SelectedCoordinate
