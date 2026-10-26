/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalClosureOrderedResponses
import SkewCornerDescent.Matrix.OriginalVerticalOrderedResponses
import SkewCornerDescent.Matrix.OriginalInternalNormalFrontiers

/-!
# Complete internal matrices in both actual closure copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every entry of the copied internal matrix is transported from its actual
selected endpoint ranks, retaining all original normal-dependent inverses.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both literal ordinary closures contain the complete lower source matrix.
The crossing join is outside this copied region, not removed from the closure. -/
theorem originalClosure_lower_internal_matrix {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells) :
    ∃ hc : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
        ((c.originalInternalResponseMatrix Q).map c.normalSeries)
            ⟨originalSelectedCount (hD := hD) P + i.val, by have := i.isLt; omega⟩
            ⟨originalSelectedCount (hD := hD) P + j.val, by have := j.isLt; omega⟩ =
          ((c.originalInternalResponseMatrix P).map c.normalSeries) i j := by
  have hc : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P := by
    rcases hQ with hQ | hQ
    · exact originalHorizontalClosure_profile_selected_count P Q z hQ
    · exact originalVerticalClosure_profile_selected_count P Q z hQ
  refine ⟨hc, fun i j => ?_⟩
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val + 1, by have := j.isLt; omega⟩
  have hraw : c.originalInternalResponseMatrix Q
        ⟨originalSelectedCount (hD := hD) P + i.val, by have := i.isLt; omega⟩
        ⟨originalSelectedCount (hD := hD) P + j.val, by have := j.isLt; omega⟩ =
      c.originalInternalResponseMatrix P i j := by
    change c.originalHessenbergResponse Q _ _ = c.originalHessenbergResponse P _ _
    rcases hQ with hQ | hQ
    · convert c.originalHorizontalClosure_ordered_response P Q z hQ false a b using 1 <;>
        congr 1
    · convert c.originalVerticalClosure_ordered_response P Q z hQ false a b using 1 <;>
        congr 1
  exact congrArg c.normalSeries hraw

/-- Both actual ordinary closures retain the whole upper source internal matrix,
with all original inverse entries and normal jets unchanged. -/
theorem originalClosure_upper_internal_matrix {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells) :
    ∃ hc : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
        ((c.originalInternalResponseMatrix Q).map c.normalSeries)
            ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ =
          ((c.originalInternalResponseMatrix P).map c.normalSeries) i j := by
  obtain ⟨hc, _⟩ := c.originalClosure_lower_internal_matrix P Q z hQ
  refine ⟨hc, fun i j => ?_⟩
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val + 1, by have := j.isLt; omega⟩
  have hraw : c.originalInternalResponseMatrix Q
        ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ =
      c.originalInternalResponseMatrix P i j := by
    change c.originalHessenbergResponse Q _ _ = c.originalHessenbergResponse P _ _
    rcases hQ with hQ | hQ
    · have h := c.originalHorizontalClosure_ordered_response P Q z hQ true a b
      simp only [originalClosureSelectedIndex, ite_true, zero_add] at h
      convert h using 1 <;> congr 1
    · have h := c.originalVerticalClosure_ordered_response P Q z hQ true a b
      simp only [originalVerticalClosureSelectedIndex, ite_true, zero_add] at h
      convert h using 1 <;> congr 1
  exact congrArg c.normalSeries hraw

end SkewCornerDescent.Matrix.SelectedCoordinate
