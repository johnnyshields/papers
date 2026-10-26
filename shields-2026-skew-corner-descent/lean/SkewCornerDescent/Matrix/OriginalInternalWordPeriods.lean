/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.CopiedMatrixWordPeriods
import SkewCornerDescent.Matrix.OriginalAmalgamationInternalMatrices
import SkewCornerDescent.Matrix.OriginalClosureInternalMatrices

/-!
# Full normal diagonal and pair words from actual literal matrix copies

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`,
`prop:normal-interface`). The complete normal words have the actual overlap
period in the amalgamation and the complete source length in either closure.
These are not assumed to be full-normal periods of the smaller residue phase.
Canonical cycles retain the actual finite crossing pair, not a column-zero entry.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Literal complete source copies supply both full-normal matrix-word periods
of the actual amalgamation, including every genuine adjacent pair entry. -/
theorem originalAmalgamation_internal_word_periods {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hAP : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hinv : originalSelectedCount (hD := hD) A + originalSelectedCount (hD := hD) W =
      2 * originalSelectedCount (hD := hD) P,
      let T := originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P
      let N := originalSelectedCount (hD := hD) A - 1
      let M := (c.originalInternalResponseMatrix A).map c.normalSeries
      (∀ i j : Fin N, j.val = i.val + T → M i i = M j j) ∧
        (∀ i j : Fin (N - 1), j.val = i.val + T →
          M ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val + 1, by have := i.isLt; omega⟩ =
            M ⟨j.val, by have := j.isLt; omega⟩ ⟨j.val + 1, by have := j.isLt; omega⟩) := by
  obtain ⟨hAP, hinv, hlo⟩ := c.originalAmalgamation_lower_internal_matrix
    P W A q v u z hq hv hwindow hW hA hcutq hcutLq
  obtain ⟨_, hup⟩ := c.originalAmalgamation_upper_internal_matrix
    P A q v u hq hv hwindow hA hcutq hcutLq
  refine ⟨hAP, hinv, ?_⟩
  exact copied_matrix_word_periods
    (N := originalSelectedCount (hD := hD) A - 1)
    (B := originalSelectedCount (hD := hD) P - 1)
    (T := originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P)
    (by omega) ((c.originalInternalResponseMatrix A).map c.normalSeries)
    ((c.originalInternalResponseMatrix P).map c.normalSeries) hup hlo

/-- Both actual ordinary closures have the full source-length overlap period
for their normal diagonal and pair words. The unique central state is not erased. -/
theorem originalClosure_internal_word_periods {n m : ℕ}
    (P : Profile n) (Q : Profile m) (z : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate z Q.cells ∨
      originalVerticalClosure P = translate z Q.cells) :
    ∃ hCQ : originalSelectedCount (hD := hD) Q = 2 * originalSelectedCount (hD := hD) P,
      let T := originalSelectedCount (hD := hD) P
      let N := originalSelectedCount (hD := hD) Q - 1
      let M := (c.originalInternalResponseMatrix Q).map c.normalSeries
      (∀ i j : Fin N, j.val = i.val + T → M i i = M j j) ∧
        (∀ i j : Fin (N - 1), j.val = i.val + T →
          M ⟨i.val, by have := i.isLt; omega⟩ ⟨i.val + 1, by have := i.isLt; omega⟩ =
            M ⟨j.val, by have := j.isLt; omega⟩ ⟨j.val + 1, by have := j.isLt; omega⟩) := by
  obtain ⟨hCQ, hlo⟩ := c.originalClosure_lower_internal_matrix P Q z hQ
  obtain ⟨_, hup⟩ := c.originalClosure_upper_internal_matrix P Q z hQ
  refine ⟨hCQ, ?_⟩
  exact copied_matrix_word_periods
    (N := originalSelectedCount (hD := hD) Q - 1)
    (B := originalSelectedCount (hD := hD) P - 1)
    (T := originalSelectedCount (hD := hD) P)
    (by omega) ((c.originalInternalResponseMatrix Q).map c.normalSeries)
    ((c.originalInternalResponseMatrix P).map c.normalSeries) hup hlo

end SkewCornerDescent.Matrix.SelectedCoordinate
