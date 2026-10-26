/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalAmalgamationWord
import SkewCornerDescent.Matrix.OriginalWindowInternalMatrices

/-!
# Complete internal matrices in both actual amalgamation copies

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Literal complete end windows supply both full copied normal matrices and
their actual rank offset. All removed inverse coefficients are retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual amalgamation tail is the whole original internal normal matrix.
The selected inventory and every copied entry are consequences of literal cells. -/
theorem originalAmalgamation_lower_internal_matrix {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hc : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
    ∃ hinventory : originalSelectedCount (hD := hD) A +
      originalSelectedCount (hD := hD) W = 2 * originalSelectedCount (hD := hD) P,
      ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
        ((c.originalInternalResponseMatrix A).map c.normalSeries)
          ⟨(originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P) + i.val,
            by have := i.isLt; omega⟩
          ⟨(originalSelectedCount (hD := hD) A - originalSelectedCount (hD := hD) P) + j.val,
            by have := j.isLt; omega⟩ =
        ((c.originalInternalResponseMatrix P).map c.normalSeries) i j := by
  have hinventory := originalAmalgamation_selected_inventory (hD := hD)
    P W A q v u z hv hwindow hW hA
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  have hleft := (originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA).1
  obtain ⟨hc, he⟩ := c.originalWindow_lower_internal_matrix A P q u hleft.symm
    (fun x hx => (hcuts x hx).1) (fun x hx => (hcuts x hx).2.2.1)
  exact ⟨hc, hinventory, he⟩

/-- The whole upper source matrix is copied into the actual amalgamation,
including every off-diagonal response, removed inverse, and normal coefficient. -/
theorem originalAmalgamation_upper_internal_matrix {n m : ℕ}
    (P : Profile n) (A : Profile m) (q : ℤ) (v u : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hc : originalSelectedCount (hD := hD) P ≤ originalSelectedCount (hD := hD) A,
      ∀ i j : Fin (originalSelectedCount (hD := hD) P - 1),
        ((c.originalInternalResponseMatrix A).map c.normalSeries)
            ⟨i.val, by have := i.isLt; omega⟩ ⟨j.val, by have := j.isLt; omega⟩ =
          ((c.originalInternalResponseMatrix P).map c.normalSeries) i j := by
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  have hwin := (originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA).2
  have hupper : P.cells = translate (u - v)
      (A.cells.filter fun x => q ≤ content x ∧ content x < A.xi 0) := by
    apply translate_injective v
    rw [translate_translate, show v + (u - v) = u by abel]
    exact hwin.symm
  exact c.originalWindow_upper_internal_matrix A P q (u - v) hupper
    (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2)

end SkewCornerDescent.Matrix.SelectedCoordinate
