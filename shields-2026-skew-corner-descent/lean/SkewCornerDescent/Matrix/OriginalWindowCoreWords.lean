/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedCoreWords
import SkewCornerDescent.Matrix.OriginalWindowOrderedResponses
import SkewCornerDescent.Matrix.OriginalWindowOrderedLowerResponses

/-!
# Complete selected-core words of actual end windows

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete literal windows supply each canonical selected rank and every whole
component translation. Both full proper-core polynomials are transported.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- An actual complete upper window retains both whole selected-core words at
its unshifted canonical ranks. No core correspondence is an input. -/
theorem originalWindow_upper_core_words {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i : Fin (originalSelectedCount (hD := hD) Q),
        c.originalSelectedCoreLeft Q i = c.originalSelectedCoreLeft P
          ⟨i.val, by have := i.isLt; omega⟩ ∧
        c.originalSelectedCoreRight Q i = c.originalSelectedCoreRight P
          ⟨i.val, by have := i.isLt; omega⟩ := by
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q q (P.xi 0) v
    hwindow hq hL
  refine ⟨hc, fun i => ?_⟩
  obtain ⟨a, ha, _, he⟩ := originalWindow_restriction_selected_rank P Q q v hwindow hq hL i
  have h := c.original_selected_core_polynomials_of_translate P Q
    (originalSelectedEnumeration P a) (originalSelectedEnumeration Q i) v he
  have hai : a = (⟨i.val, by have := i.isLt; omega⟩ :
      Fin (originalSelectedCount (hD := hD) P)) := Fin.ext ha
  rw [hai] at h
  exact ⟨h.1.symm, h.2.symm⟩

/-- An actual complete lower window retains both whole selected-core words at
its source-produced shifted ranks, including both endpoint occurrences. -/
theorem originalWindow_lower_core_words {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i : Fin (originalSelectedCount (hD := hD) Q),
        c.originalSelectedCoreLeft Q i = c.originalSelectedCoreLeft P
          ⟨i.val + (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) Q),
            by have := i.isLt; omega⟩ ∧
        c.originalSelectedCoreRight Q i = c.originalSelectedCoreRight P
          ⟨i.val + (originalSelectedCount (hD := hD) P - originalSelectedCount (hD := hD) Q),
            by have := i.isLt; omega⟩ := by
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q 0 (P.xi 0 - q) v
    hwindow hq hL
  refine ⟨hc, fun i => ?_⟩
  obtain ⟨a, ha, _, he⟩ := originalWindow_lower_restriction_selected_rank
    P Q q v hwindow hq hL i
  have h := c.original_selected_core_polynomials_of_translate P Q
    (originalSelectedEnumeration P a) (originalSelectedEnumeration Q i) v he
  have hai : a = (⟨i.val + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) Q), by have := i.isLt; omega⟩ :
      Fin (originalSelectedCount (hD := hD) P)) := Fin.ext ha
  rw [hai] at h
  exact ⟨h.1.symm, h.2.symm⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
