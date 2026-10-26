/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowOrderedResponses
import SkewCornerDescent.Matrix.OriginalWindowLowerWord
import SkewCornerDescent.Matrix.OriginalWindowLowerCapResponse

/-!
# Complete ordered responses in an actual lower end window

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete literal lower window supplies the exact final selected-rank segment
and every full between-occurrence and right-cap germ. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every ordered lower-window response is its full original shifted source response.
The rank offset and selected-count bound come from the complete literal window. -/
theorem originalWindow_lower_ordered_responses {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i j : Fin (originalSelectedCount (hD := hD) Q),
        c.originalHessenbergResponse Q i.succ j.castSucc =
          c.originalHessenbergResponse P
            (⟨i.val + (originalSelectedCount (hD := hD) P -
              originalSelectedCount (hD := hD) Q), by have := i.isLt; omega⟩ :
                Fin (originalSelectedCount (hD := hD) P)).succ
            (⟨j.val + (originalSelectedCount (hD := hD) P -
              originalSelectedCount (hD := hD) Q), by have := j.isLt; omega⟩ :
                Fin (originalSelectedCount (hD := hD) P)).castSucc := by
  classical
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q 0 (P.xi 0 - q) v
    hwindow hq hL
  refine ⟨hc, fun i j => ?_⟩
  obtain ⟨a, ha, haband, hae⟩ := originalWindow_lower_restriction_selected_rank
    P Q q v hwindow hq hL i
  obtain ⟨b, hb, hbband, hbe⟩ := originalWindow_lower_restriction_selected_rank
    P Q q v hwindow hq hL j
  let EP := originalSelectedEnumeration (hD := hD) P
  let EQ := originalSelectedEnumeration (hD := hD) Q
  have hbounds := originalLiteralWindow_profile_bounds P Q 0 (P.xi 0 - q) v hwindow hq hL
  have hfilter : Q.cells.filter (fun x => 0 + content v ≤ content x ∧
      content x < P.xi 0 - q + content v) = Q.cells := Finset.filter_eq_self.mpr hbounds.1
  have hband (k : Fin (originalSelectedCount (hD := hD) Q)) :
      originalBlockInWindow Q (0 + content v) (P.xi 0 - q + content v) (EQ k).val := by
    refine Or.inl ⟨originalBlockSelected_nonempty Q (EQ k).val (EQ k).property, ?_⟩
    intro x hx
    have hI := component_subset (interiorBlockCells_mem_components Q (EQ k).val.val
      (originalBlockSelected_nonempty Q (EQ k).val (EQ k).property)) hx
    exact hbounds.1 x (Finset.mem_filter.mp hI).1
  have hr := c.originalLocalResponse_literal_window_translate P Q 0 (P.xi 0 - q) (content v)
    v rfl (by rw [hfilter]; exact hwindow) hq hbounds.2.1 hL hbounds.2.2
    (EP a) (EP b) (EQ i) (EQ j)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP a).val (EP a).property, haband⟩)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP b).val (EP b).property, hbband⟩)
    (hband i) (hband j) hae hbe
  have hai : a = ⟨i.val + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) Q), by have := i.isLt; omega⟩ := Fin.ext ha
  have hbj : b = ⟨j.val + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) Q), by have := j.isLt; omega⟩ := Fin.ext hb
  simp only [hai, hbj] at hr
  change c.originalLocalResponse Q _ _ = c.originalLocalResponse P _ _
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  exact hr

/-- Every full lower-window right-cap germ occurs at the produced shifted source rank. -/
theorem originalWindow_lower_ordered_right_responses {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i : Fin (originalSelectedCount (hD := hD) Q),
        c.originalHessenbergResponse Q i.succ (Fin.last _) =
          c.originalHessenbergResponse P
            (⟨i.val + (originalSelectedCount (hD := hD) P -
              originalSelectedCount (hD := hD) Q), by have := i.isLt; omega⟩ :
                Fin (originalSelectedCount (hD := hD) P)).succ (Fin.last _) := by
  classical
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q 0 (P.xi 0 - q) v
    hwindow hq hL
  refine ⟨hc, fun i => ?_⟩
  obtain ⟨a, ha, haband, hae⟩ := originalWindow_lower_restriction_selected_rank
    P Q q v hwindow hq hL i
  have hr := c.originalWindow_lower_cap_response P Q (P.xi 0 - q) v hwindow hq hL
    (originalSelectedEnumeration P a) (originalSelectedEnumeration Q i)
    (Or.inl ⟨originalBlockSelected_nonempty P (originalSelectedEnumeration P a).val
      (originalSelectedEnumeration P a).property, haband⟩) hae
  have hai : a = ⟨i.val + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) Q), by have := i.isLt; omega⟩ := Fin.ext ha
  rw [hai] at hr
  change c.originalLocalResponse Q _ _ = c.originalLocalResponse P _ _
  rw [originalHessenbergRows_succ, originalHessenbergCols_last,
    originalHessenbergRows_succ, originalHessenbergCols_last]
  exact hr

end SkewCornerDescent.Matrix.SelectedCoordinate
