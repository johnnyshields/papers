/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRestrictionWord
import SkewCornerDescent.Matrix.OriginalWindowUpperCapResponse

/-!
# Complete ordered responses in an actual upper end window

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The literal complete window supplies matching selected ranks and every original
between-occurrence and left-cap germ, not just its diagonal response word.
All normal-dependent removed inverse entries remain. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A whole original upper end window preserves every ordered between-occurrence response.
Its selected-rank embedding and count bound are produced from complete literal cells. -/
theorem originalWindow_upper_ordered_responses {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i j : Fin (originalSelectedCount (hD := hD) Q),
        c.originalHessenbergResponse Q i.succ j.castSucc =
          c.originalHessenbergResponse P
            (⟨i.val, by have := i.isLt; omega⟩ : Fin (originalSelectedCount (hD := hD) P)).succ
            (⟨j.val, by have := j.isLt; omega⟩ :
              Fin (originalSelectedCount (hD := hD) P)).castSucc := by
  classical
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q q (P.xi 0) v
    hwindow hq hL
  refine ⟨hc, fun i j => ?_⟩
  obtain ⟨a, ha, haband, hae⟩ := originalWindow_restriction_selected_rank P Q q v hwindow hq hL i
  obtain ⟨b, hb, hbband, hbe⟩ := originalWindow_restriction_selected_rank P Q q v hwindow hq hL j
  let EP := originalSelectedEnumeration (hD := hD) P
  let EQ := originalSelectedEnumeration (hD := hD) Q
  have hbounds := originalLiteralWindow_profile_bounds P Q q (P.xi 0) v hwindow hq hL
  have hfilter : Q.cells.filter (fun x => q + content v ≤ content x ∧
      content x < P.xi 0 + content v) = Q.cells := Finset.filter_eq_self.mpr hbounds.1
  have hband (k : Fin (originalSelectedCount (hD := hD) Q)) :
      originalBlockInWindow Q (q + content v) (P.xi 0 + content v) (EQ k).val := by
    refine Or.inl ⟨originalBlockSelected_nonempty Q (EQ k).val (EQ k).property, ?_⟩
    intro x hx
    have hI := component_subset (interiorBlockCells_mem_components Q (EQ k).val.val
      (originalBlockSelected_nonempty Q (EQ k).val (EQ k).property)) hx
    exact hbounds.1 x (Finset.mem_filter.mp hI).1
  have hr := c.originalLocalResponse_literal_window_translate P Q q (P.xi 0) (content v)
    v rfl (by rw [hfilter]; exact hwindow) hq hbounds.2.1 hL hbounds.2.2
    (EP a) (EP b) (EQ i) (EQ j)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP a).val (EP a).property, haband⟩)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP b).val (EP b).property, hbband⟩)
    (hband i) (hband j) hae hbe
  have hai : a = ⟨i.val, by have := i.isLt; omega⟩ := Fin.ext ha
  have hbj : b = ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext hb
  rw [hai, hbj] at hr
  change c.originalLocalResponse Q _ _ = c.originalLocalResponse P _ _
  rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  exact hr

/-- A complete upper end window preserves every full left-cap response at its actual rank,
including all original normal jets. No cap matching premise is supplied. -/
theorem originalWindow_upper_ordered_left_responses {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ j : Fin (originalSelectedCount (hD := hD) Q),
        c.originalHessenbergResponse Q 0 j.castSucc =
          c.originalHessenbergResponse P 0
            (⟨j.val, by have := j.isLt; omega⟩ :
              Fin (originalSelectedCount (hD := hD) P)).castSucc := by
  classical
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q q (P.xi 0) v
    hwindow hq hL
  refine ⟨hc, fun j => ?_⟩
  obtain ⟨b, hb, hbband, hbe⟩ := originalWindow_restriction_selected_rank P Q q v hwindow hq hL j
  have hr := c.originalWindow_upper_cap_response P Q q v hwindow hq hL
    (originalSelectedEnumeration P b) (originalSelectedEnumeration Q j)
    (Or.inl ⟨originalBlockSelected_nonempty P (originalSelectedEnumeration P b).val
      (originalSelectedEnumeration P b).property, hbband⟩) hbe
  have hbj : b = ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext hb
  rw [hbj] at hr
  change c.originalLocalResponse Q _ _ = c.originalLocalResponse P _ _
  rw [originalHessenbergRows_zero, originalHessenbergCols_castSucc,
    originalHessenbergRows_zero, originalHessenbergCols_castSucc]
  exact hr

end SkewCornerDescent.Matrix.SelectedCoordinate
