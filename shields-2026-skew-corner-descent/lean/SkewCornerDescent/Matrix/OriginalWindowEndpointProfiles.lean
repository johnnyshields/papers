/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowEndpointProfiles
import SkewCornerDescent.Matrix.OriginalWindowOrderedResponses
import SkewCornerDescent.Matrix.OriginalWindowOrderedLowerResponses

/-!
# Full endpoint polynomials in complete actual end windows

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`,
`lem:early-recovery`). Actual selected ranks and whole remaining-index
equivalences preserve both full endpoint polynomials, not only their product.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A complete upper literal window preserves both full endpoint polynomials
at the actual selected occurrence ranks. -/
theorem originalWindow_upper_endpoint_polynomials {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i j : Fin (originalSelectedCount (hD := hD) Q),
        c.originalResidueLeftEndpointPolynomial Q
            (some (originalSelectedEnumeration Q i)) (some (originalSelectedEnumeration Q j)) =
          c.originalResidueLeftEndpointPolynomial P
            (some (originalSelectedEnumeration P ⟨i.val, by have := i.isLt; omega⟩))
            (some (originalSelectedEnumeration P ⟨j.val, by have := j.isLt; omega⟩)) ∧
        c.originalResidueRightEndpointPolynomial Q
            (some (originalSelectedEnumeration Q i)) (some (originalSelectedEnumeration Q j)) =
          c.originalResidueRightEndpointPolynomial P
            (some (originalSelectedEnumeration P ⟨i.val, by have := i.isLt; omega⟩))
            (some (originalSelectedEnumeration P ⟨j.val, by have := j.isLt; omega⟩)) := by
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
  have hr := c.originalEndpointProfiles_literal_window_translate P Q q (P.xi 0) (content v)
    v rfl (by rw [hfilter]; exact hwindow) hq hbounds.2.1 hL hbounds.2.2
    (EP a) (EP b) (EQ i) (EQ j)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP a).val (EP a).property, haband⟩)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP b).val (EP b).property, hbband⟩)
    (hband i) (hband j) hae hbe
  have hai : a = ⟨i.val, by have := i.isLt; omega⟩ := Fin.ext ha
  have hbj : b = ⟨j.val, by have := j.isLt; omega⟩ := Fin.ext hb
  rw [hai, hbj] at hr
  simpa only [EP, EQ] using hr

/-- A complete lower literal window preserves both full endpoint polynomials
at the actual selected occurrence ranks. -/
theorem originalWindow_lower_endpoint_polynomials {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hc : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i j : Fin (originalSelectedCount (hD := hD) Q),
        c.originalResidueLeftEndpointPolynomial Q
            (some (originalSelectedEnumeration Q i)) (some (originalSelectedEnumeration Q j)) =
          c.originalResidueLeftEndpointPolynomial P
            (some (originalSelectedEnumeration P
              ⟨i.val + (originalSelectedCount P - originalSelectedCount Q),
                by have := i.isLt; omega⟩))
            (some (originalSelectedEnumeration P
              ⟨j.val + (originalSelectedCount P - originalSelectedCount Q),
                by have := j.isLt; omega⟩)) ∧
        c.originalResidueRightEndpointPolynomial Q
            (some (originalSelectedEnumeration Q i)) (some (originalSelectedEnumeration Q j)) =
          c.originalResidueRightEndpointPolynomial P
            (some (originalSelectedEnumeration P
              ⟨i.val + (originalSelectedCount P - originalSelectedCount Q),
                by have := i.isLt; omega⟩))
            (some (originalSelectedEnumeration P
              ⟨j.val + (originalSelectedCount P - originalSelectedCount Q),
                by have := j.isLt; omega⟩)) := by
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
  have hr := c.originalEndpointProfiles_literal_window_translate P Q 0 (P.xi 0 - q) (content v)
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
  simpa only [EP, EQ] using hr

end SkewCornerDescent.Matrix.SelectedCoordinate
