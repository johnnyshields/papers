/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowLowerRanks
import SkewCornerDescent.Matrix.OriginalWindowRestrictionWord
import SkewCornerDescent.Matrix.OriginalLiteralWindowBounds
import SkewCornerDescent.Matrix.OriginalClosureResponseWord

/-!
# The complete actual internal response word of a restricted window

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). A complete
literal lower-content end window has exactly the final source internal word. The
correspondence holds for the full regular-ring germs, not only their residues. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual full internal window word is the final source word, with all removed
normal-dependent inverse entries retained. Its length bound is produced from literal cells. -/
theorem originalWindow_lower_restriction_internal_word {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q) :
    ∃ hcount : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i : Fin (originalSelectedCount (hD := hD) Q - 1),
        c.originalInternalResponse Q i = c.originalInternalResponse P
          ⟨i.val + (originalSelectedCount (hD := hD) P -
            originalSelectedCount (hD := hD) Q), by have hi := i.isLt; omega⟩ := by
  classical
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q 0 (P.xi 0 - q) v
    hwindow hq hL
  refine ⟨hc, fun i => ?_⟩
  let a : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val, by have hi := i.isLt; omega⟩
  let d : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val + 1, by have hi := i.isLt; omega⟩
  obtain ⟨b, hb, hbband, he⟩ := originalWindow_lower_restriction_selected_rank
    P Q q v hwindow hq hL a
  obtain ⟨f, hf, hfband, he'⟩ := originalWindow_lower_restriction_selected_rank
    P Q q v hwindow hq hL d
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
    (EP b) (EP f) (EQ a) (EQ d)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP b).val (EP b).property, hbband⟩)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP f).val (EP f).property, hfband⟩)
    (hband a) (hband d) he he'
  have hb' : b = ⟨i.val + (originalSelectedCount (hD := hD) P -
            originalSelectedCount (hD := hD) Q), by have hi := i.isLt; omega⟩ := Fin.ext hb
  have hf' : f = ⟨i.val + (originalSelectedCount (hD := hD) P -
    originalSelectedCount (hD := hD) Q) + 1, by have hi := i.isLt; omega⟩ := by
    apply Fin.ext
    change f.val = i.val + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) Q) + 1
    change f.val = i.val + 1 + (originalSelectedCount (hD := hD) P -
      originalSelectedCount (hD := hD) Q) at hf
    rw [hf, Nat.add_right_comm]
  simp only [hb', hf'] at hr
  rw [c.originalInternalResponse_eq_local, c.originalInternalResponse_eq_local]
  exact hr

end SkewCornerDescent.Matrix.SelectedCoordinate
