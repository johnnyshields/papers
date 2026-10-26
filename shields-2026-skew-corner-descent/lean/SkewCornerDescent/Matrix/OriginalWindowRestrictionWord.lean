/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRestrictionRanks
import SkewCornerDescent.Matrix.OriginalLiteralWindowBounds
import SkewCornerDescent.Matrix.OriginalClosureResponseWord

/-!
# The complete actual internal response word of a restricted window

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). A complete
literal upper-content end window has exactly the initial source internal word. The
correspondence holds for the full regular-ring germs, not only their residues. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every full literal window profile has no more selected occurrences than its source. -/
theorem originalLiteralWindow_selected_count_le {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo hi : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi) :
    originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P := by
  classical
  obtain ⟨e, _⟩ := originalLiteralWindow_profile_selected_orderIso (hD := hD)
    P Q lo hi v hwindow hlo hhi
  change Fintype.card (OriginalSelectedBlocks (hD := hD) Q) ≤
    Fintype.card (OriginalSelectedBlocks (hD := hD) P)
  apply Fintype.card_le_of_injective (fun b => (e.symm b).val)
  intro a b hab
  exact e.symm.injective (Subtype.ext hab)

/-- The actual full internal window word is the initial source word, with all removed
normal-dependent inverse entries retained. Its length bound is produced from literal cells. -/
theorem originalWindow_restriction_internal_word {n m : ℕ} (P : Profile n) (Q : Profile m)
    (q : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0))
    (hq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hL : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0) :
    ∃ hcount : originalSelectedCount (hD := hD) Q ≤ originalSelectedCount (hD := hD) P,
      ∀ i : Fin (originalSelectedCount (hD := hD) Q - 1),
        c.originalInternalResponse Q i = c.originalInternalResponse P
          ⟨i.val, by have hi := i.isLt; omega⟩ := by
  classical
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P Q q (P.xi 0) v
    hwindow hq hL
  refine ⟨hc, fun i => ?_⟩
  let a : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val, by have hi := i.isLt; omega⟩
  let d : Fin (originalSelectedCount (hD := hD) Q) := ⟨i.val + 1, by have hi := i.isLt; omega⟩
  obtain ⟨b, hb, hbband, he⟩ := originalWindow_restriction_selected_rank P Q q v hwindow hq hL a
  obtain ⟨f, hf, hfband, he'⟩ := originalWindow_restriction_selected_rank P Q q v hwindow hq hL d
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
    (EP b) (EP f) (EQ a) (EQ d)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP b).val (EP b).property, hbband⟩)
    (Or.inl ⟨originalBlockSelected_nonempty P (EP f).val (EP f).property, hfband⟩)
    (hband a) (hband d) he he'
  have hb' : b = ⟨i.val, by have hi := i.isLt; omega⟩ := Fin.ext hb
  have hf' : f = ⟨i.val + 1, by have hi := i.isLt; omega⟩ := Fin.ext hf
  simp only [hb', hf'] at hr
  rw [c.originalInternalResponse_eq_local, c.originalInternalResponse_eq_local]
  exact hr

end SkewCornerDescent.Matrix.SelectedCoordinate
