/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowTrueCaps
import SkewCornerDescent.Matrix.OriginalAmalgamationWindows
import SkewCornerDescent.Matrix.OriginalClosureCapProducts
import SkewCornerDescent.Matrix.OriginalWindowGapAssembly

/-!
# Common full true exterior germs of all four literal diagrams

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The source,
complete overlap window, actual amalgamation, and actual horizontal closure have the
same two true exterior responses before residue specialization. Every interval and
rank correspondence is produced from the literal parent cells. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete equal end windows preserve both true caps in the overlap window and union. -/
theorem originalWindow_common_true_caps {n m k : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (q : ℤ) (v u z : ℤ × ℤ)
    (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W) :
    (c.originalHessenbergResponse W 0 0 = c.originalHessenbergResponse P 0 0 ∧
      c.originalHessenbergResponse W (Fin.last _) (Fin.last _) =
        c.originalHessenbergResponse P (Fin.last _) (Fin.last _)) ∧
    (c.originalHessenbergResponse A 0 0 = c.originalHessenbergResponse P 0 0 ∧
      c.originalHessenbergResponse A (Fin.last _) (Fin.last _) =
        c.originalHessenbergResponse P (Fin.last _) (Fin.last _)) := by
  have hWP : W.cells = translate (-z)
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
    rw [← hW, translate_translate, neg_add_cancel, translate_zero]
  have hWUpper : W.cells = translate (-z - v)
      (P.cells.filter fun x => q ≤ content x ∧ content x < P.xi 0) := by
    rw [hwindow, translate_translate]
    have ht : -z - v + v = -z := by abel
    rw [ht]
    exact hWP
  have hb := originalProfile_interior_boundary_gaps P
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P W 0 (P.xi 0 - q)
    (-z) hWP hb.1 hcutLq
  have hP : 0 < originalSelectedCount (hD := hD) P := hC.trans_le hc
  have hWLeft := c.originalWindow_true_left_response P W q (-z - v) hWUpper hcutq hb.2 hC
  have hWRight := c.originalWindow_true_right_response P W q (-z) hWP hb.1 hcutLq hC
  have hcuts := originalAmalgamation_private_end_cuts P A q v u hq hv hwindow hA hcutq hcutLq
  obtain ⟨hleft, hright⟩ := originalAmalgamation_complete_end_windows P A q v u hq hv hwindow hA
  have hPUpper : P.cells = translate (u - v)
      (A.cells.filter fun x => q ≤ content x ∧ content x < A.xi 0) := by
    apply translate_injective v
    rw [translate_translate]
    have ht : v + (u - v) = u := by abel
    rw [ht]
    exact hright.symm
  have hALeft := c.originalWindow_true_left_response A P q (u - v) hPUpper
    (fun x hx => (hcuts x hx).2.1) (fun x hx => (hcuts x hx).2.2.2) hP
  have hARight := c.originalWindow_true_right_response A P q u hleft.symm
    (fun x hx => (hcuts x hx).1) (fun x hx => (hcuts x hx).2.2.1) hP
  exact ⟨⟨hWLeft, hWRight⟩, ⟨hALeft.symm, hARight.symm⟩⟩

/-- The actual horizontal closure preserves those same two full true exterior germs. -/
theorem originalWindow_common_closure_true_caps {n m k s : ℕ}
    (P : Profile n) (W : Profile k) (A : Profile m) (H : Profile s)
    (q : ℤ) (v u z h : ℤ × ℤ) (hq : 0 ≤ q) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => q ≤ content x ∧ content x < P.xi 0) =
      translate v (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hW : translate z W.cells = P.cells.filter
      (fun x => 0 ≤ content x ∧ content x < P.xi 0 - q))
    (hA : P.cells ∪ translate v P.cells = translate u A.cells)
    (hH : originalHorizontalClosure P = translate h H.cells)
    (hcutq : ∀ x ∈ diagramInterior P.cells, content x ≠ q)
    (hcutLq : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0 - q)
    (hC : 0 < originalSelectedCount (hD := hD) W) :
    c.originalHessenbergResponse H 0 0 = c.originalHessenbergResponse W 0 0 ∧
      c.originalHessenbergResponse H (Fin.last _) (Fin.last _) =
        c.originalHessenbergResponse A (Fin.last _) (Fin.last _) := by
  have hcaps := c.originalWindow_common_true_caps P W A q v u z hq hv hwindow hW hA
    hcutq hcutLq hC
  have hWP : W.cells = translate (-z)
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < P.xi 0 - q) := by
    rw [← hW, translate_translate, neg_add_cancel, translate_zero]
  have hc := originalLiteralWindow_selected_count_le (hD := hD) P W 0 (P.xi 0 - q)
    (-z) hWP (originalProfile_interior_boundary_gaps P).1 hcutLq
  have hP := hC.trans_le hc
  exact ⟨(c.originalHorizontalClosure_true_left_response P H h hH hP).trans hcaps.1.1.symm,
    (c.originalHorizontalClosure_true_right_response P H h hH hP).trans hcaps.2.2.symm⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
