/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowInverse
import SkewCornerDescent.Matrix.TranslatedResponses

/-!
# Complete full-inverse responses of literal source windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Equal complete
windows translate the full original-field response on their entire whole-block inventory.
The inverse and every endpoint-list equivalence are produced. Restriction to the selected
endpoint interval is a separate identification, not assumed here. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Full original-field response on the actual complete whole-window removed matrix. -/
noncomputable def originalWholeWindowResponse {n : ℕ} (P : Profile n) (lo hi x y : ℤ) :
    actualField := by
  classical
  let := c.originalWholeWindowFieldInverse P lo hi
  exact intervalResponse x y
    (fun i : OriginalWholeWindowRemaining (hD := hD) P lo hi =>
      originalResponseRows P ⟨i.1.val, i.2⟩)
    (fun i => originalResponseCols P ⟨i.1.val, i.2⟩)

/-- Literal complete windows preserve the full response, with no supplied inverse or
endpoint-transport hypotheses. All normal-dependent off-diagonal couplings remain. -/
theorem originalWholeWindowResponse_translate {n : ℕ} (P : Profile n)
    (lo hi q x y : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun a => lo + q ≤ content a ∧ content a < hi) =
      translate v (P.cells.filter fun a => lo ≤ content a ∧ content a < hi - q))
    (hlo : ∀ a ∈ diagramInterior P.cells, content a ≠ lo)
    (hloq : ∀ a ∈ diagramInterior P.cells, content a ≠ lo + q)
    (hhiq : ∀ a ∈ diagramInterior P.cells, content a ≠ hi - q)
    (hhi : ∀ a ∈ diagramInterior P.cells, content a ≠ hi) :
    c.originalWholeWindowResponse P (lo + q) hi (x + q) (y + q) =
      c.originalWholeWindowResponse P lo (hi - q) x y := by
  classical
  obtain ⟨e, hend, _⟩ := originalWindow_remaining_matrix_equiv (hD := hD)
    P lo hi q v hv hwindow hlo hloq hhiq hhi
  let := c.originalWholeWindowFieldInverse P lo (hi - q)
  let := c.originalWholeWindowFieldInverse P (lo + q) hi
  exact intervalResponse_affine_reindex e x y (x + q) (y + q) q
    (fun i => originalResponseRows P ⟨i.1.val, i.2⟩)
    (fun i => originalResponseCols P ⟨i.1.val, i.2⟩)
    (fun i => originalResponseRows P ⟨i.1.val, i.2⟩)
    (fun i => originalResponseCols P ⟨i.1.val, i.2⟩)
    rfl rfl (fun i => (hend i).1) (fun i => (hend i).2)

end SkewCornerDescent.Matrix.SelectedCoordinate
