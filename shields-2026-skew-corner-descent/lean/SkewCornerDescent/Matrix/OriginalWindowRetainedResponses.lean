/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowRetainedTransport
import SkewCornerDescent.Matrix.TranslatedResponses

/-!
# Full regular-ring retained responses in complete equal windows

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Literal matched
selected occurrences translate the complete actual retained response in the regular ring.
All boundary proper minors, unselected blocks, empty pivots, and normal-dependent inverse
entries are retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete literal source windows preserve the full actual regular retained response. -/
theorem originalLocalResponse_window_translate {n : ℕ} (P : Profile n)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : P.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi - q))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior P.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi - q)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (b d b' d' : OriginalSelectedBlocks (hD := hD) P)
    (hb : originalBlockInWindow P lo (hi - q) b.val)
    (hd : originalBlockInWindow P lo (hi - q) d.val)
    (hb' : originalBlockInWindow P (lo + q) hi b'.val)
    (hd' : originalBlockInWindow P (lo + q) hi d'.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells P b'.val.val)
    (he' : translate v (interiorBlockCells P d.val.val) = interiorBlockCells P d'.val.val) :
    c.originalLocalResponse P (some b') (some d') =
      c.originalLocalResponse P (some b) (some d) := by
  classical
  obtain ⟨e, hend⟩ := originalWindow_retained_interval_equiv (hD := hD) P lo hi q v hv
    hwindow hlo hloq hhiq hhi b d b' d' hb hd hb' hd' he he'
  have hx := (c.originalSelected_translated_endpoints P P b b' v he).1
  have hy := (c.originalSelected_translated_endpoints P P d d' v he').2
  rw [hv] at hx hy
  apply c.regularEmbedding_injective
  let := c.originalResponseIntervalInverse P (some b) (some d)
  let := c.originalResponseIntervalInverse P (some b') (some d')
  rw [c.originalLocalResponse_embedding_pruned, c.originalLocalResponse_embedding_pruned]
  simp only [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  exact intervalResponse_affine_reindex e _ _ _ _ q _ _ _ _ hx hy
    (fun i => (hend i).1) (fun i => (hend i).2)

end SkewCornerDescent.Matrix.SelectedCoordinate
