/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowIntervals
import SkewCornerDescent.Matrix.TranslatedResponses

/-!
# Full retained responses between literal windows of different profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The entire
actual retained inverse and both retained endpoints are produced from complete literal
windows and their selected occurrences. Equality holds in the regular ring before residue
reduction, retaining every normal-dependent off-diagonal coupling. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Complete literal source windows preserve the full actual regular retained response. -/
theorem originalLocalResponse_literal_window_translate {n m : ℕ} (P : Profile n)
    (Q : Profile m)
    (lo hi q : ℤ) (v : ℤ × ℤ) (hv : content v = q)
    (hwindow : Q.cells.filter (fun x => lo + q ≤ content x ∧ content x < hi + q) =
      translate v (P.cells.filter fun x => lo ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hloq : ∀ x ∈ diagramInterior Q.cells, content x ≠ lo + q)
    (hhiq : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (hhi : ∀ x ∈ diagramInterior Q.cells, content x ≠ hi + q)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (b' d' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : originalBlockInWindow P lo (hi) b.val)
    (hd : originalBlockInWindow P lo (hi) d.val)
    (hb' : originalBlockInWindow Q (lo + q) (hi + q) b'.val)
    (hd' : originalBlockInWindow Q (lo + q) (hi + q) d'.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val)
    (he' : translate v (interiorBlockCells P d.val.val) = interiorBlockCells Q d'.val.val) :
    c.originalLocalResponse Q (some b') (some d') =
      c.originalLocalResponse P (some b) (some d) := by
  classical
  obtain ⟨e, hend⟩ := originalLiteralWindow_retained_interval_equiv (hD := hD) P Q lo hi q v hv
    hwindow hlo hloq hhiq hhi b d b' d' hb hd hb' hd' he he'
  have hx := (c.originalSelected_translated_endpoints P Q b b' v he).1
  have hy := (c.originalSelected_translated_endpoints P Q d d' v he').2
  rw [hv] at hx hy
  apply c.regularEmbedding_injective
  let := c.originalResponseIntervalInverse P (some b) (some d)
  let := c.originalResponseIntervalInverse Q (some b') (some d')
  rw [c.originalLocalResponse_embedding_pruned, c.originalLocalResponse_embedding_pruned]
  simp only [originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  exact intervalResponse_affine_reindex e _ _ _ _ q _ _ _ _ hx hy
    (fun i => (hend i).1) (fun i => (hend i).2)

end SkewCornerDescent.Matrix.SelectedCoordinate
