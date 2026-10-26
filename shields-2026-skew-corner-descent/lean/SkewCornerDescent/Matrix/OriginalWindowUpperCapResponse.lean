/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalLiteralWindowCaps
import SkewCornerDescent.Matrix.OriginalWindowProfileEndpoints
import SkewCornerDescent.Matrix.OriginalLiteralWindowResponses

/-!
# Full true upper exterior germs of a complete literal end window

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The actual
parent top cell supplies the exterior beta endpoint. Every whole cap block and its
full normal-dependent inverse is transported from literal cells. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A complete upper-content window preserves the full true left-cap germ at matched occurrences. -/
theorem originalWindow_upper_cap_response {n m : ℕ} (P : Profile n) (Q : Profile m)
    (lo : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => lo ≤ content x ∧ content x < P.xi 0))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ lo)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ P.xi 0)
    (b : OriginalSelectedBlocks (hD := hD) P) (b' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : originalBlockInWindow P lo (P.xi 0) b.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val) :
    c.originalLocalResponse Q none (some b') = c.originalLocalResponse P none (some b) := by
  classical
  let q := content v
  have hbounds := originalLiteralWindow_profile_bounds P Q lo (P.xi 0) v hwindow hlo hhi
  have hfilter : Q.cells.filter (fun x => lo + q ≤ content x ∧
      content x < P.xi 0 + q) = Q.cells := Finset.filter_eq_self.mpr hbounds.1
  have hcontained (a : OriginalBlocks P) (ha : originalCapBlockSide true b a) :
      originalBlockInWindow P lo (P.xi 0) a :=
    originalBlockInWindow_before_selected P lo b a hb ha
  have hcontained' (a : OriginalBlocks Q) (_ : originalCapBlockSide true b' a) :
      originalBlockInWindow Q (lo + q) (P.xi 0 + q) a :=
    originalLiteralWindow_full_profile_blocks P Q lo (P.xi 0) v hwindow hlo hhi a
  obtain ⟨e, hend⟩ := originalLiteralWindow_cap_interval_equiv (hD := hD) P Q lo (P.xi 0)
    q v rfl (by rw [hfilter]; exact hwindow) hlo hbounds.2.1 hhi hbounds.2.2
    true b b' hcontained hcontained' he
  have hbnd := originalBlockInWindow_bounds P lo (P.xi 0) b.val hb
  have hs := originalBlockSelected_nonempty P b.val b.property
  have ht : lo < P.xi 0 := by
    have hz := P.zeta_strictAnti.antitone (show b.val.val.castSucc ≤
      (interiorBlockLast P b.val.val).castSucc from interiorBlockFirst_le_last P b.val.val |>
        fun h => by rwa [b.val.property] at h)
    have hx := P.xi_strictAnti (show (0 : Fin (n + 1)) < b.val.val.succ from
      by change (0 : ℕ) < b.val.val.val + 1; omega)
    omega
  have htop := originalLiteralWindow_upper_top P Q lo v ht hwindow
  have hy := (c.originalSelected_translated_endpoints P Q b b' v he).2
  let e' : OriginalResponseInterval (hD := hD) P none (some b) ≃
      OriginalResponseInterval (hD := hD) Q none (some b') := e
  apply c.regularEmbedding_injective
  let := c.originalResponseIntervalInverse P none (some b)
  let := c.originalResponseIntervalInverse Q none (some b')
  rw [c.originalLocalResponse_embedding_pruned, c.originalLocalResponse_embedding_pruned]
  apply intervalResponse_affine_reindex e' _ _ _ _ q
  · change Q.xi 0 = P.xi 0 + q
    exact htop
  · simp only [originalColSplitEquiv_selected]
    exact hy
  · intro i
    exact (hend i).1
  · intro i
    exact (hend i).2

end SkewCornerDescent.Matrix.SelectedCoordinate
