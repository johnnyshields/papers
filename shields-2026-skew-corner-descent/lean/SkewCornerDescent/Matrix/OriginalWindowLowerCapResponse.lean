/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalWindowUpperCapResponse

/-!
# Full true lower exterior germs of a complete literal end window

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The actual
bottom parent cell fixes the normalization shift. Every whole cap block and its
full normal-dependent inverse is transported from literal cells. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A complete lower-content window preserves the full true right-cap germ at matched
occurrences. -/
theorem originalWindow_lower_cap_response {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hi : ℤ) (v : ℤ × ℤ)
    (hwindow : Q.cells = translate v
      (P.cells.filter fun x => 0 ≤ content x ∧ content x < hi))
    (hlo : ∀ x ∈ diagramInterior P.cells, content x ≠ 0)
    (hhi : ∀ x ∈ diagramInterior P.cells, content x ≠ hi)
    (b : OriginalSelectedBlocks (hD := hD) P) (b' : OriginalSelectedBlocks (hD := hD) Q)
    (hb : originalBlockInWindow P 0 hi b.val)
    (he : translate v (interiorBlockCells P b.val.val) = interiorBlockCells Q b'.val.val) :
    c.originalLocalResponse Q (some b') none = c.originalLocalResponse P (some b) none := by
  classical
  let q := content v
  have hbounds := originalLiteralWindow_profile_bounds P Q 0 hi v hwindow hlo hhi
  have hfilter : Q.cells.filter (fun x => 0 + q ≤ content x ∧
      content x < hi + q) = Q.cells := Finset.filter_eq_self.mpr hbounds.1
  have hcontained (a : OriginalBlocks P) (ha : originalCapBlockSide false b a) :
      originalBlockInWindow P 0 hi a :=
    originalBlockInWindow_after_selected P hi b a hb ha
  have hcontained' (a : OriginalBlocks Q) (_ : originalCapBlockSide false b' a) :
      originalBlockInWindow Q (0 + q) (hi + q) a :=
    originalLiteralWindow_full_profile_blocks P Q 0 hi v hwindow hlo hhi a
  obtain ⟨e, hend⟩ := originalLiteralWindow_cap_interval_equiv (hD := hD) P Q 0 hi
    q v rfl (by rw [hfilter]; exact hwindow) hlo hbounds.2.1 hhi hbounds.2.2
    false b b' hcontained hcontained' he
  have hbnd := originalBlockInWindow_bounds P 0 hi b.val hb
  have hs := originalBlockSelected_nonempty P b.val b.property
  have hz := P.zeta_nonneg b.val.val.castSucc
  have ht : 0 < hi := by omega
  have hshift := originalLiteralWindow_lower_shift P Q hi v ht hwindow
  have hx := (c.originalSelected_translated_endpoints P Q b b' v he).1
  let e' : OriginalResponseInterval (hD := hD) P (some b) none ≃
      OriginalResponseInterval (hD := hD) Q (some b') none := e
  apply c.regularEmbedding_injective
  let := c.originalResponseIntervalInverse P (some b) none
  let := c.originalResponseIntervalInverse Q (some b') none
  rw [c.originalLocalResponse_embedding_pruned, c.originalLocalResponse_embedding_pruned]
  apply intervalResponse_affine_reindex e' _ _ _ _ q
  · simp only [originalRowSplitEquiv_selected]
    exact hx
  · change Q.zeta (Fin.last m) = P.zeta (Fin.last n) + content v
    rw [Q.zeta_last, P.zeta_last, hshift, add_zero]
  · intro i
    exact (hend i).1
  · intro i
    exact (hend i).2

end SkewCornerDescent.Matrix.SelectedCoordinate
