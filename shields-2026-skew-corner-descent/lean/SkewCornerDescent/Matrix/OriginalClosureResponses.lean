/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureResponseIntervals
import SkewCornerDescent.Matrix.TranslatedResponses

/-!
# Whole original responses inside the two literal closure copies

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Both retained endpoints
and the complete remaining interval have one common affine shift. The resulting equality
uses the full original inverse and holds in the regular ring before residue specialization.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- A copied selected row and its actual last selected column retain one common shift. -/
theorem originalHorizontalClosure_retained_endpoints {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let q := originalHorizontalClosureSelectedCopy P Q v hQ upper b
    let w := originalClosureBlockDisplacement P upper
    Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some q))) =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) + w.2 - w.1 ∧
    Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some q))) =
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) + w.2 - w.1 := by
  dsimp only
  rw [originalRowSplitEquiv_selected, originalRowSplitEquiv_selected,
    originalColSplitEquiv_selected, originalColSplitEquiv_selected,
    originalHorizontalClosureSelectedCopy_block]
  change Q.xi (originalClosureComplementaryCopy P Q v hQ upper b.val.val).succ = _ ∧
    Q.zeta (interiorBlockLast Q
      (originalClosureComplementaryCopy P Q v hQ upper b.val.val)).castSucc = _
  rw [originalHorizontalClosure_block_last]
  exact ⟨(originalHorizontalClosure_copy_coordinates P Q v hQ upper b.val.val).2.1,
    (originalHorizontalClosure_copy_coordinates P Q v hQ upper
      (interiorBlockLast P b.val.val)).2.2⟩

/-- The actual full local response between copied selected occurrences equals its source. -/
theorem originalHorizontalClosure_local_response {n m : ℕ}
    (c : SelectedCoordinate D hD) (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b d : OriginalSelectedBlocks (hD := hD) P) :
    c.originalLocalResponse Q
      (some (originalHorizontalClosureSelectedCopy P Q v hQ upper b))
      (some (originalHorizontalClosureSelectedCopy P Q v hQ upper d)) =
        c.originalLocalResponse P (some b) (some d) := by
  classical
  let qb := originalHorizontalClosureSelectedCopy P Q v hQ upper b
  let qd := originalHorizontalClosureSelectedCopy P Q v hQ upper d
  let e := originalClosureResponseIntervalEquiv P Q v hQ upper b d
  let w := originalClosureBlockDisplacement P upper
  let := c.originalResponseIntervalInverse P (some b) (some d)
  let := c.originalResponseIntervalInverse Q (some qb) (some qd)
  apply c.regularEmbedding_injective
  rw [c.originalLocalResponse_embedding_pruned, c.originalLocalResponse_embedding_pruned]
  apply intervalResponse_affine_reindex e _ _ _ _ (w.2 - w.1)
  · simpa only [add_sub_assoc] using
      (originalHorizontalClosure_retained_endpoints P Q v hQ upper b).1
  · simpa only [add_sub_assoc] using
      (originalHorizontalClosure_retained_endpoints P Q v hQ upper d).2
  · intro i
    simpa only [add_sub_assoc] using
      (originalHorizontalClosure_response_interval_endpoints P Q v hQ upper b d i).1
  · intro i
    simpa only [add_sub_assoc] using
      (originalHorizontalClosure_response_interval_endpoints P Q v hQ upper b d i).2

end SkewCornerDescent.Matrix.SelectedCoordinate
