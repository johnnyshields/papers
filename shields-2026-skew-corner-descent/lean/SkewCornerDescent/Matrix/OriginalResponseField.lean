/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalResponseSupport

/-!
# Original field response seams

Supports `shields-2026-skew-corner-descent.tex`, «Equal windows and the determinant defect»
(`sec:normal-chart`, `lem:actual-elimination`). The actual local component response embeds
as its complete original-generator block contraction. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual selected block's complete local inverse is supplied by its proved regularity. -/
@[instance_reducible]
noncomputable def originalDiagonalLocalInverse {n : ℕ} (P : Profile n) (b : OriginalBlocks P) :
    Invertible ((originalRemovedDiagonal (hD := hD) P b).map
      (algebraMap Lambda c.RegularRing)) :=
  c.regularMatrixInverse _ (not_dvd_originalRemovedDiagonal P b)

/-- Embedding the actual component response retains every original-generator inverse entry. -/
theorem originalLocalResponse_diagonal_embedding {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    c.regularEmbedding (c.originalLocalResponse P (some b) (some b)) =
      originalMap ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inl (some b))) -
      inverseContraction
        (fun j : Fin (originalRemovedSize (hD := hD) P b.val) =>
          originalMap ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inr ⟨b.val, j⟩)))
        (fun j => originalMap
          ((originalSplitMatrix (hD := hD) P) (.inr ⟨b.val, j⟩) (.inl (some b))))
        ((originalRemovedDiagonal (hD := hD) P b.val).map originalMap) := by
  let := c.originalDiagonalLocalInverse P b.val
  rw [c.originalLocalResponse_diagonal, map_sub, c.regularEmbedding_polynomial]
  have hm : ((originalRemovedDiagonal (hD := hD) P b.val).map
      (algebraMap Lambda c.RegularRing)).map c.regularEmbedding =
      (originalRemovedDiagonal (hD := hD) P b.val).map originalMap := by
    apply Matrix.ext
    intro i j
    exact c.regularEmbedding_polynomial _
  rw [map_inverseContraction, hm]
  have hr : (c.regularEmbedding ∘ fun j : Fin (originalRemovedSize (hD := hD) P b.val) =>
      algebraMap Lambda c.RegularRing
        ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inr ⟨b.val, j⟩))) =
      fun j => originalMap
        ((originalSplitMatrix (hD := hD) P) (.inl (some b)) (.inr ⟨b.val, j⟩)) := by
    funext j
    exact c.regularEmbedding_polynomial _
  have hc : (c.regularEmbedding ∘ fun j : Fin (originalRemovedSize (hD := hD) P b.val) =>
      algebraMap Lambda c.RegularRing
        ((originalSplitMatrix (hD := hD) P) (.inr ⟨b.val, j⟩) (.inl (some b)))) =
      fun j => originalMap
        ((originalSplitMatrix (hD := hD) P) (.inr ⟨b.val, j⟩) (.inl (some b))) := by
    funext j
    exact c.regularEmbedding_polynomial _
  rw [hr, hc]

end SkewCornerDescent.Matrix.SelectedCoordinate
