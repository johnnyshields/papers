/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureSelectedIndices

/-!
# Actual retained rows and columns in closure copies

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). Exact determinant
selection and complete block intervals produce the actual remaining sizes and indices.
Selected boundary blocks retain their proper minors; unselected blocks retain every
original row and column. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Each complete block has exactly the same actual remaining size in either closure copy. -/
theorem originalHorizontalClosure_removed_size {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalBlocks P) :
    originalRemovedSize (hD := hD) Q (originalClosureBlockCopy P Q v hQ upper b) =
      originalRemovedSize (hD := hD) P b := by
  classical
  simp only [originalRemovedSize, originalHorizontalClosure_block_selected]
  have hl := originalHorizontalClosure_block_length P Q v hQ upper b.val
  change interiorBlockLength Q (originalClosureBlockCopy P Q v hQ upper b).val =
    interiorBlockLength P b.val at hl
  rw [hl]

/-- The remaining row position is preserved, including the omitted selected first row. -/
theorem originalHorizontalClosure_removed_row_position {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalBlocks P) (j : Fin (originalRemovedSize (hD := hD) P b)) :
    (originalRemovedRowPosition (hD := hD) Q (originalClosureBlockCopy P Q v hQ upper b)
      (Fin.cast (originalHorizontalClosure_removed_size P Q v hQ upper b).symm j)).val =
        (originalRemovedRowPosition (hD := hD) P b j).val := by
  classical
  by_cases hs : originalBlockSelected (hD := hD) P b
  · have hq := (originalHorizontalClosure_block_selected P Q v hQ upper b).mpr hs
    simp only [originalRemovedRowPosition, dite_eq_left hs, dite_eq_left hq, Fin.val_cast]
  · have hq : ¬originalBlockSelected (hD := hD) Q (originalClosureBlockCopy P Q v hQ upper b) :=
      fun h => hs ((originalHorizontalClosure_block_selected P Q v hQ upper b).mp h)
    simp only [originalRemovedRowPosition, dite_eq_right hs, dite_eq_right hq, Fin.val_cast]

/-- Every remaining original row is the literal copied source row, with its selection intact. -/
theorem originalHorizontalClosure_removed_row {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalBlocks P) (j : Fin (originalRemovedSize (hD := hD) P b)) :
    originalRemovedRow (hD := hD) Q (originalClosureBlockCopy P Q v hQ upper b)
      (Fin.cast (originalHorizontalClosure_removed_size P Q v hQ upper b).symm j) =
        originalClosureComplementaryCopy P Q v hQ upper (originalRemovedRow (hD := hD) P b j) := by
  apply Fin.ext
  change (interiorBlockFirst Q (originalClosureComplementaryCopy P Q v hQ upper b.val)).val +
    (originalRemovedRowPosition (hD := hD) Q (originalClosureBlockCopy P Q v hQ upper b)
      (Fin.cast (originalHorizontalClosure_removed_size P Q v hQ upper b).symm j)).val = _
  rw [originalHorizontalClosure_block_first, originalHorizontalClosure_removed_row_position]
  cases upper with
  | true => rfl
  | false =>
    change n + (interiorBlockFirst P b.val).val +
      (originalRemovedRowPosition (hD := hD) P b j).val =
        n + ((interiorBlockFirst P b.val).val + (originalRemovedRowPosition (hD := hD) P b j).val)
    omega

/-- Every remaining original column is the literal copied source column, including proper minors. -/
theorem originalHorizontalClosure_removed_col {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalBlocks P) (j : Fin (originalRemovedSize (hD := hD) P b)) :
    originalRemovedCol (hD := hD) Q (originalClosureBlockCopy P Q v hQ upper b)
      (Fin.cast (originalHorizontalClosure_removed_size P Q v hQ upper b).symm j) =
        originalClosureComplementaryCopy P Q v hQ upper (originalRemovedCol (hD := hD) P b j) := by
  apply Fin.ext
  change (interiorBlockFirst Q (originalClosureComplementaryCopy P Q v hQ upper b.val)).val +
    j.val = _
  rw [originalHorizontalClosure_block_first]
  cases upper with
  | true => rfl
  | false =>
    change n + (interiorBlockFirst P b.val).val + j.val =
      n + ((interiorBlockFirst P b.val).val + j.val)
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
