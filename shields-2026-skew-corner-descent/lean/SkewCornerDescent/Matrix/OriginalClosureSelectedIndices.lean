/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalClosureBlocks
import SkewCornerDescent.Matrix.OriginalClosureSelectedOrder

/-!
# Actual canonical selected indices of both closure copies

Supports `shields-2026-skew-corner-descent.tex` (`lem:actual-words`). The geometrically
selected whole occurrences coincide with the produced complete original block indices.
Their agreement is literal cell equality, not equality of a residue class. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The actual profile and gluing displacements identify the two whole component copies. -/
theorem originalHorizontalClosure_block_displacement {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) :
    v + originalClosureBlockDisplacement P upper = if upper then vH P.cells else 0 := by
  rw [(originalHorizontalClosure_profile_rows P Q v hQ).2]
  cases upper with
  | true =>
    change (-(n : ℤ), -(n : ℤ)) + (0, P.xi 0) = vH P.cells
    rw [originalHorizontalDisplacement_pair]
    apply Prod.ext <;> dsimp only [Prod.fst_add, Prod.snd_add] <;> omega
  | false =>
    change (-(n : ℤ), -(n : ℤ)) + ((n : ℤ), (n : ℤ)) = 0
    apply Prod.ext <;>
      dsimp only [Prod.fst_add, Prod.snd_add, Prod.fst_zero, Prod.snd_zero] <;> omega

/-- Whole geometric selected-copy matching fixes the actual canonical original representative. -/
theorem originalHorizontalClosureSelectedCopy_block {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    (originalHorizontalClosureSelectedCopy P Q v hQ upper b).val =
      originalClosureBlockCopy P Q v hQ upper b.val := by
  let cb : OriginalSelectedBlocks (hD := hD) Q :=
    ⟨originalClosureBlockCopy P Q v hQ upper b.val,
      (originalHorizontalClosure_block_selected P Q v hQ upper b.val).mpr b.property⟩
  have he : originalHorizontalClosureSelectedCopy P Q v hQ upper b = cb := by
    apply originalSelectedBlock_cells_injective Q
    apply translate_injective v
    rw [originalHorizontalClosureSelectedCopy_cells]
    change (if upper then translate (vH P.cells) (interiorBlockCells P b.val.val)
      else interiorBlockCells P b.val.val) =
        translate v (interiorBlockCells Q
          (originalClosureComplementaryCopy P Q v hQ upper b.val.val))
    rw [originalHorizontalClosure_block_cells, translate_translate,
      originalHorizontalClosure_block_displacement P Q v hQ]
    cases upper with
    | true => rfl
    | false => exact SkewGluing.translate_zero.symm
  exact congrArg Subtype.val he

end SkewCornerDescent.Matrix.SelectedCoordinate
