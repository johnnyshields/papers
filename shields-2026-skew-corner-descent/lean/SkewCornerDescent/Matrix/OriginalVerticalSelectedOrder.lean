/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalSelectedCopies
import SkewCornerDescent.Matrix.OriginalVerticalSelectedInventory

/-!
# Actual order of both complete vertical selected-copy inventories

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Content separation orders every original selected occurrence in both complete
vertical copies, independently of equality of their selected Schur functions.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Both literal copy maps preserve the original selected occurrence order. -/
theorem originalVerticalClosureSelectedCopy_strictMono {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool) :
    StrictMono (originalVerticalClosureSelectedCopy (hD := hD) P Q v hQ upper) := by
  intro b e hbe
  have hb := congrArg minContent
    (originalVerticalClosureSelectedCopy_cells P Q v hQ upper b)
  have he := congrArg minContent
    (originalVerticalClosureSelectedCopy_cells P Q v hQ upper e)
  have hbs := originalBlockSelected_nonempty Q
    (originalVerticalClosureSelectedCopy P Q v hQ upper b).val
    (originalVerticalClosureSelectedCopy P Q v hQ upper b).property
  have hes := originalBlockSelected_nonempty Q
    (originalVerticalClosureSelectedCopy P Q v hQ upper e).val
    (originalVerticalClosureSelectedCopy P Q v hQ upper e).property
  rw [minContent_translate (interiorBlockCells_connected Q _ hbs).2.1] at hb
  rw [minContent_translate (interiorBlockCells_connected Q _ hes).2.1] at he
  have hmin := originalSelected_minContent_strictAnti P hbe
  change minContent (interiorBlockCells P e.val.val) <
    minContent (interiorBlockCells P b.val.val) at hmin
  apply (originalSelected_lt_iff_minContent Q _ _).mpr
  cases upper with
  | false => simp only [Bool.false_eq_true, ↓reduceIte] at hb he; omega
  | true =>
    simp only [↓reduceIte] at hb he
    rw [minContent_translate (interiorBlockCells_connected P b.val.val
      (originalBlockSelected_nonempty P b.val b.property)).2.1] at hb
    rw [minContent_translate (interiorBlockCells_connected P e.val.val
      (originalBlockSelected_nonempty P e.val e.property)).2.1] at he
    omega

/-- Every translated-copy occurrence precedes every unshifted-copy occurrence in source order. -/
theorem originalVerticalClosureSelectedCopy_before {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells)
    (b e : OriginalSelectedBlocks (hD := hD) P) :
    originalVerticalClosureSelectedCopy P Q v hQ true b <
      originalVerticalClosureSelectedCopy P Q v hQ false e := by
  have hb := congrArg minContent
    (originalVerticalClosureSelectedCopy_cells P Q v hQ true b)
  have he := congrArg minContent
    (originalVerticalClosureSelectedCopy_cells P Q v hQ false e)
  simp only [Bool.false_eq_true, ↓reduceIte] at hb he
  rw [minContent_translate (interiorBlockCells_connected Q _
    (originalBlockSelected_nonempty Q _
      (originalVerticalClosureSelectedCopy P Q v hQ true b).property)).2.1,
    minContent_translate (interiorBlockCells_connected P b.val.val
      (originalBlockSelected_nonempty P b.val b.property)).2.1] at hb
  rw [minContent_translate (interiorBlockCells_connected Q _
    (originalBlockSelected_nonempty Q _
      (originalVerticalClosureSelectedCopy P Q v hQ false e).property)).2.1] at he
  have hz := P.zeta_strictAnti.antitone
    (show (interiorBlockLast P b.val.val).castSucc ≤ Fin.last n from Fin.le_last _)
  rw [P.zeta_last] at hz
  have hx := P.xi_strictAnti
    (show (0 : Fin (n + 1)) < e.val.val.succ by change 0 < e.val.val.val + 1; omega)
  have hi := originalBlockSelected_nonempty P e.val e.property
  have hz' := P.zeta_strictAnti.antitone
    (show e.val.val.castSucc ≤ (interiorBlockLast P e.val.val).castSucc by
      change e.val.val.val ≤ (interiorBlockLast P e.val.val).val
      have hlast := interiorBlockFirst_le_last P e.val.val
      rw [e.val.property] at hlast
      exact Fin.le_def.mp hlast)
  rw [interiorBlockCells_minContent P b.val.val
    (originalBlockSelected_nonempty P b.val b.property)] at hb
  rw [interiorBlockCells_minContent P e.val.val hi] at he
  rw [originalVerticalDisplacement_content] at hb
  apply (originalSelected_lt_iff_minContent Q _ _).mpr
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
