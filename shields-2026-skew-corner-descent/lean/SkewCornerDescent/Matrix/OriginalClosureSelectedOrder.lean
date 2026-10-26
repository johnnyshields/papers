/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalSelectedOrder

/-!
# Ordered selected occurrences in the literal horizontal closure

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:actual-words`). Both complete source copies supply their actual
selected occurrences. Their order is derived from literal least contents; no matching
permutation or occurrence order is assumed. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Every original selected occurrence occurs intact in either literal closure copy. -/
theorem originalHorizontalClosure_selected_copy_exists {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P) :
    ∃ e : OriginalSelectedBlocks (hD := hD) Q,
      translate v (interiorBlockCells Q e.val.val) =
        if upper then translate (vH P.cells) (interiorBlockCells P b.val.val)
        else interiorBlockCells P b.val.val := by
  have hb := originalBlockSelected_nonempty P b.val b.property
  have hC := interiorBlockCells_mem_components P b.val.val hb
  have he := (dvd_originalBlock_iff (hD := hD) P b.val.val hb).mp b.property
  cases upper with
  | false =>
    have hc := originalHorizontalClosure_first_component P hC
    rw [hQ] at hc
    exact exists_originalSelectedBlock_of_translated_component (hD := hD) Q v _ hc he
  | true =>
    have hc := originalHorizontalClosure_second_component P hC
    rw [hQ] at hc
    apply exists_originalSelectedBlock_of_translated_component (hD := hD) Q v _ hc
    exact he.trans (cellSchur_translate _ (interiorBlockCells_connected P b.val.val hb).1
      (vH P.cells)).symm

/-- The canonical block in an actual closure profile corresponding to a whole source copy. -/
noncomputable def originalHorizontalClosureSelectedCopy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P) :
    OriginalSelectedBlocks (hD := hD) Q :=
  (originalHorizontalClosure_selected_copy_exists P Q v hQ upper b).choose

/-- The produced copy map preserves the entire literal component, not just its function. -/
theorem originalHorizontalClosureSelectedCopy_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (upper : Bool) (b : OriginalSelectedBlocks (hD := hD) P) :
    translate v (interiorBlockCells Q
      (originalHorizontalClosureSelectedCopy P Q v hQ upper b).val.val) =
        if upper then translate (vH P.cells) (interiorBlockCells P b.val.val)
        else interiorBlockCells P b.val.val :=
  (originalHorizontalClosure_selected_copy_exists P Q v hQ upper b).choose_spec

/-- Both literal copy maps preserve the original selected occurrence order. -/
theorem originalHorizontalClosureSelectedCopy_strictMono {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells) (upper : Bool) :
    StrictMono (originalHorizontalClosureSelectedCopy (hD := hD) P Q v hQ upper) := by
  intro b e hbe
  have hb := congrArg minContent
    (originalHorizontalClosureSelectedCopy_cells P Q v hQ upper b)
  have he := congrArg minContent
    (originalHorizontalClosureSelectedCopy_cells P Q v hQ upper e)
  have hbs := originalBlockSelected_nonempty Q
    (originalHorizontalClosureSelectedCopy P Q v hQ upper b).val
    (originalHorizontalClosureSelectedCopy P Q v hQ upper b).property
  have hes := originalBlockSelected_nonempty Q
    (originalHorizontalClosureSelectedCopy P Q v hQ upper e).val
    (originalHorizontalClosureSelectedCopy P Q v hQ upper e).property
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
theorem originalHorizontalClosureSelectedCopy_before {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalHorizontalClosure P = translate v Q.cells)
    (b e : OriginalSelectedBlocks (hD := hD) P) :
    originalHorizontalClosureSelectedCopy P Q v hQ true b <
      originalHorizontalClosureSelectedCopy P Q v hQ false e := by
  have hb := congrArg minContent
    (originalHorizontalClosureSelectedCopy_cells P Q v hQ true b)
  have he := congrArg minContent
    (originalHorizontalClosureSelectedCopy_cells P Q v hQ false e)
  simp only [Bool.false_eq_true, ↓reduceIte] at hb he
  rw [minContent_translate (interiorBlockCells_connected Q _
    (originalBlockSelected_nonempty Q _
      (originalHorizontalClosureSelectedCopy P Q v hQ true b).property)).2.1,
    minContent_translate (interiorBlockCells_connected P b.val.val
      (originalBlockSelected_nonempty P b.val b.property)).2.1] at hb
  rw [minContent_translate (interiorBlockCells_connected Q _
    (originalBlockSelected_nonempty Q _
      (originalHorizontalClosureSelectedCopy P Q v hQ false e).property)).2.1] at he
  have hz := P.zeta_strictAnti.antitone
    (show (interiorBlockLast P b.val.val).castSucc ≤ Fin.last n from Fin.le_last _)
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
  rw [originalHorizontalDisplacement_content] at hb
  apply (originalSelected_lt_iff_minContent Q _ _).mpr
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
