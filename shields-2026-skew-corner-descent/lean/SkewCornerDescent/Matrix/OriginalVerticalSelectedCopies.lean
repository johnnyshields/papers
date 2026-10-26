/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVerticalWindows
import SkewCornerDescent.Matrix.OriginalWindowRows
import SkewCornerDescent.Matrix.SelectedCoreLiteralTransport
import SkewCornerDescent.Matrix.OriginalWindowRemainingOccurrences

/-!
# Whole selected occurrences in the actual vertical closure

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Both complete source component copies supply actual selected occurrences in
every canonical vertical profile. Literal cells produce their normalized
endpoints, proper cores, and whole-window containment. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both literal source copies produce complete actual selected occurrences
in a vertical profile; no component or selected-core correspondence is given. -/
theorem originalVerticalClosure_selected_copy_exists {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    ∃ d : OriginalSelectedBlocks (hD := hD) Q,
      translate v (interiorBlockCells Q d.val.val) =
        if upper then translate (vH P.cells - eCell) (interiorBlockCells P b.val.val)
        else interiorBlockCells P b.val.val := by
  have hb := originalBlockSelected_nonempty P b.val b.property
  have hC := interiorBlockCells_mem_components P b.val.val hb
  have hpsi := (dvd_originalBlock_iff (hD := hD) P b.val.val hb).mp b.property
  cases upper
  · have hcomp : interiorBlockCells P b.val.val ∈
        edgeComponents (diagramInterior (originalVerticalClosure P)) := by
      rw [originalVerticalClosure_components]
      exact Finset.mem_union_left _ hC
    rw [hQ] at hcomp
    exact exists_originalSelectedBlock_of_translated_component (hD := hD) Q v _ hcomp hpsi
  · have hcomp : translate (vH P.cells - eCell) (interiorBlockCells P b.val.val) ∈
        edgeComponents (diagramInterior (originalVerticalClosure P)) := by
      rw [originalVerticalClosure_components]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, hC, rfl⟩)
    rw [hQ] at hcomp
    apply exists_originalSelectedBlock_of_translated_component (hD := hD) Q v _ hcomp
    exact hpsi.trans (cellSchur_translate _ (interiorBlockCells_connected P b.val.val hb).1
      (vH P.cells - eCell)).symm

/-- The actual whole selected source copy in the normalized vertical closure. -/
noncomputable def originalVerticalClosureSelectedCopy {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) : OriginalSelectedBlocks (hD := hD) Q :=
  (originalVerticalClosure_selected_copy_exists P Q v hQ upper b).choose

/-- The selected-copy producer retains every original component cell. -/
theorem originalVerticalClosureSelectedCopy_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    translate v (interiorBlockCells Q
      (originalVerticalClosureSelectedCopy P Q v hQ upper b).val.val) =
        if upper then translate (vH P.cells - eCell) (interiorBlockCells P b.val.val)
        else interiorBlockCells P b.val.val :=
  (originalVerticalClosure_selected_copy_exists P Q v hQ upper b).choose_spec

/-- The actual normalization displacement for one whole vertical source copy. -/
def originalVerticalCopyDisplacement {n : ℕ} (P : Profile n) (v : ℤ × ℤ) (upper : Bool) :=
  if upper then vH P.cells - eCell - v else -v

/-- Both whole selected copies agree as normalized literal cells. -/
theorem originalVerticalClosure_selected_normalized_cells {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    translate (originalVerticalCopyDisplacement P v upper) (interiorBlockCells P b.val.val) =
      interiorBlockCells Q (originalVerticalClosureSelectedCopy P Q v hQ upper b).val.val := by
  apply translate_injective v
  rw [translate_translate, originalVerticalClosureSelectedCopy_cells]
  cases upper
  · simp only [originalVerticalCopyDisplacement, Bool.false_eq_true, ↓reduceIte,
      add_neg_cancel, translate_zero]
  · simp only [originalVerticalCopyDisplacement, ↓reduceIte]
    rw [show v + (vH P.cells - eCell - v) = vH P.cells - eCell by abel]

/-- The produced vertical copy shifts contents by the span or by zero. -/
theorem originalVerticalCopyDisplacement_content {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool) :
    content (originalVerticalCopyDisplacement P v upper) = if upper then P.xi 0 else 0 := by
  have hv := originalVerticalClosure_profile_content P Q v hQ
  have hw := originalVerticalDisplacement_content P
  cases upper <;> simp only [originalVerticalCopyDisplacement, Bool.false_eq_true, ↓reduceIte]
  · simp only [content, Prod.fst_neg, Prod.snd_neg] at *
    omega
  · simp only [content, eCell, Prod.fst_sub, Prod.snd_sub] at *
    omega

include c in
/-- Both actual retained endpoint lists have the produced vertical-copy shift. -/
theorem originalVerticalClosure_retained_endpoints {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let d := originalVerticalClosureSelectedCopy P Q v hQ upper b
    Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some d))) =
        P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) +
          (if upper then P.xi 0 else 0) ∧
      Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some d))) =
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) +
          (if upper then P.xi 0 else 0) := by
  have he := c.originalSelected_translated_endpoints P Q b _
    (originalVerticalCopyDisplacement P v upper)
    (originalVerticalClosure_selected_normalized_cells P Q v hQ upper b)
  rw [originalVerticalCopyDisplacement_content P Q v hQ upper] at he
  dsimp only
  rw [originalRowSplitEquiv_selected, originalColSplitEquiv_selected,
    originalRowSplitEquiv_selected, originalColSplitEquiv_selected]
  exact he

/-- The whole selected occurrence lies in its actual complete vertical
half window. Every source cell, not merely a scalar response, is transported. -/
theorem originalVerticalClosure_selected_copy_window {n m : ℕ}
    (P : Profile n) (Q : Profile m) (v : ℤ × ℤ)
    (hQ : originalVerticalClosure P = translate v Q.cells) (upper : Bool)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let shift : ℤ := if upper then P.xi 0 else 0
    let d := originalVerticalClosureSelectedCopy P Q v hQ upper b
    originalBlockInWindow Q shift (P.xi 0 + shift) d.val := by
  intro shift d
  left
  refine ⟨originalBlockSelected_nonempty Q d.val d.property, ?_⟩
  intro x hx
  have he := originalVerticalClosure_selected_normalized_cells P Q v hQ upper b
  rw [← he, mem_translate] at hx
  have hb := P.content_bounds_cells
    (Finset.mem_filter.mp (interiorSliceCells_subset P _ _ _ hx)).1
  have hw := originalVerticalCopyDisplacement_content P Q v hQ upper
  change content (originalVerticalCopyDisplacement P v upper) = shift at hw
  have hc : content (x - originalVerticalCopyDisplacement P v upper) = content x - shift := by
    simp only [content, Prod.fst_sub, Prod.snd_sub] at *
    omega
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
