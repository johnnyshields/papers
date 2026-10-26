/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedStripIndices
import SkewCornerDescent.Matrix.SelectedCoreSeries

/-!
# Exact normalized coordinates of actual selected proper cores

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). Actual selection supplies the proper-minor size and the
literal source beta coordinates of its normalized selected profile. No selected
component is replaced by a Schur-equivalent diagram. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

attribute [local instance] Classical.propDecidable

variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The actual selected block leaves its complete proper minor, including size zero. -/
theorem originalRemovedSize_selected {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    originalRemovedSize (hD := hD) P b.val = interiorBlockLength P b.val.val := by
  simp only [originalRemovedSize, ite_eq_left b.property]

/-- Every remaining selected source row is exactly the corresponding proper
minor row of the normalized original component, with its actual beta translation. -/
theorem original_selected_core_row_coordinate {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (k : Fin (interiorBlockLength P b.val.val)) :
    let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    originalResponseRows P ⟨b.val, Fin.cast (originalRemovedSize_selected P b).symm k⟩ =
      Q.xi k.succ + P.zeta (interiorBlockLast P b.val.val).castSucc := by
  let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  have hpos : originalRemovedRowPosition (hD := hD) P b.val
      (Fin.cast (originalRemovedSize_selected P b).symm k) = k.succ := by
    apply Fin.ext
    simp only [originalRemovedRowPosition, dite_eq_left b.property]
    rfl
  have hx := congrFun (interiorSliceProfile_beta P _ _ _ (interiorBlock_slice_same P b.val.val)
    (interiorBlock_first_nonempty P b.val.val
      (originalBlockSelected_nonempty P b.val b.property))).1 k.succ
  change Q.xi k.succ = P.xi (interiorSliceIndex _ _ _ k.succ).succ -
    P.zeta (interiorSliceIndex _ _ _ (Fin.last _)).castSucc at hx
  rw [originalBlockInterval_last] at hx
  change P.xi (interiorSliceIndex _ _ _
    (originalRemovedRowPosition (hD := hD) P b.val
      (Fin.cast (originalRemovedSize_selected P b).symm k))).succ = _
  rw [hpos]
  exact sub_eq_iff_eq_add.mp hx.symm

/-- Every remaining selected source column is exactly the normalized proper
minor column, with the same actual beta translation. -/
theorem original_selected_core_col_coordinate {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (k : Fin (interiorBlockLength P b.val.val)) :
    let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    originalResponseCols P ⟨b.val, Fin.cast (originalRemovedSize_selected P b).symm k⟩ =
      Q.zeta k.castSucc + P.zeta (interiorBlockLast P b.val.val).castSucc := by
  let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  have hpos : originalRemovedColPosition (hD := hD) P b.val
      (Fin.cast (originalRemovedSize_selected P b).symm k) = k.castSucc := by
    apply Fin.ext
    rfl
  have hz := congrFun (interiorSliceProfile_beta P _ _ _ (interiorBlock_slice_same P b.val.val)
    (interiorBlock_first_nonempty P b.val.val
      (originalBlockSelected_nonempty P b.val b.property))).2 k.castSucc
  change Q.zeta k.castSucc = P.zeta (interiorSliceIndex _ _ _ k.castSucc).castSucc -
    P.zeta (interiorSliceIndex _ _ _ (Fin.last _)).castSucc at hz
  rw [originalBlockInterval_last] at hz
  change P.zeta (interiorSliceIndex _ _ _
    (originalRemovedColPosition (hD := hD) P b.val
      (Fin.cast (originalRemovedSize_selected P b).symm k))).castSucc = _
  rw [hpos]
  exact sub_eq_iff_eq_add.mp hz.symm

/-- The actual retained source row is the top row of that same normalized
component profile, translated by its actual last-column coordinate. -/
theorem original_selected_core_retained_row {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) :
    let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) =
      Q.xi 0 + P.zeta (interiorBlockLast P b.val.val).castSucc := by
  let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  have hx := congrFun (interiorSliceProfile_beta P _ _ _ (interiorBlock_slice_same P b.val.val)
    (interiorBlock_first_nonempty P b.val.val
      (originalBlockSelected_nonempty P b.val b.property))).1 0
  change Q.xi 0 = P.xi (interiorSliceIndex _ _ _ 0).succ -
    P.zeta (interiorSliceIndex _ _ _ (Fin.last _)).castSucc at hx
  have hf := (originalBlockInterval_first P b.val.val).trans b.val.property
  rw [hf, originalBlockInterval_last] at hx
  rw [originalRowSplitEquiv_selected]
  exact sub_eq_iff_eq_add.mp hx.symm

end SkewCornerDescent.Matrix.SelectedCoordinate
