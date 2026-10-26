/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalConsecutiveIntervalCard

/-!
# Actual physical row gap between selected occurrences

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The complete retained interval cardinality recovers the original source-row
separation after restoring its endpoint component and both omitted pivots.
All differences are integral, including single-row endpoint cores. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Physical source-row separation of two consecutive selected starting rows. -/
noncomputable def originalInternalSourceRowGap {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) : ℤ :=
  let a := originalSelectedEnumeration (hD := hD) P ⟨i.val, by have := i.isLt; omega⟩
  let b := originalSelectedEnumeration (hD := hD) P ⟨i.val+1, by have := i.isLt; omega⟩
  (b.val.val.val : ℤ) - (a.val.val.val : ℤ)

/-- Complete original interval sizes recover the physical selected-start gap. -/
theorem originalInternal_source_row_gap_card {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    let b := originalSelectedEnumeration (hD := hD) P ⟨i.val+1, by have := i.isLt; omega⟩
    originalInternalSourceRowGap P i = (Fintype.card (OriginalInternalInterval P i) : ℤ) -
      (interiorBlockLength P b.val.val : ℤ) + 1 := by
  let a := originalSelectedEnumeration (hD := hD) P ⟨i.val, by have := i.isLt; omega⟩
  let b := originalSelectedEnumeration (hD := hD) P ⟨i.val+1, by have := i.isLt; omega⟩
  have hc := original_internal_interval_card (hD := hD) P i
  change Fintype.card (OriginalInternalInterval P i) + 2 =
    (interiorBlockLast P b.val.val).val + 1 - a.val.val.val at hc
  have hb := Fin.le_def.mp (interiorBlockFirst_le_last P b.val.val)
  rw [b.val.property] at hb
  change (b.val.val.val : ℤ) - (a.val.val.val : ℤ) = _
  change (b.val.val.val : ℤ) - (a.val.val.val : ℤ) =
    (Fintype.card (OriginalInternalInterval P i) : ℤ) -
      ((interiorBlockLast P b.val.val).val - (interiorBlockFirst P b.val.val).val : ℕ) + 1
  rw [b.val.property]
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
