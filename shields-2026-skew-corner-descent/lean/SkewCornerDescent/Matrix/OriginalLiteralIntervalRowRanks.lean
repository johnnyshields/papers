/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalIntervalOrdinalOrder
import SkewCornerDescent.Matrix.OriginalLiteralIntervalRanks

/-!
# Full literal interval copies recover the physical row map

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Complete interval cardinality and recovered endpoint core sizes identify
both actual two-pivot row frames. Strict beta order then identifies every
physical retained-row position, not only the interval’s total size.
The paired original beta translation is retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Genuine equal-height literal intervals have identical complete two-pivot row frames. -/
theorem originalInternal_literal_row_frame {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j) :
    (originalInternalRowLast P i + 1 - originalInternalRowStart P i =
      originalInternalRowLast P j + 1 - originalInternalRowStart P j) ∧
    (originalInternalRowEnd P i - originalInternalRowStart P i =
      originalInternalRowEnd P j - originalInternalRowStart P j) := by
  have hcard := Fintype.card_congr (Classical.choose hcopy)
  have hi := original_internal_interval_card (hD := hD) P i
  have hj := original_internal_interval_card (hD := hD) P j
  change Fintype.card (OriginalInternalInterval P i) + 2 =
    originalInternalRowLast P i + 1 - originalInternalRowStart P i at hi
  change Fintype.card (OriginalInternalInterval P j) + 2 =
    originalInternalRowLast P j + 1 - originalInternalRowStart P j at hj
  have hgap := originalInternal_literal_source_row_gap P i j hheight hcopy
  change (originalInternalRowEnd P i : ℤ) - (originalInternalRowStart P i : ℤ) =
    (originalInternalRowEnd P j : ℤ) - (originalInternalRowStart P j : ℤ) at hgap
  have hfi := originalInternal_row_frame_bounds P i
  have hfj := originalInternal_row_frame_bounds P j
  omega

/-- Complete paired original beta copies identify every physical retained-row position. -/
theorem originalInternal_literal_physical_row_map {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (hcopy : originalInternalLiteralCopy P i j) :
    ∃ e : OriginalInternalInterval P i ≃ OriginalInternalInterval P j,
      (∀ r, originalResponseRows P (e r).val.val = originalResponseRows P r.val.val +
          originalInternalIntervalShift P i j ∧
        originalResponseCols P (e r).val.val = originalResponseCols P r.val.val +
          originalInternalIntervalShift P i j) ∧
      ∀ r, ((originalRemovedRow P (e r).val.val.1 (e r).val.val.2).val : ℤ) =
        ((originalRemovedRow P r.val.val.1 r.val.val.2).val : ℤ) +
          (originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ) := by
  have hf := originalInternal_literal_row_frame P i j hheight hcopy
  obtain ⟨e, he⟩ := hcopy
  refine ⟨e, he, ?_⟩
  intro r
  have hrank := originalInterval_copy_relative_row_rank P P i j e
    (originalInternalIntervalShift P i j) (fun r => (he r).1) hf.1 hf.2 r
  have hsource := originalInternal_interval_row_bounds P i r
  have htarget := originalInternal_interval_row_bounds P j (e r)
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
