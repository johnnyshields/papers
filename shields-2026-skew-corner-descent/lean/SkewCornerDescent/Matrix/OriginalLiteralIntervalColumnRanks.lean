/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalIntervalPivotMask
import SkewCornerDescent.Matrix.OriginalLiteralIntervalRowRanks
import SkewCornerDescent.Matrix.OriginalLiteralInitialCore

/-!
# Full physical row and column maps of literal original intervals

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Whole initial and terminal core recovery fixes the two actual selected
proper-strip masks. Exact row-ordinal rigidity preserves those masks, so
the source’s genuine row-column index offsets recover the full physical
column map as well as the row map. Paired beta data are retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Actual paired interval copies preserve which retained points lie in selected proper strips. -/
theorem originalInternal_literal_copy_selected_flags {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j))
    (e : OriginalInternalInterval P i ≃ OriginalInternalInterval P j)
    (he : ∀ r, originalResponseRows P (e r).val.val = originalResponseRows P r.val.val +
          originalInternalIntervalShift P i j ∧
        originalResponseCols P (e r).val.val = originalResponseCols P r.val.val +
          originalInternalIntervalShift P i j) (r : OriginalInternalInterval P i) :
    originalBlockSelected (hD := hD) P (e r).val.val.1 ↔
      originalBlockSelected (hD := hD) P r.val.val.1 := by
  have hcopy : originalInternalLiteralCopy P i j := ⟨e, he⟩
  have hf := originalInternal_literal_row_frame P i j hheight hcopy
  have hlen := originalInternal_literal_start_length P i j hheight hcopy
  have hrank := originalInterval_copy_relative_row_rank P P i j e
    (originalInternalIntervalShift P i j) (fun r => (he r).1) hf.1 hf.2 r
  change (originalInternalRowOrdinal P j (e r)).val.val =
    (originalInternalRowOrdinal P i r).val.val at hrank
  rw [originalInternal_selected_row_ordinal_iff, originalInternal_selected_row_ordinal_iff,
    hrank, ← hf.2, ← hlen]

/-- A whole literal interval copy recovers both physical source-coordinate maps. -/
theorem originalInternal_literal_physical_both_maps {n : ℕ} (P : Profile n)
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
      ∀ r, (((originalRemovedRow P (e r).val.val.1 (e r).val.val.2).val : ℤ) =
          ((originalRemovedRow P r.val.val.1 r.val.val.2).val : ℤ) +
            (originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ)) ∧
        (((originalRemovedCol P (e r).val.val.1 (e r).val.val.2).val : ℤ) =
          ((originalRemovedCol P r.val.val.1 r.val.val.2).val : ℤ) +
            (originalInternalRowStart P j : ℤ) - (originalInternalRowStart P i : ℤ)) := by
  obtain ⟨e, he, hrow⟩ := originalInternal_literal_physical_row_map P i j hheight hcopy
  refine ⟨e, he, ?_⟩
  intro r
  refine ⟨hrow r, ?_⟩
  have hflag := originalInternal_literal_copy_selected_flags P i j hheight e he r
  have hsource := originalRemoved_row_col_rank_difference P r.val.val
  have htarget := originalRemoved_row_col_rank_difference P (e r).val.val
  have hr := hrow r
  by_cases hs : originalBlockSelected (hD := hD) P r.val.val.1
  · have ht := hflag.mpr hs
    simp only [ite_eq_left hs] at hsource
    simp only [ite_eq_left ht] at htarget
    omega
  · have ht : ¬ originalBlockSelected (hD := hD) P (e r).val.val.1 := fun h => hs (hflag.mp h)
    simp only [ite_eq_right hs] at hsource
    simp only [ite_eq_right ht] at htarget
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
