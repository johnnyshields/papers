/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/


import SkewCornerDescent.Matrix.OriginalLiteralIntervalColumnRanks
import SkewCornerDescent.Matrix.OriginalSelectedBetaGaps

/-!
# Exact original beta translation of both retained endpoint pivots

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The genuine selected core span and actual equal interval heights transport
both retained starting-row pivots and both selected last-column pivots
under the same original beta shift. These are the coordinates omitted
from the full removed interval, not replacement pivots. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The original interval shift is exactly its two retained starting beta coordinates. -/
theorem originalInternalIntervalShift_eq_beta {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1)) :
    originalInternalIntervalShift P i j =
      originalSelectedSourceBeta P ⟨j.val, by have := j.isLt; omega⟩ -
        originalSelectedSourceBeta P ⟨i.val, by have := i.isLt; omega⟩ := by
  unfold originalInternalIntervalShift
  rw [originalRowSplitEquiv_selected, originalRowSplitEquiv_selected]
  rfl

/-- Equal actual heights transport both row pivots and both column pivots at one beta shift. -/
theorem originalInternal_equal_height_pivot_betas {n : ℕ} (P : Profile n)
    (i j : Fin (originalSelectedCount (hD := hD) P - 1))
    (hheight : originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      originalHessenbergDistance (hD := hD) P
        (originalInternalStateIndex P j) (originalInternalStateIndex P j)) :
    let ai := originalSelectedEnumeration (hD := hD) P ⟨i.val, by have := i.isLt; omega⟩
    let bi := originalSelectedEnumeration (hD := hD) P ⟨i.val+1, by have := i.isLt; omega⟩
    let aj := originalSelectedEnumeration (hD := hD) P ⟨j.val, by have := j.isLt; omega⟩
    let bj := originalSelectedEnumeration (hD := hD) P ⟨j.val+1, by have := j.isLt; omega⟩
    (P.xi aj.val.val.succ = P.xi ai.val.val.succ + originalInternalIntervalShift P i j) ∧
    (P.xi bj.val.val.succ = P.xi bi.val.val.succ + originalInternalIntervalShift P i j) ∧
    (P.zeta (interiorBlockLast P aj.val.val).castSucc =
      P.zeta (interiorBlockLast P ai.val.val).castSucc + originalInternalIntervalShift P i j) ∧
    (P.zeta (interiorBlockLast P bj.val.val).castSucc =
      P.zeta (interiorBlockLast P bi.val.val).castSucc + originalInternalIntervalShift P i j) := by
  obtain ⟨coord⟩ := exists_selectedCoordinate hD
  let ai : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let bi : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val+1, by have := i.isLt; omega⟩
  let aj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val, by have := j.isLt; omega⟩
  let bj : Fin (originalSelectedCount (hD := hD) P) := ⟨j.val+1, by have := j.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have hai := coord.originalSelected_endpoint_distance P (E ai)
  have hbi := coord.originalSelected_endpoint_distance P (E bi)
  have haj := coord.originalSelected_endpoint_distance P (E aj)
  have hbj := coord.originalSelected_endpoint_distance P (E bj)
  have hshift : originalInternalIntervalShift P i j =
      P.xi (E aj).val.val.succ - P.xi (E ai).val.val.succ :=
    originalInternalIntervalShift_eq_beta P i j
  change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P ai.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P bi.castSucc))) =
    P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P aj.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P bj.castSucc))) at hheight
  simp only [originalHessenbergRows_succ, originalHessenbergCols_castSucc,
    originalRowSplitEquiv_selected, originalColSplitEquiv_selected] at hheight
  change P.xi (E ai).val.val.succ - P.zeta (interiorBlockLast P (E bi).val.val).castSucc =
    P.xi (E aj).val.val.succ - P.zeta (interiorBlockLast P (E bj).val.val).castSucc at hheight
  change (P.xi (E aj).val.val.succ =
      P.xi (E ai).val.val.succ + originalInternalIntervalShift P i j) ∧
    (P.xi (E bj).val.val.succ = P.xi (E bi).val.val.succ + originalInternalIntervalShift P i j) ∧
    (P.zeta (interiorBlockLast P (E aj).val.val).castSucc =
      P.zeta (interiorBlockLast P (E ai).val.val).castSucc + originalInternalIntervalShift P i j) ∧
    (P.zeta (interiorBlockLast P (E bj).val.val).castSucc =
      P.zeta (interiorBlockLast P (E bi).val.val).castSucc + originalInternalIntervalShift P i j)
  refine ⟨?_, ?_, ?_, ?_⟩ <;> omega

end SkewCornerDescent.Matrix.SelectedCoordinate
