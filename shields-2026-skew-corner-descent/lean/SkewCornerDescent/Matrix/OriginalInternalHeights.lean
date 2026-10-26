/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalInternalSelfJet

/-!
# Actual selected-to-selected interval heights

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:normal-interface`). The actual completed gap identifies the full
retained height and puts it strictly above twice the selected span.
No numerical gap bound is an extra input. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Each actual internal retained height is its completed gap plus the
selected span, with the original endpoint occurrences retained. -/
theorem originalInternal_height_eq_completed_gap {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      (c.top : ℤ) + c.originalCompletedGap P ⟨i.val, by have := i.isLt; omega⟩ := by
  let a : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val, by have := i.isLt; omega⟩
  let b : Fin (originalSelectedCount (hD := hD) P) := ⟨i.val + 1, by have := i.isLt; omega⟩
  let E := originalSelectedEnumeration (hD := hD) P
  have hg := c.originalCompletedGap_internal_endpoints P a
    (by dsimp only [a]; have := i.isLt; omega)
  have hh : originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) =
      P.xi (originalRowSplitEquiv P (.inl (some (E a)))) -
        P.zeta (originalColSplitEquiv P (.inl (some (E b)))) := by
    change P.xi (originalRowSplitEquiv P (.inl (originalHessenbergRows P a.succ))) -
      P.zeta (originalColSplitEquiv P (.inl (originalHessenbergCols P b.castSucc))) = _
    rw [originalHessenbergRows_succ, originalHessenbergCols_castSucc]
  rw [hh]
  dsimp only [a, b, E] at hg ⊢
  omega

/-- The full actual source gap, not an assumed numerical bound, puts every
selected-to-selected retained height strictly above twice the selected span. -/
theorem originalInternal_height_gt_twice_top {n : ℕ} (P : Profile n)
    (i : Fin (originalSelectedCount (hD := hD) P - 1)) :
    2 * (c.top : ℤ) < originalHessenbergDistance (hD := hD) P
      (originalInternalStateIndex P i) (originalInternalStateIndex P i) := by
  rw [c.originalInternal_height_eq_completed_gap P i]
  have hg := c.originalCompletedGap_gt_top P ⟨i.val, by have := i.isLt; omega⟩
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
