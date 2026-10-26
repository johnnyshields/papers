/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVisibleUnitSets

/-!
# Genuine extrema of complete original unit lists

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The greatest original row and least original column attain the minimum
endpoint distances in their full unit lists. Actual extreme indices and
source bounds supply the least-element contracts, including empty pivots.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The least incoming distance in the complete original unit row list is
attained at its genuine greatest row, including when the block is empty. -/
theorem original_unit_row_distances_least {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P) (u : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u) :
    IsLeast (originalUnitRowDistances P a u : Set ℤ)
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        P.xi (interiorBlockFirst P u.val).succ) := by
  classical
  constructor
  · refine Finset.mem_image.mpr ⟨originalUnitIndex P u hu 0, Finset.mem_univ _, ?_⟩
    change _ - P.xi (originalRemovedRow P u (originalUnitIndex P u hu 0)).succ = _
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first]
  · intro z hz
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hz
    rw [← hk]
    exact sub_le_sub_left (original_remaining_row_le_block_top P ⟨u, k⟩) _

/-- The least outgoing distance is attained at the actual least column, with
all original unit columns represented in the finite set. -/
theorem original_unit_col_distances_least {n : ℕ} (P : Profile n)
    (d : OriginalSelectedBlocks (hD := hD) P) (u : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u) :
    IsLeast (originalUnitColDistances P d u : Set ℤ)
      (originalComponentTau P u -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))) := by
  classical
  constructor
  · refine Finset.mem_image.mpr ⟨originalUnitIndex P u hu (Fin.last _), Finset.mem_univ _, ?_⟩
    change P.zeta (originalRemovedCol P u (originalUnitIndex P u hu (Fin.last _))).castSucc - _ = _
    rw [originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last]
    rfl
  · intro z hz
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hz
    rw [← hk]
    exact sub_le_sub_right (original_remaining_col_ge_tau P ⟨u, k⟩) _

end SkewCornerDescent.Matrix.SelectedCoordinate
