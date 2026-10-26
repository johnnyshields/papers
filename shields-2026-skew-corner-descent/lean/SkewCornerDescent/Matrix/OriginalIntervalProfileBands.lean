/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedEndRecovery
import SkewCornerDescent.Matrix.OriginalIntervalVisibility
import SkewCornerDescent.Matrix.OriginalUnitProtectedPositions

/-!
# The selected and unit bands of actual interval profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Original coordinates put proper selected strips strictly below the selected
span and every nonselected block strictly above it. Actual consecutive-interval
visibility excludes the opposite strip and identifies the two bands exactly.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every genuine proper row of the initial selected block has endpoint
distance strictly between zero and the selected span. -/
theorem original_selected_row_distance_band {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hj : j.1 = b.val) :
    0 < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) - originalResponseRows P j ∧
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) - originalResponseRows P j <
        (c.top : ℤ) := by
  rcases j with ⟨u, k⟩
  change u = b.val at hj
  subst u
  let l := Fin.cast (originalRemovedSize_selected P b) k
  have hk : Fin.cast (originalRemovedSize_selected P b).symm l = k := by
    apply Fin.ext
    rfl
  have hc := original_selected_core_row_coordinate P b l
  rw [hk] at hc
  have hx := original_selected_core_retained_row P b
  have hb := c.selected_core_left_distances _ (originalSelectedProfile_schur P b).symm l
  rw [hx, hc]
  simpa only [add_sub_add_right_eq_sub] using hb

/-- The dual actual proper column has the same strict selected-span band. -/
theorem original_selected_col_distance_band {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hj : j.1 = b.val) :
    0 < originalResponseCols P j - P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) ∧
      originalResponseCols P j - P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) <
        (c.top : ℤ) := by
  rcases j with ⟨u, k⟩
  change u = b.val at hj
  subst u
  let l := Fin.cast (originalRemovedSize_selected P b) k
  have hk : Fin.cast (originalRemovedSize_selected P b).symm l = k := by
    apply Fin.ext
    rfl
  have hc := original_selected_core_col_coordinate P b l
  rw [hk] at hc
  have hb := c.selected_core_right_distances _ (originalSelectedProfile_schur P b).symm l
  rw [hc, originalColSplitEquiv_selected, add_sub_cancel_right]
  simpa only [Profile.zeta_last, sub_zero] using hb

/-- Every full nonselected block in a selected-start interval lies strictly
above the selected-span incoming band, including an empty pivot. -/
theorem original_interval_nonselected_row_high {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (j : OriginalResponseInterval (hD := hD) P (some a) d)
    (hs : ¬ originalBlockSelected (hD := hD) P j.1.1.1) :
    (c.top : ℤ) < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
      originalResponseRows P j.1.1 := by
  have hl := j.2
  change (interiorBlock P a.val.val : ℤ) - 1 < (interiorBlock P j.1.1.1.val : ℤ) at hl
  have hn : a.val ≠ j.1.1.1 := by intro he; exact hs (he ▸ a.property)
  have hne : interiorBlock P a.val.val ≠ interiorBlock P j.1.1.1.val := by
    intro he
    exact hn ((originalBlocks_label_strictMono P).injective he)
  apply c.original_row_distance_gt_top_of_later_block P a j.1.1
  omega

/-- Every nonselected block before a selected end lies in the strict outgoing
high band; no independent component-height assumption is used. -/
theorem original_interval_nonselected_col_high {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (j : OriginalResponseInterval (hD := hD) P b (some d))
    (hs : ¬ originalBlockSelected (hD := hD) P j.1.1.1) :
    (c.top : ℤ) < originalResponseCols P j.1.1 -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) := by
  have hl := j.1.2
  change (interiorBlock P j.1.1.1.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1 at hl
  have hn : j.1.1.1 ≠ d.val := by intro he; exact hs (he.symm ▸ d.property)
  have hne : interiorBlock P j.1.1.1.val ≠ interiorBlock P d.val.val := by
    intro he
    exact hn ((originalBlocks_label_strictMono P).injective he)
  apply c.original_col_distance_gt_top_of_earlier_block P d j.1.1
  omega

/-- In the visible half of an actual consecutive interval, the low incoming
band identifies exactly the initial selected proper strip. -/
theorem original_visible_row_low_iff_selected {n : ℕ} (P : Profile n)
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + 1)
    (j : OriginalResponseInterval (hD := hD) P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t)))
    (hspan : 2 * (c.top : ℤ) <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (originalSelectedEnumeration P i)))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (originalSelectedEnumeration P t)))))
    (hvisible : 2 * (P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i)))) - originalResponseRows P j.1.1) <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (originalSelectedEnumeration P i)))) -
        P.zeta (originalColSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P t))))) :
    (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (originalSelectedEnumeration P i)))) -
      originalResponseRows P j.1.1 ≤ (c.top : ℤ)) ↔
      j.1.1.1 = (originalSelectedEnumeration P i).val := by
  constructor
  · intro hlow
    rcases c.original_consecutive_visible_row_cases P i t ht j hspan hvisible with h | h
    · exact h
    · have hh := c.original_interval_nonselected_row_high P _ _ j h
      omega
  · intro h
    exact (c.original_selected_row_distance_band P _ j.1.1 h).2.le

/-- The low outgoing band identifies exactly the terminal selected proper strip. -/
theorem original_visible_col_low_iff_selected {n : ℕ} (P : Profile n)
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + 1)
    (j : OriginalResponseInterval (hD := hD) P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t)))
    (hspan : 2 * (c.top : ℤ) <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (originalSelectedEnumeration P i)))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (originalSelectedEnumeration P t)))))
    (hvisible : 2 * (originalResponseCols P j.1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P t))))) <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some (originalSelectedEnumeration P i)))) -
        P.zeta (originalColSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P t))))) :
    (originalResponseCols P j.1.1 -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some (originalSelectedEnumeration P t)))) ≤
        (c.top : ℤ)) ↔ j.1.1.1 = (originalSelectedEnumeration P t).val := by
  constructor
  · intro hlow
    rcases c.original_consecutive_visible_col_cases P i t ht j hspan hvisible with h | h
    · exact h
    · have hh := c.original_interval_nonselected_col_high P _ _ j h
      omega
  · intro h
    exact (c.original_selected_col_distance_band P _ j.1.1 h).2.le

end SkewCornerDescent.Matrix.SelectedCoordinate
