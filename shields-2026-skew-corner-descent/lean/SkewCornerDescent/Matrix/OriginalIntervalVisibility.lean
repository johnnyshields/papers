/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalConsecutiveIntervals

/-!
# Actual opposite selected strips are invisible below half-span

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
The complete original selected endpoint distance and actual interval row/column
bounds exclude the opposite proper strip from the visible endpoint profile.
No profile truncation or selected-core support premise is supplied.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The far selected proper strip cannot contribute a visible incoming degree. -/
theorem original_interval_far_row_invisible {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (j : OriginalResponseInterval (hD := hD) P (some b) (some d))
    (hj : j.1.1.1 = d.val)
    (hspan : 2 * (c.top : ℤ) <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))) :
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) <
      2 * (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        originalResponseRows P j.1.1) := by
  have hl : originalResponseLowerCut P (some d) < (interiorBlock P j.1.1.1.val : ℤ) := by
    rw [hj]
    change (interiorBlock P d.val.val : ℤ) - 1 < (interiorBlock P d.val.val : ℤ)
    omega
  have hr := originalResponse_row_lt P (some d) j.1.1 hl
  have hd := c.originalSelected_endpoint_distance P d
  simp only [originalRowSplitEquiv_selected, originalColSplitEquiv_selected] at hr hspan ⊢
  change originalResponseRows P j.1.1 < P.xi d.val.val.succ at hr
  omega

/-- The first selected proper strip cannot contribute a visible outgoing degree. -/
theorem original_interval_far_col_invisible {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (j : OriginalResponseInterval (hD := hD) P (some b) (some d))
    (hj : j.1.1.1 = b.val)
    (hspan : 2 * (c.top : ℤ) <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))) :
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) <
      2 * (originalResponseCols P j.1.1 -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))) := by
  have hu : (interiorBlock P j.1.1.1.val : ℤ) < originalResponseUpperCut P (some b) := by
    rw [hj]
    change (interiorBlock P b.val.val : ℤ) < (interiorBlock P b.val.val : ℤ) + 1
    omega
  have hc := originalResponse_col_gt P (some b) j.1.1 hu
  have hb := c.originalSelected_endpoint_distance P b
  simp only [originalRowSplitEquiv_selected, originalColSplitEquiv_selected] at hc hspan ⊢
  change P.zeta (interiorBlockLast P b.val.val).castSucc < originalResponseCols P j.1.1 at hc
  omega

/-- Every visible incoming position between consecutive selected occurrences is
in its own initial proper strip or in a full nonselected block. -/
theorem original_consecutive_visible_row_cases {n : ℕ} (P : Profile n)
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
    j.1.1.1 = (originalSelectedEnumeration P i).val ∨
      ¬ originalBlockSelected (hD := hD) P j.1.1.1 := by
  rcases original_consecutive_interval_block_cases P i t ht j with hb | hd | hs
  · exact Or.inl hb
  · have h := c.original_interval_far_row_invisible P _ _ j hd hspan
    omega
  · exact Or.inr hs

/-- The dual visible outgoing positions use only their final proper strip and
full nonselected blocks, with no assumed component inventory. -/
theorem original_consecutive_visible_col_cases {n : ℕ} (P : Profile n)
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
    j.1.1.1 = (originalSelectedEnumeration P t).val ∨
      ¬ originalBlockSelected (hD := hD) P j.1.1.1 := by
  rcases original_consecutive_interval_block_cases P i t ht j with hb | hd | hs
  · have h := c.original_interval_far_col_invisible P _ _ j hb hspan
    omega
  · exact Or.inl hd
  · exact Or.inr hs

end SkewCornerDescent.Matrix.SelectedCoordinate
