/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUpperResponses

/-!
# Strict original endpoint distances outside selected strips

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`). Any
later removed row starts strictly beyond the first selected span; every earlier
removed column starts strictly beyond the last selected span. Actual selected
endpoint distances and original block separation supply both bounds.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every removed row in a strictly later original block has left-profile
position strictly larger than the selected span, including literal unit vertices. -/
theorem original_row_distance_gt_top_of_later_block {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hlt : interiorBlock P b.val.val < interiorBlock P j.1.val) :
    (c.top : ℤ) < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
      originalResponseRows P j := by
  have ht := c.originalSelected_endpoint_distance P b
  have he := interior_block_endpoint_separation P
    (originalRemovedRow (hD := hD) P j.1 j.2) (interiorBlockLast P b.val.val)
    (by rw [originalRemovedRow_block, interiorBlockLast_label]; exact hlt)
  change originalResponseRows P j < P.zeta (interiorBlockLast P b.val.val).castSucc at he
  rw [originalRowSplitEquiv_selected]
  omega

/-- Every removed column in a strictly earlier original block has right-profile
position strictly larger than the selected span, without a generic gap bound. -/
theorem original_col_distance_gt_top_of_earlier_block {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hlt : interiorBlock P j.1.val < interiorBlock P b.val.val) :
    (c.top : ℤ) < originalResponseCols P j -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) := by
  have ht := c.originalSelected_endpoint_distance P b
  have he := interior_block_endpoint_separation P b.val.val
    (originalRemovedCol (hD := hD) P j.1 j.2)
    (by rw [originalRemovedCol_block]; exact hlt)
  change P.xi b.val.val.succ < originalResponseCols P j at he
  rw [originalColSplitEquiv_selected]
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
