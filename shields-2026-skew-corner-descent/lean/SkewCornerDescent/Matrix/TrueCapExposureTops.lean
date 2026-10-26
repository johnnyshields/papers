/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalHorizontalSplice

/-!
# True caps below the actual closure top

Supports `shields-2026-skew-corner-descent.tex`, «Actual responses and residue classes»
(`sec:normal-chart`, `lem:exposure`).

Both actual cap endpoint distances exceed the selected span. Their sum is the protected
closure top, so each cap is strictly below that top and remains off the anchor.

Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both true original caps are strictly below the protected literal closure top. -/
theorem originalTrueCaps_below_closure {n : ℕ} (P : Profile n)
    (first last : OriginalSelectedBlocks (hD := hD) P) :
    originalFirstCapDistance P first < (c.top : ℤ) + originalCapSpliceDistance P first last ∧
      originalLastCapDistance P last < (c.top : ℤ) + originalCapSpliceDistance P first last := by
  rw [c.originalCapSpliceDistance_cap_sum P first last]
  have hfirst := c.originalFirstCapDistance_gt_top P first
  have hlast := c.originalLastCapDistance_gt_top P last
  have hN : (0 : ℤ) < (c.top : ℤ) := by exact_mod_cast c.top.pos
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
