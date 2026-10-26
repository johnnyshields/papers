/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCoreHessianProjection

/-!
# Original selected endpoint strips lie outside the high projection positions

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Actual selected component spans and their full original block fibers bound
every removed endpoint in the first and last selected strips. Literal selected
rows have empty proper strips; no artificial thick-core premise is used.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Every removed column in the source's first selected strip lies at or
above the actual selected endpoint span. -/
theorem original_removed_col_ge_selected_left {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hsame : interiorBlock P j.1.val = interiorBlock P b.val.val) :
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) - (c.top : ℤ) ≤
      originalResponseCols P j := by
  let k := originalRemovedCol (hD := hD) P j.1 j.2
  have hk : k ∈ interiorBlockFiber P b.val.val := by
    rw [mem_interiorBlockFiber, originalRemovedCol_block]
    exact hsame
  have hlast := ((mem_interiorBlockFiber_iff P b.val.val k).mp hk).2
  have hcol := P.zeta_strictAnti.antitone
    (show k.castSucc ≤ (interiorBlockLast P b.val.val).castSucc by
      change k.val ≤ (interiorBlockLast P b.val.val).val
      exact hlast)
  have ht := c.originalSelected_endpoint_distance P b
  rw [originalRowSplitEquiv_selected]
  change P.xi b.val.val.succ - (c.top : ℤ) ≤ P.zeta k.castSucc
  omega

/-- Every removed row in the source's last selected strip lies at or
below its actual selected endpoint span. -/
theorem original_removed_row_le_selected_right {n : ℕ} (P : Profile n)
    (d : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hsame : interiorBlock P j.1.val = interiorBlock P d.val.val) :
    originalResponseRows P j ≤
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) + (c.top : ℤ) := by
  let k := originalRemovedRow (hD := hD) P j.1 j.2
  have hk : k ∈ interiorBlockFiber P d.val.val := by
    rw [mem_interiorBlockFiber, originalRemovedRow_block]
    exact hsame
  have hfirst := ((mem_interiorBlockFiber_iff P d.val.val k).mp hk).1
  rw [d.val.property] at hfirst
  have hrow := P.xi_strictAnti.antitone
    (show d.val.val.succ ≤ k.succ by
      change d.val.val.val + 1 ≤ k.val + 1
      exact Nat.add_le_add_right hfirst 1)
  have ht := c.originalSelected_endpoint_distance P d
  rw [originalColSplitEquiv_selected]
  change P.xi k.succ ≤ P.zeta (interiorBlockLast P d.val.val).castSucc + (c.top : ℤ)
  omega

end SkewCornerDescent.Matrix.SelectedCoordinate
