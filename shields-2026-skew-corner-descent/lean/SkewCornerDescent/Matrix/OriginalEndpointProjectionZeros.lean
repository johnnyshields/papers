/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalProjectionEndpointBounds

/-!
# High projection positions omit the two actual selected endpoint strips

Supports `shields-2026-skew-corner-descent.tex` (`prop:closure-pin`).
Produced original selected-span bounds put the high intermediate position
strictly outside both proper selected strips. Their proper-core weights are
therefore zero there, including selected rows with empty proper cores.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A high projection position is below every first selected-strip column,
so its complete proper incoming core weight vanishes. -/
theorem original_first_strip_core_projection_zero {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hsame : interiorBlock P j.1.val = interiorBlock P b.val.val)
    (p : ℕ+) (hp : c.top < p) :
    let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
    (c.selectedCoreLeftPolynomial Q (originalSelectedProfile_schur P b).symm).toLaurent.coeff
      (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) - (p : ℤ) -
        originalResponseCols P j) = 0 := by
  let Q := interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property)
  have hQ : cellSchur D hD.1 = Q.schur := (originalSelectedProfile_schur P b).symm
  have hc := c.original_removed_col_ge_selected_left P b j hsame
  have hpn : (c.top : ℤ) < (p : ℤ) := by exact_mod_cast hp
  have hz : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) - (p : ℤ) -
      originalResponseCols P j < 0 := by omega
  dsimp only
  rw [c.selected_core_left_toLaurent Q hQ]
  exact endpointProfile_coeff_negative _ _
    (fun i => (c.selected_core_left_distances Q hQ i).1.le) _ hz

/-- The symmetric high position is above every last selected-strip row,
so its complete proper outgoing core weight vanishes. -/
theorem original_last_strip_core_projection_zero {n : ℕ} (P : Profile n)
    (d : OriginalSelectedBlocks (hD := hD) P) (j : OriginalRemainingIndices (hD := hD) P)
    (hsame : interiorBlock P j.1.val = interiorBlock P d.val.val)
    (q : ℕ+) (hq : c.top < q) :
    let Q := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
    (c.selectedCoreRightPolynomial Q (originalSelectedProfile_schur P d).symm).toLaurent.coeff
      (originalResponseRows P j -
        (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) + (q : ℤ))) = 0 := by
  let Q := interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property)
  have hQ : cellSchur D hD.1 = Q.schur := (originalSelectedProfile_schur P d).symm
  have hr := c.original_removed_row_le_selected_right P d j hsame
  have hqn : (c.top : ℤ) < (q : ℤ) := by exact_mod_cast hq
  have hz : originalResponseRows P j -
      (P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) + (q : ℤ)) < 0 := by omega
  dsimp only
  rw [c.selected_core_right_toLaurent Q hQ]
  exact endpointProfile_coeff_negative _ _
    (fun i => (c.selected_core_right_distances Q hQ i).1.le) _ hz

end SkewCornerDescent.Matrix.SelectedCoordinate
