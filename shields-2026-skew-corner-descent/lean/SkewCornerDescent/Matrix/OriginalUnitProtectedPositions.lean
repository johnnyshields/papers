/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitEffectiveCoordinates
import SkewCornerDescent.Matrix.OriginalSelectedStripBounds
import SkewCornerDescent.Matrix.OriginalBlockSpanCoordinates

/-!
# Protected high positions of complete original unit components

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Actual selected endpoints and component order supply the high-distance inputs
of effective-coordinate recovery. No high-position inequality is assumed.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A complete nonselected component after a selected source endpoint has every
incoming column position strictly above the selected generator. -/
theorem original_unit_incoming_positions_high {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P) (b : OriginalBlocks P)
    (hab : interiorBlock P a.val.val < interiorBlock P b.val)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ)
    (i : Fin (interiorBlockLength P b.val + 1)) :
    (c.top : ℤ) < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
      ((interiorBlockProfile P b.val hne).zeta i + originalComponentTau P b) := by
  let Q := interiorBlockProfile P b.val hne
  have h := c.original_row_distance_gt_top_of_later_block P a
    ⟨b, originalUnitIndex P b hs i⟩ hab
  change (c.top : ℤ) < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
    P.xi (originalRemovedRow (hD := hD) P b (originalUnitIndex P b hs i)).succ at h
  rw [(original_unit_component_beta P b hs hne i).1] at h
  change (c.top : ℤ) < P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
    (Q.xi i + originalComponentTau P b) at h
  have hp := Q.r_pos i
  have he := Q.xi_sub_zeta i
  change 0 < (Q.r i : ℕ) at hp
  change Q.xi i - Q.zeta i = (Q.r i : ℤ) at he
  change (c.top : ℤ) < _ - (Q.zeta i + _)
  omega

/-- A complete nonselected component before a selected source endpoint has every
outgoing row position strictly above the selected generator. -/
theorem original_unit_outgoing_positions_high {n : ℕ} (P : Profile n)
    (b : OriginalBlocks P) (d : OriginalSelectedBlocks (hD := hD) P)
    (hbd : interiorBlock P b.val < interiorBlock P d.val.val)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ)
    (i : Fin (interiorBlockLength P b.val + 1)) :
    (c.top : ℤ) < (interiorBlockProfile P b.val hne).xi i + originalComponentTau P b -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) := by
  let Q := interiorBlockProfile P b.val hne
  have h := c.original_col_distance_gt_top_of_earlier_block P d
    ⟨b, originalUnitIndex P b hs i⟩ hbd
  change (c.top : ℤ) <
    P.zeta (originalRemovedCol (hD := hD) P b (originalUnitIndex P b hs i)).castSucc -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) at h
  rw [(original_unit_component_beta P b hs hne i).2] at h
  change (c.top : ℤ) < Q.zeta i + originalComponentTau P b -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) at h
  have hp := Q.r_pos i
  have he := Q.xi_sub_zeta i
  change 0 < (Q.r i : ℕ) at hp
  change Q.xi i - Q.zeta i = (Q.r i : ℤ) at he
  change (c.top : ℤ) < Q.xi i + _ - _
  omega

/-- The original maximal-component assumption supplies the normalized full unit
component's span bound. It is not a separate assumption of endpoint recovery. -/
theorem original_unit_component_top_le {n : ℕ} (P : Profile n) (b : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P b)
    (hne : P.zeta b.val.castSucc < P.xi b.val.succ)
    (hmax : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ)) :
    (interiorBlockProfile P b.val hne).topVar ≤ c.top := by
  let Q := interiorBlockProfile P b.val hne
  let i := originalRemovedCol (hD := hD) P b (originalUnitIndex P b hs (Fin.last _))
  let j := originalRemovedRow (hD := hD) P b (originalUnitIndex P b hs 0)
  have he : interiorBlock P j = interiorBlock P i := by
    rw [originalRemovedRow_block, originalRemovedCol_block]
  have h := interior_same_block_entry_span_le P (c.top : ℕ) hmax i j he
  change P.xi j.succ - P.zeta i.castSucc ≤ (c.top : ℤ) at h
  dsimp only [i, j] at h
  rw [(original_unit_component_beta P b hs hne 0).1,
    (original_unit_component_beta P b hs hne (Fin.last _)).2] at h
  change Q.xi 0 + originalComponentTau P b -
    (Q.zeta (Fin.last _) + originalComponentTau P b) ≤ (c.top : ℤ) at h
  rw [Q.zeta_last, zero_add, add_sub_cancel_right] at h
  rw [← Q.topVar_coe] at h
  exact_mod_cast h

end SkewCornerDescent.Matrix.SelectedCoordinate
