/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitComponentOrder
import SkewCornerDescent.Matrix.OriginalBlockField

/-!
# Literal boundary order of complete original unit blocks

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Actual least columns and greatest rows strictly order all nonselected blocks,
including empty pivots. For a positive-span block, every original row lies
above its least column and every original column below its greatest row.
These bounds supply complete-block visibility without a geometric model input.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

private theorem component_lower_le_upper {n : ℕ} (P : Profile n) (u : OriginalBlocks P) :
    originalComponentTau P u ≤ P.xi (interiorBlockFirst P u.val).succ := by
  have hc := P.zeta_le_xi_succ (interiorBlockLast P u.val)
  have hi := interiorBlockFirst_le_last P u.val
  have hr := P.xi_strictAnti.antitone
    (show (interiorBlockFirst P u.val).succ ≤ (interiorBlockLast P u.val).succ from by
      change (interiorBlockFirst P u.val).val + 1 ≤ (interiorBlockLast P u.val).val + 1
      exact Nat.add_le_add_right hi 1)
  exact hc.trans hr

private theorem unit_extreme_separation {n : ℕ} (P : Profile n) (u v : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) P v) (huv : u < v) :
    P.xi (interiorBlockFirst P v.val).succ < originalComponentTau P u := by
  have h := original_remaining_beta_separated (hD := hD) P v u huv
    (originalUnitIndex P v hv 0) (originalUnitIndex P u hu (Fin.last _))
  change P.xi (originalRemovedRow P v (originalUnitIndex P v hv 0)).succ <
    P.zeta (originalRemovedCol P u (originalUnitIndex P u hu (Fin.last _))).castSucc at h
  rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first,
    originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last] at h
  exact h

/-- Actual least columns decrease strictly across complete nonselected blocks,
including literal empty pivots. -/
theorem original_unit_tau_strict {n : ℕ} (P : Profile n) (u v : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) P v) (huv : u < v) :
    originalComponentTau P v < originalComponentTau P u :=
  lt_of_le_of_lt (component_lower_le_upper P v) (unit_extreme_separation P u v hu hv huv)

/-- Actual greatest rows also decrease strictly across the complete unit blocks. -/
theorem original_unit_row_top_strict {n : ℕ} (P : Profile n) (u v : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) P v) (huv : u < v) :
    P.xi (interiorBlockFirst P v.val).succ < P.xi (interiorBlockFirst P u.val).succ :=
  lt_of_lt_of_le (unit_extreme_separation P u v hu hv huv) (component_lower_le_upper P u)

/-- One actual least-column coordinate identifies the entire original unit block. -/
theorem original_unit_tau_injective {n : ℕ} (P : Profile n) (u v : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) P v)
    (he : originalComponentTau P u = originalComponentTau P v) : u = v := by
  rcases lt_trichotomy u v with h | h | h
  · have hh := original_unit_tau_strict P u v hu hv h
    omega
  · exact h
  · have hh := original_unit_tau_strict P v u hv hu h
    omega

/-- One actual greatest-row coordinate likewise identifies the original unit block. -/
theorem original_unit_row_top_injective {n : ℕ} (P : Profile n) (u v : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) P v)
    (he : P.xi (interiorBlockFirst P u.val).succ =
      P.xi (interiorBlockFirst P v.val).succ) : u = v := by
  rcases lt_trichotomy u v with h | h | h
  · have hh := original_unit_row_top_strict P u v hu hv h
    omega
  · exact h
  · have hh := original_unit_row_top_strict P v u hv hu h
    omega

/-- Every original row of a positive-span unit component lies strictly above
its actual least column. This supplies whole-block incoming visibility. -/
theorem original_unit_row_gt_tau {n : ℕ} (P : Profile n) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (k : Fin (originalRemovedSize (hD := hD) P u)) :
    originalComponentTau P u < originalRemainingRowBeta P ⟨u, k⟩ := by
  classical
  have hsize : originalRemovedSize (hD := hD) P u = interiorBlockLength P u.val + 1 := by
    simp only [originalRemovedSize, ite_eq_right hs]
  let j := Fin.cast hsize k
  have hk : originalUnitIndex P u hs j = k := by
    apply Fin.ext
    rfl
  have he := (original_unit_component_beta P u hs hne j).1
  rw [hk] at he
  have hp := (interiorBlockProfile P u.val hne).xi_pos j
  change originalComponentTau P u < P.xi (originalRemovedRow P u k).succ
  rw [he]
  omega

/-- Every original column of a positive-span unit component lies strictly
below its actual greatest row, supplying whole-block outgoing visibility. -/
theorem original_unit_col_lt_row_top {n : ℕ} (P : Profile n) (u : OriginalBlocks P)
    (hs : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (k : Fin (originalRemovedSize (hD := hD) P u)) :
    originalRemainingColBeta P ⟨u, k⟩ < P.xi (interiorBlockFirst P u.val).succ := by
  classical
  have hsize : originalRemovedSize (hD := hD) P u = interiorBlockLength P u.val + 1 := by
    simp only [originalRemovedSize, ite_eq_right hs]
  let j := Fin.cast hsize k
  have hk : originalUnitIndex P u hs j = k := by
    apply Fin.ext
    rfl
  have he := (original_unit_component_beta P u hs hne j).2
  rw [hk] at he
  have hTop := (original_unit_component_beta P u hs hne 0).1
  rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first] at hTop
  have hz := (interiorBlockProfile P u.val hne).zeta_strictAnti.antitone (Fin.zero_le j)
  have hp := (interiorBlockProfile P u.val hne).r_pos 0
  have hr := (interiorBlockProfile P u.val hne).xi_sub_zeta 0
  change P.zeta (originalRemovedCol P u k).castSucc <
    P.xi (interiorBlockFirst P u.val).succ
  rw [he, hTop]
  omega

/-- Every retained original row lies below its own block's greatest row,
including selected proper strips and empty unit pivots. -/
theorem original_remaining_row_le_block_top {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) :
    originalRemainingRowBeta P j ≤ P.xi (interiorBlockFirst P j.1.val).succ := by
  change P.xi (originalRemovedRow P j.1 j.2).succ ≤ _
  apply P.xi_strictAnti.antitone
  change (interiorBlockFirst P j.1.val).val + 1 ≤
    (originalRemovedRow P j.1 j.2).val + 1
  simp only [originalRemovedRow, interiorSliceIndex]
  omega

/-- Every retained original column lies above its own block's least column. -/
theorem original_remaining_col_ge_tau {n : ℕ} (P : Profile n)
    (j : OriginalRemainingIndices (hD := hD) P) :
    originalComponentTau P j.1 ≤ originalRemainingColBeta P j := by
  change P.zeta (interiorBlockLast P j.1.val).castSucc ≤
    P.zeta (originalRemovedCol P j.1 j.2).castSucc
  apply P.zeta_strictAnti.antitone
  change (originalRemovedCol P j.1 j.2).val ≤ (interiorBlockLast P j.1.val).val
  have hp := (originalRemovedColPosition P j.1 j.2).isLt
  have hle := interiorBlockFirst_le_last P j.1.val
  simp only [originalRemovedCol, interiorSliceIndex]
  dsimp only [interiorBlockLength] at hp
  omega

/-- At most one complete unit block straddles a prescribed half-integer
midpoint.  Doubling the coordinates avoids an unjustified integer rounding
when the interval height is odd. -/
theorem original_unit_half_midpoint_unique {n : ℕ} (P : Profile n)
    (u v : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) P v) (mid2 : ℤ)
    (huLeft : 2 * originalComponentTau P u < mid2)
    (huRight : mid2 < 2 * P.xi (interiorBlockFirst P u.val).succ)
    (hvLeft : 2 * originalComponentTau P v < mid2)
    (hvRight : mid2 < 2 * P.xi (interiorBlockFirst P v.val).succ) : u = v := by
  rcases lt_trichotomy u v with h | h | h
  · have hs := unit_extreme_separation P u v hu hv h
    omega
  · exact h
  · have hs := unit_extreme_separation P v u hv hu h
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
