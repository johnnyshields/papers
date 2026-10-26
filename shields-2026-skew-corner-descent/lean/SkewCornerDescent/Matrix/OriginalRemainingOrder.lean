/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitBoundaryOrder
import SkewCornerDescent.Matrix.OriginalIntervalUnitComponents

/-!
# Strict original point order and paired-component boundary recovery

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Actual block order makes every preceding or following point strictly visible
in the appropriate whole-component regime.  Full paired copying recovers the
least-column shift without presuming that its finite equivalence is ordered.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- Earlier original blocks have strictly greater retained rows, even when
one block is selected and only its proper strip remains. -/
theorem original_remaining_row_block_strict {n : ℕ} (P : Profile n)
    (u v : OriginalBlocks P) (huv : u < v)
    (i : Fin (originalRemovedSize (hD := hD) P u))
    (j : Fin (originalRemovedSize (hD := hD) P v)) :
    originalRemainingRowBeta P ⟨v, j⟩ < originalRemainingRowBeta P ⟨u, i⟩ := by
  change P.xi (originalRemovedRow P v j).succ < P.xi (originalRemovedRow P u i).succ
  apply P.xi_strictAnti
  change (originalRemovedRow P u i).val + 1 < (originalRemovedRow P v j).val + 1
  have hh : originalRemovedRow P u i < originalRemovedRow P v j := by
    by_contra hnot
    have hle := interiorBlock_mono P (le_of_not_gt hnot)
    rw [originalRemovedRow_block P v j, originalRemovedRow_block P u i] at hle
    have hlt := originalBlocks_label_strictMono P huv
    change interiorBlock P u.val < interiorBlock P v.val at hlt
    omega
  exact Nat.add_lt_add_right (Fin.lt_def.mp hh) 1

/-- The corresponding strict order of retained columns includes empty pivots
and both selected proper strips. -/
theorem original_remaining_col_block_strict {n : ℕ} (P : Profile n)
    (u v : OriginalBlocks P) (huv : u < v)
    (i : Fin (originalRemovedSize (hD := hD) P u))
    (j : Fin (originalRemovedSize (hD := hD) P v)) :
    originalRemainingColBeta P ⟨v, j⟩ < originalRemainingColBeta P ⟨u, i⟩ := by
  change P.zeta (originalRemovedCol P v j).castSucc < P.zeta (originalRemovedCol P u i).castSucc
  apply P.zeta_strictAnti
  change (originalRemovedCol P u i).val < (originalRemovedCol P v j).val
  have hh : originalRemovedCol P u i < originalRemovedCol P v j := by
    by_contra hnot
    have hle := interiorBlock_mono P (le_of_not_gt hnot)
    rw [originalRemovedCol_block P v j, originalRemovedCol_block P u i] at hle
    have hlt := originalBlocks_label_strictMono P huv
    change interiorBlock P u.val < interiorBlock P v.val at hlt
    omega
  exact Fin.lt_def.mp hh

/-- Every point in the prefix of a wholly left-of-midpoint positive unit
is strictly visible.  The current least column may be exactly at midpoint. -/
theorem original_left_unit_prefix_visible {n : ℕ} (P : Profile n)
    (a b : Option (OriginalSelectedBlocks (hD := hD) P))
    (u : OriginalBlocks P) (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (x K : ℤ) (hband : 2 * (x - originalComponentTau P u) ≤ K)
    (k : OriginalIntervalUnitPrefix (hD := hD) P a b u) :
    2 * (x - originalResponseRows P k.1.1.1) < K := by
  have hgt := original_unit_row_gt_tau P u hu hne (originalUnitIndex P u hu 0)
  have horder := original_remaining_row_block_strict P k.1.1.1.1 u k.2
    k.1.1.1.2 (originalUnitIndex P u hu 0)
  change originalRemainingRowBeta P ⟨u, originalUnitIndex P u hu 0⟩ <
    originalResponseRows P k.1.1.1 at horder
  omega

/-- Every suffix point of a wholly right-of-midpoint positive unit is
strictly visible in the outgoing profile. -/
theorem original_right_unit_suffix_visible {n : ℕ} (P : Profile n)
    (a b : Option (OriginalSelectedBlocks (hD := hD) P))
    (u : OriginalBlocks P) (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ)
    (y K : ℤ) (hband : 2 * (P.xi (interiorBlockFirst P u.val).succ - y) ≤ K)
    (k : OriginalIntervalUnitSuffix (hD := hD) P a b u) :
    2 * (originalResponseCols P k.1.1.1 - y) < K := by
  have hlt := original_unit_col_lt_row_top P u hu hne (originalUnitIndex P u hu (Fin.last _))
  have horder := original_remaining_col_block_strict P u k.1.1.1.1 k.2
    (originalUnitIndex P u hu (Fin.last _)) k.1.1.1.2
  change originalResponseCols P k.1.1.1 <
    originalRemainingColBeta P ⟨u, originalUnitIndex P u hu (Fin.last _)⟩ at horder
  omega

/-- A full paired endpoint copy determines the actual least-column shift.
The proof uses both extreme columns and surjectivity, not a chosen ordering
of the finite equivalence. -/
theorem original_unit_tau_of_endpoint_equiv {n m : ℕ} (P : Profile n) (Q : Profile m)
    (u : OriginalBlocks P) (v : OriginalBlocks Q)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) Q v) (shift : ℤ)
    (e : Fin (originalRemovedSize (hD := hD) P u) ≃
      Fin (originalRemovedSize (hD := hD) Q v))
    (hc : ∀ k, originalRemainingColBeta Q ⟨v, e k⟩ =
      originalRemainingColBeta P ⟨u, k⟩ + shift) :
    originalComponentTau Q v = originalComponentTau P u + shift := by
  let p := originalUnitIndex P u hu (Fin.last _)
  let q := originalUnitIndex Q v hv (Fin.last _)
  have hp : originalRemainingColBeta P ⟨u, p⟩ = originalComponentTau P u := by
    change P.zeta (originalRemovedCol P u (originalUnitIndex P u hu (Fin.last _))).castSucc = _
    rw [originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last]
    rfl
  have hq : originalRemainingColBeta Q ⟨v, q⟩ = originalComponentTau Q v := by
    change Q.zeta (originalRemovedCol Q v (originalUnitIndex Q v hv (Fin.last _))).castSucc = _
    rw [originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last]
    rfl
  have hforward := original_remaining_col_ge_tau Q ⟨v, e p⟩
  have hback := original_remaining_col_ge_tau P ⟨u, e.symm q⟩
  change originalComponentTau Q v ≤ originalRemainingColBeta Q ⟨v, e p⟩ at hforward
  change originalComponentTau P u ≤ originalRemainingColBeta P ⟨u, e.symm q⟩ at hback
  have heP := hc p
  have heQ := hc (e.symm q)
  rw [hp] at heP
  rw [e.apply_symm_apply, hq] at heQ
  omega

/-- Least-column order reflects the complete original block order among
nonselected components, including empty pivots. -/
theorem original_unit_lt_iff_tau {n : ℕ} (P : Profile n)
    (u v : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) P v) :
    u < v ↔ originalComponentTau P v < originalComponentTau P u := by
  constructor
  · exact original_unit_tau_strict P u v hu hv
  · intro h
    rcases lt_trichotomy u v with hlt | he | hgt
    · exact hlt
    · rw [he] at h
      exact (lt_irrefl _ h).elim
    · have hh := original_unit_tau_strict P v u hv hu hgt
      omega

/-- Full paired endpoint copying also determines the actual greatest-row
shift.  Both extreme rows and surjectivity make ordering of the equivalence
unnecessary. -/
theorem original_unit_row_top_of_endpoint_equiv {n m : ℕ} (P : Profile n) (Q : Profile m)
    (u : OriginalBlocks P) (v : OriginalBlocks Q)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) Q v) (shift : ℤ)
    (e : Fin (originalRemovedSize (hD := hD) P u) ≃
      Fin (originalRemovedSize (hD := hD) Q v))
    (hr : ∀ k, originalRemainingRowBeta Q ⟨v, e k⟩ =
      originalRemainingRowBeta P ⟨u, k⟩ + shift) :
    Q.xi (interiorBlockFirst Q v.val).succ =
      P.xi (interiorBlockFirst P u.val).succ + shift := by
  let p := originalUnitIndex P u hu 0
  let q := originalUnitIndex Q v hv 0
  have hp : originalRemainingRowBeta P ⟨u, p⟩ =
      P.xi (interiorBlockFirst P u.val).succ := by
    change P.xi (originalRemovedRow P u (originalUnitIndex P u hu 0)).succ = _
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first]
  have hq : originalRemainingRowBeta Q ⟨v, q⟩ =
      Q.xi (interiorBlockFirst Q v.val).succ := by
    change Q.xi (originalRemovedRow Q v (originalUnitIndex Q v hv 0)).succ = _
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first]
  have hforward := original_remaining_row_le_block_top Q ⟨v, e p⟩
  have hback := original_remaining_row_le_block_top P ⟨u, e.symm q⟩
  change originalRemainingRowBeta Q ⟨v, e p⟩ ≤
    Q.xi (interiorBlockFirst Q v.val).succ at hforward
  change originalRemainingRowBeta P ⟨u, e.symm q⟩ ≤
    P.xi (interiorBlockFirst P u.val).succ at hback
  have heP := hr p
  have heQ := hr (e.symm q)
  rw [hp] at heP
  rw [e.apply_symm_apply, hq] at heQ
  omega

/-- Greatest-row order reflects the original order of full nonselected
blocks, including literal empty pivots. -/
theorem original_unit_lt_iff_row_top {n : ℕ} (P : Profile n)
    (u v : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) P v) :
    u < v ↔ P.xi (interiorBlockFirst P v.val).succ <
      P.xi (interiorBlockFirst P u.val).succ := by
  constructor
  · exact original_unit_row_top_strict P u v hu hv
  · intro h
    rcases lt_trichotomy u v with hlt | he | hgt
    · exact hlt
    · rw [he] at h
      exact (lt_irrefl _ h).elim
    · have hh := original_unit_row_top_strict P v u hv hu hgt
      omega

/-- A positive full unit has distinct least column and greatest row. -/
theorem original_unit_extremes_strict {n : ℕ} (P : Profile n) (u : OriginalBlocks P)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hne : P.zeta u.val.castSucc < P.xi u.val.succ) :
    originalComponentTau P u < P.xi (interiorBlockFirst P u.val).succ := by
  have hh := original_unit_row_gt_tau P u hu hne (originalUnitIndex P u hu 0)
  change originalComponentTau P u <
    P.xi (originalRemovedRow P u (originalUnitIndex P u hu 0)).succ at hh
  rwa [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first] at hh

end SkewCornerDescent.Matrix.SelectedCoordinate
