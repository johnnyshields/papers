/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRightUnitRecovery

/-!
# Complete visible original ordered copies

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Visible least columns and matching greatest-row groups produce both full
paired suffixes.  Later positive components are reconstructed by the closed
right-to-left induction; empty pivots and selected proper strips are retained.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Visible least columns and matching greatest-row groups determine the
whole paired suffixes.  Later positive components are reconstructed from
actual outgoing coefficients rather than assumed compatible. -/
theorem original_visible_unit_suffix_equiv {n m : ℕ} (P : Profile n) (Q : Profile m)
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + 1)
    (i' t' : Fin (originalSelectedCount (hD := hD) Q)) (ht' : t'.val = i'.val + 1)
    (K : ℤ) (hK : 2 * (c.top : ℤ) < K)
    (hKP : P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t)))) = K)
    (hKQ : Q.xi (originalRowSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q i')))) -
      Q.zeta (originalColSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q t')))) = K)
    (hmaxP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ))
    (hcoeff : ∀ w : ℕ, 2 * (w : ℤ) < K →
      (c.originalResidueRightEndpointPolynomial P
        (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t))).coeff w =
      (c.originalResidueRightEndpointPolynomial Q
        (some (originalSelectedEnumeration Q i'))
        (some (originalSelectedEnumeration Q t'))).coeff w)
    (u : OriginalBlocks P) (v : OriginalBlocks Q)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) Q v)
    (huint : originalResponseLowerCut P (some (originalSelectedEnumeration P i)) <
        (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P
        (some (originalSelectedEnumeration P t)))
    (hvint : originalResponseLowerCut Q (some (originalSelectedEnumeration Q i')) <
        (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q
        (some (originalSelectedEnumeration Q t')))
    (htailP : 2 * (originalComponentTau P u -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t))))) < K)
    (htailQ : 2 * (originalComponentTau Q v -
      Q.zeta (originalColSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q t'))))) < K)
    (hgroup : P.xi (interiorBlockFirst P u.val).succ -
        P.zeta (originalColSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P t)))) =
      Q.xi (interiorBlockFirst Q v.val).succ -
        Q.zeta (originalColSplitEquiv (hD := hD) Q
          (.inl (some (originalSelectedEnumeration Q t'))))) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P t
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let shift := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
    ∃ e : OriginalIntervalUnitSuffix (hD := hD) P (some a) (some b) u ≃
        OriginalIntervalUnitSuffix (hD := hD) Q (some a') (some b') v,
      ∀ k, originalResponseRows Q (e k).1.1.1 = originalResponseRows P k.1.1.1 + shift ∧
        originalResponseCols Q (e k).1.1.1 = originalResponseCols P k.1.1.1 + shift := by
  classical
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  let shift := y' - y
  have hc := c.original_selected_end_core_literal P Q a b a' b'
    (original_consecutive_endpoint_label_le P i t ht)
    (original_consecutive_endpoint_label_le Q i' t' ht') K hK hcoeff
  have hselected := original_selected_endpoint_equiv_of_end_core_cells P Q b b' hc shift
    (by dsimp only [shift]; omega)
  have hselected' := original_selected_endpoint_equiv_of_end_core_cells Q P b' b hc.symm (-shift)
    (by dsimp only [shift]; omega)
  have hf := c.original_right_suffix_point_matches P Q i t ht i' t' ht' K hK hKP hKQ
    hmaxP hmaxQ hcoeff u v hu hv hvint htailP hgroup hselected
  have hf' := c.original_right_suffix_point_matches Q P i' t' ht' i t ht K hK hKQ hKP
    hmaxQ hmaxP (fun w hw => (hcoeff w hw).symm) v u hv hu huint htailQ
    hgroup.symm (by simpa only [shift, neg_sub] using hselected')
  have hforward := hf (by
    intro w huw hw hwne hwint
    have hsep := original_remaining_beta_separated P w u huw
      (originalUnitIndex P w hw 0) (originalUnitIndex P u hu (Fin.last _))
    change P.xi (originalRemovedRow P w (originalUnitIndex P w hw 0)).succ <
      P.zeta (originalRemovedCol P u (originalUnitIndex P u hu (Fin.last _))).castSucc at hsep
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first,
      originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last] at hsep
    change P.xi (interiorBlockFirst P w.val).succ < originalComponentTau P u at hsep
    have hwband : 2 * (P.xi (interiorBlockFirst P w.val).succ - y) ≤ K := by
      dsimp only [y, b] at *
      omega
    obtain ⟨z, hz, _, hzint, e, he⟩ := c.original_right_unit_recovery P Q i t ht i' t' ht'
      K hK hKP hKQ hmaxP hmaxQ hcoeff w hw hwne hwint hwband
    exact ⟨z, hz, hzint, e, he⟩)
  have hbackward := hf' (by
    intro w hvw hw hwne hwint
    have hsep := original_remaining_beta_separated Q w v hvw
      (originalUnitIndex Q w hw 0) (originalUnitIndex Q v hv (Fin.last _))
    change Q.xi (originalRemovedRow Q w (originalUnitIndex Q w hw 0)).succ <
      Q.zeta (originalRemovedCol Q v (originalUnitIndex Q v hv (Fin.last _))).castSucc at hsep
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first,
      originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last] at hsep
    change Q.xi (interiorBlockFirst Q w.val).succ < originalComponentTau Q v at hsep
    have hwband : 2 * (Q.xi (interiorBlockFirst Q w.val).succ - y') ≤ K := by
      dsimp only [y', b'] at *
      omega
    obtain ⟨z, hz, _, hzint, e, he⟩ := c.original_right_unit_recovery Q P i' t' ht' i t ht
      K hK hKQ hKP hmaxQ hmaxP (fun w hw => (hcoeff w hw).symm) w hw hwne hwint hwband
    exact ⟨z, hz, hzint, e, he⟩)
  apply original_interval_suffix_equiv_of_matches P Q (some a) (some b) u
    (some a') (some b') v shift hforward
  intro j
  obtain ⟨k, hr, hc⟩ := hbackward j
  refine ⟨k, ?_, ?_⟩ <;> dsimp only [shift, y, y', b, b'] at * <;> omega

end SkewCornerDescent.Matrix.SelectedCoordinate
