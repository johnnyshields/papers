/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalBlockOrder
import SkewCornerDescent.Matrix.OriginalVisibleEmptyRecovery
import SkewCornerDescent.Matrix.OriginalPairedPrefixEquiv

/-!
# Actual suffix points from later reconstructed components

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
The terminal proper strip, later positive components and the visible
empty-pivot producer supply every actual suffix point.  Later positive
components remain the well-founded reconstruction input.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Previously recovered positive units, the reconstructed terminal strip,
and the visible empty-pivot producer supply every actual suffix point. -/
theorem original_right_suffix_point_matches {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (hvint : originalResponseLowerCut Q (some (originalSelectedEnumeration Q i')) <
        (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q
        (some (originalSelectedEnumeration Q t')))
    (hband : 2 * (originalComponentTau P u -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t))))) < K)
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
    (∃ e : Fin (originalRemovedSize (hD := hD) P b.val) ≃
        Fin (originalRemovedSize (hD := hD) Q b'.val),
      ∀ k, originalRemainingRowBeta Q ⟨b'.val, e k⟩ =
          originalRemainingRowBeta P ⟨b.val, k⟩ + shift ∧
        originalRemainingColBeta Q ⟨b'.val, e k⟩ =
          originalRemainingColBeta P ⟨b.val, k⟩ + shift) →
    (∀ w : OriginalBlocks P, u < w →
      ¬ originalBlockSelected (hD := hD) P w →
      P.zeta w.val.castSucc < P.xi w.val.succ →
      (originalResponseLowerCut P (some a) < (interiorBlock P w.val : ℤ) ∧
        (interiorBlock P w.val : ℤ) < originalResponseUpperCut P (some b)) →
      ∃ z : OriginalBlocks Q, ¬ originalBlockSelected (hD := hD) Q z ∧
        (originalResponseLowerCut Q (some a') < (interiorBlock Q z.val : ℤ) ∧
          (interiorBlock Q z.val : ℤ) < originalResponseUpperCut Q (some b')) ∧
        ∃ e : Fin (originalRemovedSize (hD := hD) P w) ≃
            Fin (originalRemovedSize (hD := hD) Q z),
          ∀ k, originalRemainingRowBeta Q ⟨z, e k⟩ =
              originalRemainingRowBeta P ⟨w, k⟩ + shift ∧
            originalRemainingColBeta Q ⟨z, e k⟩ =
              originalRemainingColBeta P ⟨w, k⟩ + shift) →
    ∀ k : OriginalIntervalUnitSuffix (hD := hD) P (some a) (some b) u,
      ∃ l : OriginalIntervalUnitSuffix (hD := hD) Q (some a') (some b') v,
        originalResponseRows Q l.1.1.1 = originalResponseRows P k.1.1.1 + shift ∧
        originalResponseCols Q l.1.1.1 = originalResponseCols P k.1.1.1 + shift := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let shift := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  dsimp only
  intro hselected hprior k
  have hvisible : 2 * (originalResponseCols P k.1.1.1 -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))) < K := by
    have horder := original_remaining_col_block_strict P u k.1.1.1.1 k.2
      (originalUnitIndex P u hu (Fin.last _)) k.1.1.1.2
    have hlast : originalRemainingColBeta P ⟨u, originalUnitIndex P u hu (Fin.last _)⟩ =
        originalComponentTau P u := by
      change P.zeta (originalRemovedCol P u (originalUnitIndex P u hu (Fin.last _))).castSucc = _
      rw [originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last]
      rfl
    rw [hlast] at horder
    change originalResponseCols P k.1.1.1 < originalComponentTau P u at horder
    dsimp only [b] at *
    omega
  have hcase := c.original_consecutive_visible_col_cases P i t ht k.1
    (by rw [hKP]; exact hK) (by rw [hKP]; exact hvisible)
  have hafter := (original_interval_unit_between Q a' b' v hv hvint).2
  rcases k with ⟨⟨⟨⟨w, kk⟩, hwupper⟩, hwlower⟩, huw⟩
  rcases hcase with hsel | hns
  · change w = b.val at hsel
    subst w
    obtain ⟨e, he⟩ := hselected
    let q := originalSelectedEndIntervalIndex Q a' b'
      (original_consecutive_endpoint_label_le Q i' t' ht') (e kk)
    exact ⟨⟨q, hafter⟩, he kk⟩
  · change ¬ originalBlockSelected (hD := hD) P w at hns
    have hpair : ∃ z : OriginalBlocks Q, ¬ originalBlockSelected (hD := hD) Q z ∧
        (originalResponseLowerCut Q (some a') < (interiorBlock Q z.val : ℤ) ∧
          (interiorBlock Q z.val : ℤ) < originalResponseUpperCut Q (some b')) ∧
        ∃ e : Fin (originalRemovedSize (hD := hD) P w) ≃
            Fin (originalRemovedSize (hD := hD) Q z),
          ∀ k, originalRemainingRowBeta Q ⟨z, e k⟩ =
              originalRemainingRowBeta P ⟨w, k⟩ + shift ∧
            originalRemainingColBeta Q ⟨z, e k⟩ =
              originalRemainingColBeta P ⟨w, k⟩ + shift := by
      by_cases hne : P.zeta w.val.castSucc < P.xi w.val.succ
      · exact hprior w huw hns hne ⟨hwlower, hwupper⟩
      · have hempty : P.xi w.val.succ = P.zeta w.val.castSucc :=
          le_antisymm (le_of_not_gt hne) (P.zeta_le_xi_succ _)
        let p : OriginalResponseInterval (hD := hD) P (some a) (some b) :=
          ⟨⟨⟨w, kk⟩, hwupper⟩, hwlower⟩
        obtain ⟨q, hqempty, e, he⟩ := c.original_visible_outgoing_empty_recovery
          P Q i t i' t' ht' K hK hKQ hmaxP hmaxQ hcoeff p hempty hvisible
        exact ⟨q.1.1.1, not_dvd_originalEmptyBlock (hD := hD) Q q.1.1.1.val hqempty,
          ⟨q.2, q.1.2⟩, e, he⟩
    obtain ⟨z, hz, hzint, e, he⟩ := hpair
    have htop := original_unit_row_top_of_endpoint_equiv P Q w z hns hz shift e
      (fun k => (he k).1)
    have horder := original_unit_row_top_strict P u w hu hns huw
    have hvz : v < z := (original_unit_lt_iff_row_top Q v z hv hz).mpr (by
      change P.xi (interiorBlockFirst P u.val).succ -
          P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) =
        Q.xi (interiorBlockFirst Q v.val).succ -
          Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))) at hgroup
      dsimp only [shift] at htop
      omega)
    let q : OriginalResponseInterval (hD := hD) Q (some a') (some b') :=
      ⟨⟨⟨z, e kk⟩, hzint.2⟩, hzint.1⟩
    exact ⟨⟨q, hvz⟩, he kk⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
