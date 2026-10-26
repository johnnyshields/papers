/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIntervalBlockOrder
import SkewCornerDescent.Matrix.OriginalVisibleEmptyRecovery
import SkewCornerDescent.Matrix.OriginalPairedPrefixEquiv

/-!
# Actual prefix points from earlier reconstructed components

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
The initial proper strip, previously recovered positive components and the
visible empty-pivot producer supply the actual prefix point matches.
Earlier positive components remain the well-founded induction input.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Previously recovered positive units, the reconstructed starting strip,
and the visible empty-pivot producer supply every actual prefix point. -/
theorem original_left_prefix_point_matches {n m : ℕ} (P : Profile n) (Q : Profile m)
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
      (c.originalResidueLeftEndpointPolynomial P
        (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t))).coeff w =
      (c.originalResidueLeftEndpointPolynomial Q
        (some (originalSelectedEnumeration Q i'))
        (some (originalSelectedEnumeration Q t'))).coeff w)
    (u : OriginalBlocks P) (v : OriginalBlocks Q)
    (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hv : ¬ originalBlockSelected (hD := hD) Q v)
    (hvint : originalResponseLowerCut Q (some (originalSelectedEnumeration Q i')) <
        (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q
        (some (originalSelectedEnumeration Q t')))
    (hband : 2 * (P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration P i)))) -
        P.xi (interiorBlockFirst P u.val).succ) < K)
    (hgroup : P.xi (originalRowSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P i)))) - originalComponentTau P u =
      Q.xi (originalRowSplitEquiv (hD := hD) Q
          (.inl (some (originalSelectedEnumeration Q i')))) - originalComponentTau Q v) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P t
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    (∃ e : Fin (originalRemovedSize (hD := hD) P a.val) ≃
        Fin (originalRemovedSize (hD := hD) Q a'.val),
      ∀ k, originalRemainingRowBeta Q ⟨a'.val, e k⟩ =
          originalRemainingRowBeta P ⟨a.val, k⟩ + shift ∧
        originalRemainingColBeta Q ⟨a'.val, e k⟩ =
          originalRemainingColBeta P ⟨a.val, k⟩ + shift) →
    (∀ w : OriginalBlocks P, w < u →
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
    ∀ k : OriginalIntervalUnitPrefix (hD := hD) P (some a) (some b) u,
      ∃ l : OriginalIntervalUnitPrefix (hD := hD) Q (some a') (some b') v,
        originalResponseRows Q l.1.1.1 = originalResponseRows P k.1.1.1 + shift ∧
        originalResponseCols Q l.1.1.1 = originalResponseCols P k.1.1.1 + shift := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  dsimp only
  intro hselected hprior k
  have hvisible : 2 * (P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
      originalResponseRows P k.1.1.1) < K := by
    have horder := original_remaining_row_block_strict P k.1.1.1.1 u k.2
      k.1.1.1.2 (originalUnitIndex P u hu 0)
    have hzero : originalRemainingRowBeta P ⟨u, originalUnitIndex P u hu 0⟩ =
        P.xi (interiorBlockFirst P u.val).succ := by
      change P.xi (originalRemovedRow P u (originalUnitIndex P u hu 0)).succ = _
      rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first]
    rw [hzero] at horder
    change P.xi (interiorBlockFirst P u.val).succ < originalResponseRows P k.1.1.1 at horder
    dsimp only [a] at *
    omega
  have hcase := c.original_consecutive_visible_row_cases P i t ht k.1
    (by rw [hKP]; exact hK) (by rw [hKP]; exact hvisible)
  have hbefore := (original_interval_unit_between Q a' b' v hv hvint).1
  rcases k with ⟨⟨⟨⟨w, kk⟩, hwupper⟩, hwlower⟩, hwu⟩
  rcases hcase with hsel | hns
  · change w = a.val at hsel
    subst w
    obtain ⟨e, he⟩ := hselected
    let q := originalSelectedStartIntervalIndex Q a' b'
      (original_consecutive_endpoint_label_le Q i' t' ht') (e kk)
    exact ⟨⟨q, hbefore⟩, he kk⟩
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
      · exact hprior w hwu hns hne ⟨hwlower, hwupper⟩
      · have hempty : P.xi w.val.succ = P.zeta w.val.castSucc :=
          le_antisymm (le_of_not_gt hne) (P.zeta_le_xi_succ _)
        let p : OriginalResponseInterval (hD := hD) P (some a) (some b) :=
          ⟨⟨⟨w, kk⟩, hwupper⟩, hwlower⟩
        obtain ⟨q, hqempty, e, he⟩ := c.original_visible_incoming_empty_recovery
          P Q i t i' t' ht' K hK hKQ hmaxP hmaxQ hcoeff p hempty hvisible
        exact ⟨q.1.1.1, not_dvd_originalEmptyBlock (hD := hD) Q q.1.1.1.val hqempty,
          ⟨q.2, q.1.2⟩, e, he⟩
    obtain ⟨z, hz, hzint, e, he⟩ := hpair
    have hτ := original_unit_tau_of_endpoint_equiv P Q w z hns hz shift e (fun k => (he k).2)
    have hτorder := original_unit_tau_strict P w u hns hu hwu
    have hzv : z < v := (original_unit_lt_iff_tau Q z v hz hv).mpr (by
      change P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
          originalComponentTau P u =
        Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
          originalComponentTau Q v at hgroup
      dsimp only [shift] at hτ
      omega)
    let q : OriginalResponseInterval (hD := hD) Q (some a') (some b') :=
      ⟨⟨⟨z, e kk⟩, hzint.2⟩, hzint.1⟩
    exact ⟨⟨q, hzv⟩, he kk⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
