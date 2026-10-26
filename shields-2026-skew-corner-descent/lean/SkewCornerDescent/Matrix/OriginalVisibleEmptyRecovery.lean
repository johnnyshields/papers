/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVisibleBlockMatching
import SkewCornerDescent.Matrix.OriginalUnitBoundaryOrder
import SkewCornerDescent.Matrix.OriginalWindowUnitBlocks

/-!
# Literal recovery of visible original empty pivots

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
A visible incoming or outgoing empty pivot matches a literal empty target
block and its complete paired endpoint list, without a known prefix or suffix.
The strict half-height visibility excludes the unresolved midpoint pivot.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A visible literal empty pivot matches another literal empty pivot, with
its entire paired endpoint list.  Positive components are excluded by their
strict row-above-least-column inequality, not an inverse-entry assumption. -/
theorem original_visible_incoming_empty_recovery {n m : ℕ} (P : Profile n) (Q : Profile m)
    (i t : Fin (originalSelectedCount (hD := hD) P))
    (i' t' : Fin (originalSelectedCount (hD := hD) Q)) (ht' : t'.val = i'.val + 1)
    (K : ℤ) (hK : 2 * (c.top : ℤ) < K)
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
    (p : OriginalResponseInterval (hD := hD) P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t)))
    (hp : P.xi p.1.1.1.val.succ = P.zeta p.1.1.1.val.castSucc)
    (hvisible : 2 * (P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i)))) - originalResponseRows P p.1.1) < K) :
    let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q i')))) -
      P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i))))
    ∃ q : OriginalResponseInterval (hD := hD) Q
        (some (originalSelectedEnumeration Q i')) (some (originalSelectedEnumeration Q t')),
      Q.xi q.1.1.1.val.succ = Q.zeta q.1.1.1.val.castSucc ∧
      ∃ e : Fin (originalRemovedSize (hD := hD) P p.1.1.1) ≃
          Fin (originalRemovedSize (hD := hD) Q q.1.1.1),
        ∀ k, originalRemainingRowBeta Q ⟨q.1.1.1, e k⟩ =
            originalRemainingRowBeta P ⟨p.1.1.1, k⟩ + shift ∧
          originalRemainingColBeta Q ⟨q.1.1.1, e k⟩ =
            originalRemainingColBeta P ⟨p.1.1.1, k⟩ + shift := by
  have hpns := not_dvd_originalEmptyBlock (hD := hD) P p.1.1.1.val hp
  obtain ⟨q, hqns, hrow, htau⟩ := c.original_visible_incoming_block_match
    P Q i t i' t' ht' K hK hKQ hmaxP hmaxQ hcoeff p hpns hvisible
  have hpRow : originalResponseRows P p.1.1 = P.xi p.1.1.1.val.succ :=
    (originalEmptyBlock_remaining_endpoints P p.1.1.1 hp p.1.1.2).1
  have hpTau : originalComponentTau P p.1.1.1 = P.xi p.1.1.1.val.succ := by
    dsimp only [originalComponentTau]
    rw [(interior_empty_block_extremes P p.1.1.1.val hp).2, hp]
  have hqRow : originalResponseRows Q q.1.1 = originalComponentTau Q q.1.1.1 := by
    rw [hpRow] at hrow
    rw [hpTau] at htau
    omega
  have hq : Q.xi q.1.1.1.val.succ = Q.zeta q.1.1.1.val.castSucc := by
    by_contra hne
    have hpos : Q.zeta q.1.1.1.val.castSucc < Q.xi q.1.1.1.val.succ :=
      lt_of_le_of_ne (Q.zeta_le_xi_succ _) (Ne.symm hne)
    have hgt := original_unit_row_gt_tau Q q.1.1.1 hqns hpos q.1.1.2
    change originalComponentTau Q q.1.1.1 < originalResponseRows Q q.1.1 at hgt
    omega
  have hqRow' : originalResponseRows Q q.1.1 = Q.xi q.1.1.1.val.succ :=
    (originalEmptyBlock_remaining_endpoints Q q.1.1.1 hq q.1.1.2).1
  rw [hpRow, hqRow'] at hrow
  refine ⟨q, hq, ?_⟩
  apply originalEmptyBlock_translated_endpoints P Q p.1.1.1 q.1.1.1 hp hq
  · omega
  · rw [← hp, ← hq]
    omega

/-- Outgoing visible coefficients recover an empty pivot's entire paired
endpoint list, with its literal empty status. -/
theorem original_visible_outgoing_empty_recovery {n m : ℕ} (P : Profile n) (Q : Profile m)
    (i t : Fin (originalSelectedCount (hD := hD) P))
    (i' t' : Fin (originalSelectedCount (hD := hD) Q)) (ht' : t'.val = i'.val + 1)
    (K : ℤ) (hK : 2 * (c.top : ℤ) < K)
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
    (p : OriginalResponseInterval (hD := hD) P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t)))
    (hp : P.xi p.1.1.1.val.succ = P.zeta p.1.1.1.val.castSucc)
    (hvisible : 2 * (originalResponseCols P p.1.1 -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t))))) < K) :
    let shift := Q.zeta (originalColSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q t')))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t))))
    ∃ q : OriginalResponseInterval (hD := hD) Q
        (some (originalSelectedEnumeration Q i')) (some (originalSelectedEnumeration Q t')),
      Q.xi q.1.1.1.val.succ = Q.zeta q.1.1.1.val.castSucc ∧
      ∃ e : Fin (originalRemovedSize (hD := hD) P p.1.1.1) ≃
          Fin (originalRemovedSize (hD := hD) Q q.1.1.1),
        ∀ k, originalRemainingRowBeta Q ⟨q.1.1.1, e k⟩ =
            originalRemainingRowBeta P ⟨p.1.1.1, k⟩ + shift ∧
          originalRemainingColBeta Q ⟨q.1.1.1, e k⟩ =
            originalRemainingColBeta P ⟨p.1.1.1, k⟩ + shift := by
  have hpns := not_dvd_originalEmptyBlock (hD := hD) P p.1.1.1.val hp
  obtain ⟨q, hqns, hcol, htop⟩ := c.original_visible_outgoing_block_match
    P Q i t i' t' ht' K hK hKQ hmaxP hmaxQ hcoeff p hpns hvisible
  have hpCol : originalResponseCols P p.1.1 = P.xi p.1.1.1.val.succ :=
    ((originalEmptyBlock_remaining_endpoints P p.1.1.1 hp p.1.1.2).2).trans hp.symm
  have hpTop : P.xi (interiorBlockFirst P p.1.1.1.val).succ = P.xi p.1.1.1.val.succ := by
    rw [(interior_empty_block_extremes P p.1.1.1.val hp).1]
  have hqCol : originalResponseCols Q q.1.1 =
      Q.xi (interiorBlockFirst Q q.1.1.1.val).succ := by
    rw [hpCol] at hcol
    rw [hpTop] at htop
    omega
  have hq : Q.xi q.1.1.1.val.succ = Q.zeta q.1.1.1.val.castSucc := by
    by_contra hne
    have hpos : Q.zeta q.1.1.1.val.castSucc < Q.xi q.1.1.1.val.succ :=
      lt_of_le_of_ne (Q.zeta_le_xi_succ _) (Ne.symm hne)
    have hlt := original_unit_col_lt_row_top Q q.1.1.1 hqns hpos q.1.1.2
    change originalResponseCols Q q.1.1 < Q.xi (interiorBlockFirst Q q.1.1.1.val).succ at hlt
    omega
  have hqCol' : originalResponseCols Q q.1.1 = Q.xi q.1.1.1.val.succ :=
    ((originalEmptyBlock_remaining_endpoints Q q.1.1.1 hq q.1.1.2).2).trans hq.symm
  rw [hpCol, hqCol'] at hcol
  refine ⟨q, hq, ?_⟩
  apply originalEmptyBlock_translated_endpoints P Q p.1.1.1 q.1.1.1 hp hq
  · omega
  · rw [← hp, ← hq]
    omega

end SkewCornerDescent.Matrix.SelectedCoordinate
