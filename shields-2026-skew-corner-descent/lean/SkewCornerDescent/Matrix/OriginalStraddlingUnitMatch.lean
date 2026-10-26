/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVisibleBlockMatching
import SkewCornerDescent.Matrix.OriginalUnitBoundaryOrder

/-!
# One original target block for a midpoint-straddling component

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
The actual incoming and outgoing visible matches are reconciled by strict
component order at the doubled midpoint.  Both target boundary coordinates
are recovered together, including odd-height intervals.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The incoming and outgoing visible matches of a component crossing the
actual midpoint belong to one target block.  The midpoint may be a strict
half-integer; neither the source nor the target is rounded. -/
theorem original_visible_straddling_unit_match {n m : ℕ} (P : Profile n) (Q : Profile m)
    (i t : Fin (originalSelectedCount (hD := hD) P))
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
    (hleft : ∀ w : ℕ, 2 * (w : ℤ) < K →
      (c.originalResidueLeftEndpointPolynomial P
        (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t))).coeff w =
      (c.originalResidueLeftEndpointPolynomial Q
        (some (originalSelectedEnumeration Q i'))
        (some (originalSelectedEnumeration Q t'))).coeff w)
    (hright : ∀ w : ℕ, 2 * (w : ℤ) < K →
      (c.originalResidueRightEndpointPolynomial P
        (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t))).coeff w =
      (c.originalResidueRightEndpointPolynomial Q
        (some (originalSelectedEnumeration Q i'))
        (some (originalSelectedEnumeration Q t'))).coeff w)
    (u : OriginalBlocks P) (hu : ¬ originalBlockSelected (hD := hD) P u)
    (huint : originalResponseLowerCut P (some (originalSelectedEnumeration P i)) <
        (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P
        (some (originalSelectedEnumeration P t)))
    (hlo : 2 * originalComponentTau P u <
      P.xi (originalRowSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P i)))) +
        P.zeta (originalColSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P t)))))
    (hhi : P.xi (originalRowSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P i)))) +
        P.zeta (originalColSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P t)))) <
      2 * P.xi (interiorBlockFirst P u.val).succ) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P t
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
    let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
    ∃ v : OriginalBlocks Q, ¬ originalBlockSelected (hD := hD) Q v ∧
      Q.zeta v.val.castSucc < Q.xi v.val.succ ∧
      (originalResponseLowerCut Q (some a') < (interiorBlock Q v.val : ℤ) ∧
        (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q (some b')) ∧
      x - originalComponentTau P u = x' - originalComponentTau Q v ∧
      P.xi (interiorBlockFirst P u.val).succ - y =
        Q.xi (interiorBlockFirst Q v.val).succ - y' := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  let p := originalIntervalUnitIndex P (some a) (some b) u hu huint 0
  let s := originalIntervalUnitIndex P (some a) (some b) u hu huint (Fin.last _)
  have hp : originalResponseRows P p.1.1 = P.xi (interiorBlockFirst P u.val).succ := by
    change P.xi (originalRemovedRow P u (originalUnitIndex P u hu 0)).succ = _
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first]
  have hs : originalResponseCols P s.1.1 = originalComponentTau P u := by
    change P.zeta (originalRemovedCol P u (originalUnitIndex P u hu (Fin.last _))).castSucc = _
    rw [originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last]
    rfl
  have hheightP : x - y = K := hKP
  have hheightQ : x' - y' = K := hKQ
  have hlo' : 2 * originalComponentTau P u < x + y := hlo
  have hhi' : x + y < 2 * P.xi (interiorBlockFirst P u.val).succ := hhi
  obtain ⟨q, hq, hrow, htau⟩ := c.original_visible_incoming_block_match
    P Q i t i' t' ht' K hK hKQ hmaxP hmaxQ hleft p hu (by rw [hp]; omega)
  obtain ⟨j, hj, hcol, htop⟩ := c.original_visible_outgoing_block_match
    P Q i t i' t' ht' K hK hKQ hmaxP hmaxQ hright s hu (by rw [hs]; omega)
  change x - originalResponseRows P p.1.1 = x' - originalResponseRows Q q.1.1 at hrow
  change x - originalComponentTau P u = x' - originalComponentTau Q q.1.1.1 at htau
  change originalResponseCols P s.1.1 - y = originalResponseCols Q j.1.1 - y' at hcol
  change P.xi (interiorBlockFirst P u.val).succ - y =
    Q.xi (interiorBlockFirst Q j.1.1.1.val).succ - y' at htop
  rw [hp] at hrow
  rw [hs] at hcol
  have hqTop := original_remaining_row_le_block_top Q q.1.1
  have hjTau := original_remaining_col_ge_tau Q j.1.1
  change originalResponseRows Q q.1.1 ≤ Q.xi (interiorBlockFirst Q q.1.1.1.val).succ at hqTop
  change originalComponentTau Q j.1.1.1 ≤ originalResponseCols Q j.1.1 at hjTau
  have he : q.1.1.1 = j.1.1.1 := original_unit_half_midpoint_unique Q _ _ hq hj
    (x' + y') (by omega) (by omega) (by omega) (by omega)
  have htop' : P.xi (interiorBlockFirst P u.val).succ - y =
      Q.xi (interiorBlockFirst Q q.1.1.1.val).succ - y' := by rw [he]; exact htop
  have hqne : Q.zeta q.1.1.1.val.castSucc < Q.xi q.1.1.1.val.succ := by
    by_contra hnot
    have heq : Q.xi q.1.1.1.val.succ = Q.zeta q.1.1.1.val.castSucc :=
      le_antisymm (le_of_not_gt hnot) (Q.zeta_le_xi_succ _)
    have hext := interior_empty_block_extremes Q q.1.1.1.val heq
    have hsame : originalComponentTau Q q.1.1.1 =
        Q.xi (interiorBlockFirst Q q.1.1.1.val).succ := by
      dsimp only [originalComponentTau]
      rw [hext.1, hext.2, heq]
    omega
  exact ⟨q.1.1.1, hq, hqne, ⟨q.2, q.1.2⟩, htau, htop'⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
