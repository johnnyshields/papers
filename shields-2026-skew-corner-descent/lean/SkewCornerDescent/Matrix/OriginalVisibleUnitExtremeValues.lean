/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitSetExtremes

/-!
# Exact extreme inverse values supplied by visible original profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Whole visible unit lists identify both actual boundary coordinates. Their
true extrema then supply equality of the complete original incoming or
outgoing inverse coefficient at the corresponding extreme index. The matched
component, its list, and that inverse equality are produced rather than
assumed as reconstruction data. Literal prefix and suffix assembly remains
separate. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The visible profiles produce the current whole row list and its exact
complete incoming value at the greatest row. The paired component, both
boundary coordinates, and original inverse value are all conclusions. -/
theorem original_visible_unit_incoming_extreme {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (u : OriginalBlocks P) (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hune : P.zeta u.val.castSucc < P.xi u.val.succ)
    (huint : originalResponseLowerCut P (some (originalSelectedEnumeration P i)) <
        (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P
        (some (originalSelectedEnumeration P t)))
    (hband : 2 * (P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration P i)))) - originalComponentTau P u) ≤ K) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P t
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
    let rowP := fun k : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
      originalResponseRows P k.1.1
    let colP := fun k : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
      originalResponseCols P k.1.1
    let rowQ := fun k : OriginalResponseInterval (hD := hD) Q (some a') (some b') =>
      originalResponseRows Q k.1.1
    let colQ := fun k : OriginalResponseInterval (hD := hD) Q (some a') (some b') =>
      originalResponseCols Q k.1.1
    ∃ v : OriginalBlocks Q, ∃ hv : ¬ originalBlockSelected (hD := hD) Q v,
    ∃ hvint : originalResponseLowerCut Q (some a') < (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q (some b'),
      Q.zeta v.val.castSucc < Q.xi v.val.succ ∧
      x - originalComponentTau P u = x' - originalComponentTau Q v ∧
      x - P.xi (interiorBlockFirst P u.val).succ =
        x' - Q.xi (interiorBlockFirst Q v.val).succ ∧
      originalUnitRowDistances P a u = originalUnitRowDistances Q a' v ∧
      (vertexOutgoing c.residueMap colP x * (vertexBetaMatrix c.residueMap rowP colP)⁻¹)
          () (originalIntervalUnitIndex P (some a) (some b) u hu huint 0) =
        (vertexOutgoing c.residueMap colQ x' * (vertexBetaMatrix c.residueMap rowQ colQ)⁻¹)
          () (originalIntervalUnitIndex Q (some a') (some b') v hv hvint 0) := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  obtain ⟨v, hv, hvne, hvint, hgroup, hrows⟩ := c.original_visible_unit_rows_exists
    P Q i t ht i' t' ht' K hK hKP hKQ hmaxP hmaxQ hcoeff u hu hune huint hband
  have hrows' : originalUnitRowDistances P a u = originalUnitRowDistances Q a' v := hrows
  have hminP := original_unit_row_distances_least P a u hu
  have hminQ := original_unit_row_distances_least Q a' v hv
  rw [hrows'] at hminP
  have hext : x - P.xi (interiorBlockFirst P u.val).succ =
      x' - Q.xi (interiorBlockFirst Q v.val).succ := hminP.unique hminQ
  let p := originalIntervalUnitIndex P (some a) (some b) u hu huint 0
  let q := originalIntervalUnitIndex Q (some a') (some b') v hv hvint 0
  have hp0 : originalResponseRows P p.1.1 = P.xi (interiorBlockFirst P u.val).succ := by
    change P.xi (originalRemovedRow P u (originalUnitIndex P u hu 0)).succ = _
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first]
  have hq0 : originalResponseRows Q q.1.1 = Q.xi (interiorBlockFirst Q v.val).succ := by
    change Q.xi (originalRemovedRow Q v (originalUnitIndex Q v hv 0)).succ = _
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first]
  have hdist : x - originalResponseRows P p.1.1 = x' - originalResponseRows Q q.1.1 := by
    rw [hp0, hq0]
    exact hext
  have hrow := original_unit_row_gt_tau P u hu hune (originalUnitIndex P u hu 0)
  change originalComponentTau P u < originalResponseRows P p.1.1 at hrow
  have hband' : 2 * (x - originalComponentTau P u) ≤ K := hband
  have hvisible : 2 * (x - originalResponseRows P p.1.1) < K := by omega
  have hhigh := c.original_interval_nonselected_row_high P a (some b) p hu
  have hpos : 0 < x - originalResponseRows P p.1.1 := by have := c.top.pos; omega
  let w := (x - originalResponseRows P p.1.1).toNat
  have hw : (w : ℤ) = x - originalResponseRows P p.1.1 := Int.toNat_of_nonneg hpos.le
  have hdegreeQ : (x' - originalResponseRows Q q.1.1).toNat = w := by rw [← hdist]
  have hc := hcoeff w (by rw [hw]; exact hvisible)
  have hpc := c.original_left_profile_coeff_at_row P (some a) (some b) p
  have hqc := c.original_left_profile_coeff_at_row Q (some a') (some b') q
  dsimp only at hpc hqc
  refine ⟨v, hv, hvint, hvne, hgroup, hext, hrows, ?_⟩
  have hceq :
      (c.originalResidueLeftEndpointPolynomial P (some a) (some b)).coeff
        (x - originalResponseRows P p.1.1).toNat =
      (c.originalResidueLeftEndpointPolynomial Q (some a') (some b')).coeff
        (x' - originalResponseRows Q q.1.1).toNat := by
    rw [hdegreeQ]
    exact hc
  rw [hpc, hqc] at hceq
  exact neg_inj.mp hceq

/-- The outgoing visible profiles produce a whole column list and the exact
complete inverse value at its actual least column, with both boundary coordinates. -/
theorem original_visible_unit_outgoing_extreme {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (u : OriginalBlocks P) (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hune : P.zeta u.val.castSucc < P.xi u.val.succ)
    (huint : originalResponseLowerCut P (some (originalSelectedEnumeration P i)) <
        (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P
        (some (originalSelectedEnumeration P t)))
    (hband : 2 * (P.xi (interiorBlockFirst P u.val).succ -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t))))) ≤ K) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P t
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
    let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
    let rowP := fun k : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
      originalResponseRows P k.1.1
    let colP := fun k : OriginalResponseInterval (hD := hD) P (some a) (some b) =>
      originalResponseCols P k.1.1
    let rowQ := fun k : OriginalResponseInterval (hD := hD) Q (some a') (some b') =>
      originalResponseRows Q k.1.1
    let colQ := fun k : OriginalResponseInterval (hD := hD) Q (some a') (some b') =>
      originalResponseCols Q k.1.1
    ∃ v : OriginalBlocks Q, ∃ hv : ¬ originalBlockSelected (hD := hD) Q v,
    ∃ hvint : originalResponseLowerCut Q (some a') < (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q (some b'),
      Q.zeta v.val.castSucc < Q.xi v.val.succ ∧
      P.xi (interiorBlockFirst P u.val).succ - y =
        Q.xi (interiorBlockFirst Q v.val).succ - y' ∧
      originalComponentTau P u - y = originalComponentTau Q v - y' ∧
      originalUnitColDistances P b u = originalUnitColDistances Q b' v ∧
      ((vertexBetaMatrix c.residueMap rowP colP)⁻¹ * vertexIncoming c.residueMap rowP y)
          (originalIntervalUnitIndex P (some a) (some b) u hu huint (Fin.last _)) () =
        ((vertexBetaMatrix c.residueMap rowQ colQ)⁻¹ * vertexIncoming c.residueMap rowQ y')
          (originalIntervalUnitIndex Q (some a') (some b') v hv hvint (Fin.last _)) () := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  obtain ⟨v, hv, hvne, hvint, hgroup, hcols⟩ := c.original_visible_unit_cols_exists
    P Q i t ht i' t' ht' K hK hKP hKQ hmaxP hmaxQ hcoeff u hu hune huint hband
  have hcols' : originalUnitColDistances P b u = originalUnitColDistances Q b' v := hcols
  have hminP := original_unit_col_distances_least P b u hu
  have hminQ := original_unit_col_distances_least Q b' v hv
  rw [hcols'] at hminP
  have hext : originalComponentTau P u - y = originalComponentTau Q v - y' :=
    hminP.unique hminQ
  let p := originalIntervalUnitIndex P (some a) (some b) u hu huint (Fin.last _)
  let q := originalIntervalUnitIndex Q (some a') (some b') v hv hvint (Fin.last _)
  have hp0 : originalResponseCols P p.1.1 = originalComponentTau P u := by
    change P.zeta (originalRemovedCol P u (originalUnitIndex P u hu (Fin.last _))).castSucc = _
    rw [originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last]
    rfl
  have hq0 : originalResponseCols Q q.1.1 = originalComponentTau Q v := by
    change Q.zeta (originalRemovedCol Q v (originalUnitIndex Q v hv (Fin.last _))).castSucc = _
    rw [originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last]
    rfl
  have hdist : originalResponseCols P p.1.1 - y = originalResponseCols Q q.1.1 - y' := by
    rw [hp0, hq0]
    exact hext
  have hcol := original_unit_col_lt_row_top P u hu hune (originalUnitIndex P u hu (Fin.last _))
  change originalResponseCols P p.1.1 < P.xi (interiorBlockFirst P u.val).succ at hcol
  have hband' : 2 * (P.xi (interiorBlockFirst P u.val).succ - y) ≤ K := hband
  have hvisible : 2 * (originalResponseCols P p.1.1 - y) < K := by omega
  have hhigh := c.original_interval_nonselected_col_high P (some a) b p hu
  have hpos : 0 < originalResponseCols P p.1.1 - y := by have := c.top.pos; omega
  let w := (originalResponseCols P p.1.1 - y).toNat
  have hw : (w : ℤ) = originalResponseCols P p.1.1 - y := Int.toNat_of_nonneg hpos.le
  have hdegreeQ : (originalResponseCols Q q.1.1 - y').toNat = w := by rw [← hdist]
  have hc := hcoeff w (by rw [hw]; exact hvisible)
  have hpc := c.original_right_profile_coeff_at_col P (some a) (some b) p
  have hqc := c.original_right_profile_coeff_at_col Q (some a') (some b') q
  dsimp only at hpc hqc
  refine ⟨v, hv, hvint, hvne, hgroup, hext, hcols, ?_⟩
  have hceq :
      (c.originalResidueRightEndpointPolynomial P (some a) (some b)).coeff
        (originalResponseCols P p.1.1 - y).toNat =
      (c.originalResidueRightEndpointPolynomial Q (some a') (some b')).coeff
        (originalResponseCols Q q.1.1 - y').toNat := by
    rw [hdegreeQ]
    exact hc
  rw [hpc, hqc] at hceq
  exact neg_inj.mp hceq

end SkewCornerDescent.Matrix.SelectedCoordinate
