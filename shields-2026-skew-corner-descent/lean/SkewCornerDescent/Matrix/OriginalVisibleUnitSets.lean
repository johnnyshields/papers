/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalVisibleBlockMatching
import SkewCornerDescent.Matrix.OriginalUnitBoundaryOrder

/-!
# Complete original unit lists from visible endpoint profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Actual boundary order groups all visible rows or columns into one complete
nonselected component. The incoming half recovers every row when the least
column is at or above the midpoint; the outgoing half recovers every column
when the greatest row is at or below it. The matched component, its positive
span, and its whole list are produced from the actual profiles. Reconstructing
the opposite list and a possible midpoint pivot remains separate. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- All original rows of one complete block, measured from the actual retained
selected start. Nonselection later ensures that no source row was removed. -/
noncomputable def originalUnitRowDistances {n : ℕ} (P : Profile n)
    (a : OriginalSelectedBlocks (hD := hD) P) (u : OriginalBlocks P) : Finset ℤ :=
  Finset.univ.image fun k : Fin (originalRemovedSize (hD := hD) P u) =>
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
      originalRemainingRowBeta P ⟨u, k⟩

/-- All original columns of one complete block, measured from its actual
selected end, with every original unit pivot retained. -/
noncomputable def originalUnitColDistances {n : ℕ} (P : Profile n)
    (d : OriginalSelectedBlocks (hD := hD) P) (u : OriginalBlocks P) : Finset ℤ :=
  Finset.univ.image fun k : Fin (originalRemovedSize (hD := hD) P u) =>
    originalRemainingColBeta P ⟨u, k⟩ -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))

/-- If a positive-span block's least column is at or above the midpoint, its
complete original row list is recovered from the visible incoming profile.
The protected least-column match identifies one whole block on each side. -/
theorem original_visible_unit_row_sets {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (hune : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hvne : Q.zeta v.val.castSucc < Q.xi v.val.succ)
    (huint : originalResponseLowerCut P (some (originalSelectedEnumeration P i)) <
        (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P
        (some (originalSelectedEnumeration P t)))
    (hvint : originalResponseLowerCut Q (some (originalSelectedEnumeration Q i')) <
        (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q
        (some (originalSelectedEnumeration Q t')))
    (hgroup : P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i)))) - originalComponentTau P u =
      Q.xi (originalRowSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q i')))) - originalComponentTau Q v)
    (hband : 2 * (P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration P i)))) - originalComponentTau P u) ≤ K) :
    originalUnitRowDistances P (originalSelectedEnumeration P i) u =
      originalUnitRowDistances Q (originalSelectedEnumeration Q i') v := by
  classical
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  have hgroup' : x - originalComponentTau P u = x' - originalComponentTau Q v := hgroup
  have hband' : 2 * (x - originalComponentTau P u) ≤ K := hband
  have hbandQ : 2 * (x' - originalComponentTau Q v) ≤ K := by rw [← hgroup']; exact hband'
  unfold originalUnitRowDistances
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨k, _, hkz⟩ := Finset.mem_image.mp hz
    let p : OriginalResponseInterval (hD := hD) P (some a) (some b) :=
      ⟨⟨⟨u, k⟩, huint.2⟩, huint.1⟩
    have hrow := original_unit_row_gt_tau P u hu hune k
    change originalComponentTau P u < originalResponseRows P p.1.1 at hrow
    have hvisible : 2 * (x - originalResponseRows P p.1.1) < K := by omega
    obtain ⟨q, hq, hdist, htop⟩ := c.original_visible_incoming_block_match P Q i t i' t' ht'
      K hK hKQ hmaxP hmaxQ hcoeff p hu hvisible
    have htop' : x - originalComponentTau P u = x' - originalComponentTau Q q.1.1.1 := htop
    have hTau : originalComponentTau Q q.1.1.1 = originalComponentTau Q v := by omega
    have he := original_unit_tau_injective Q q.1.1.1 v hq hv hTau
    subst v
    refine Finset.mem_image.mpr ⟨q.1.1.2, Finset.mem_univ _, ?_⟩
    exact hdist.symm.trans hkz
  · intro z hz
    obtain ⟨k, _, hkz⟩ := Finset.mem_image.mp hz
    let q : OriginalResponseInterval (hD := hD) Q (some a') (some b') :=
      ⟨⟨⟨v, k⟩, hvint.2⟩, hvint.1⟩
    have hrow := original_unit_row_gt_tau Q v hv hvne k
    change originalComponentTau Q v < originalResponseRows Q q.1.1 at hrow
    have hvisible : 2 * (x' - originalResponseRows Q q.1.1) < K := by omega
    obtain ⟨p, hp, hdist, htop⟩ := c.original_visible_incoming_block_match Q P i' t' i t ht
      K hK hKP hmaxQ hmaxP (fun w hw => (hcoeff w hw).symm) q hv hvisible
    have htop' : x' - originalComponentTau Q v = x - originalComponentTau P p.1.1.1 := htop
    have hTau : originalComponentTau P p.1.1.1 = originalComponentTau P u := by omega
    have he := original_unit_tau_injective P p.1.1.1 u hp hu hTau
    subst u
    refine Finset.mem_image.mpr ⟨p.1.1.2, Finset.mem_univ _, ?_⟩
    exact hdist.symm.trans hkz

/-- If the greatest row of a positive-span block is at or below the midpoint,
the visible outgoing profile recovers its complete original column list. -/
theorem original_visible_unit_col_sets {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (hune : P.zeta u.val.castSucc < P.xi u.val.succ)
    (hvne : Q.zeta v.val.castSucc < Q.xi v.val.succ)
    (huint : originalResponseLowerCut P (some (originalSelectedEnumeration P i)) <
        (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P
        (some (originalSelectedEnumeration P t)))
    (hvint : originalResponseLowerCut Q (some (originalSelectedEnumeration Q i')) <
        (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q
        (some (originalSelectedEnumeration Q t')))
    (hgroup : P.xi (interiorBlockFirst P u.val).succ -
        P.zeta (originalColSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P t)))) =
      Q.xi (interiorBlockFirst Q v.val).succ -
        Q.zeta (originalColSplitEquiv (hD := hD) Q
          (.inl (some (originalSelectedEnumeration Q t')))))
    (hband : 2 * (P.xi (interiorBlockFirst P u.val).succ -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t))))) ≤ K) :
    originalUnitColDistances P (originalSelectedEnumeration P t) u =
      originalUnitColDistances Q (originalSelectedEnumeration Q t') v := by
  classical
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  have hgroup' : P.xi (interiorBlockFirst P u.val).succ - y =
      Q.xi (interiorBlockFirst Q v.val).succ - y' := hgroup
  have hband' : 2 * (P.xi (interiorBlockFirst P u.val).succ - y) ≤ K := hband
  have hbandQ : 2 * (Q.xi (interiorBlockFirst Q v.val).succ - y') ≤ K := by
    rw [← hgroup']
    exact hband'
  unfold originalUnitColDistances
  apply Finset.Subset.antisymm
  · intro z hz
    obtain ⟨k, _, hkz⟩ := Finset.mem_image.mp hz
    let p : OriginalResponseInterval (hD := hD) P (some a) (some b) :=
      ⟨⟨⟨u, k⟩, huint.2⟩, huint.1⟩
    have hcol := original_unit_col_lt_row_top P u hu hune k
    change originalResponseCols P p.1.1 < P.xi (interiorBlockFirst P u.val).succ at hcol
    have hvisible : 2 * (originalResponseCols P p.1.1 - y) < K := by omega
    obtain ⟨q, hq, hdist, htop⟩ := c.original_visible_outgoing_block_match P Q i t i' t' ht'
      K hK hKQ hmaxP hmaxQ hcoeff p hu hvisible
    have htop' : P.xi (interiorBlockFirst P u.val).succ - y =
        Q.xi (interiorBlockFirst Q q.1.1.1.val).succ - y' := htop
    have hTop : Q.xi (interiorBlockFirst Q q.1.1.1.val).succ =
        Q.xi (interiorBlockFirst Q v.val).succ := by omega
    have he := original_unit_row_top_injective Q q.1.1.1 v hq hv hTop
    subst v
    refine Finset.mem_image.mpr ⟨q.1.1.2, Finset.mem_univ _, ?_⟩
    exact hdist.symm.trans hkz
  · intro z hz
    obtain ⟨k, _, hkz⟩ := Finset.mem_image.mp hz
    let q : OriginalResponseInterval (hD := hD) Q (some a') (some b') :=
      ⟨⟨⟨v, k⟩, hvint.2⟩, hvint.1⟩
    have hcol := original_unit_col_lt_row_top Q v hv hvne k
    change originalResponseCols Q q.1.1 < Q.xi (interiorBlockFirst Q v.val).succ at hcol
    have hvisible : 2 * (originalResponseCols Q q.1.1 - y') < K := by omega
    obtain ⟨p, hp, hdist, htop⟩ := c.original_visible_outgoing_block_match Q P i' t' i t ht
      K hK hKP hmaxQ hmaxP (fun w hw => (hcoeff w hw).symm) q hv hvisible
    have htop' : Q.xi (interiorBlockFirst Q v.val).succ - y' =
        P.xi (interiorBlockFirst P p.1.1.1.val).succ - y := htop
    have hTop : P.xi (interiorBlockFirst P p.1.1.1.val).succ =
        P.xi (interiorBlockFirst P u.val).succ := by omega
    have he := original_unit_row_top_injective P p.1.1.1 u hp hu hTop
    subst u
    refine Finset.mem_image.mpr ⟨p.1.1.2, Finset.mem_univ _, ?_⟩
    exact hdist.symm.trans hkz

/-- Visible full profiles produce the matched positive block and its complete
original row set. The matched block, its type, its boundary coordinate, and
the resulting row-list equality are conclusions, not recovery hypotheses. -/
theorem original_visible_unit_rows_exists {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    ∃ v : OriginalBlocks Q, ¬ originalBlockSelected (hD := hD) Q v ∧
      Q.zeta v.val.castSucc < Q.xi v.val.succ ∧
      (originalResponseLowerCut Q (some (originalSelectedEnumeration Q i')) <
          (interiorBlock Q v.val : ℤ) ∧
        (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q
          (some (originalSelectedEnumeration Q t'))) ∧
      P.xi (originalRowSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P i)))) - originalComponentTau P u =
        Q.xi (originalRowSplitEquiv (hD := hD) Q
          (.inl (some (originalSelectedEnumeration Q i')))) - originalComponentTau Q v ∧
      originalUnitRowDistances P (originalSelectedEnumeration P i) u =
        originalUnitRowDistances Q (originalSelectedEnumeration Q i') v := by
  classical
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  let p := originalIntervalUnitIndex P (some a) (some b) u hu huint 0
  have hrow := original_unit_row_gt_tau P u hu hune (originalUnitIndex P u hu 0)
  change originalComponentTau P u < originalResponseRows P p.1.1 at hrow
  have hband' : 2 * (x - originalComponentTau P u) ≤ K := hband
  have hvisible : 2 * (x - originalResponseRows P p.1.1) < K := by omega
  obtain ⟨q, hq, hdist, hgroup⟩ := c.original_visible_incoming_block_match P Q i t i' t' ht'
    K hK hKQ hmaxP hmaxQ hcoeff p hu hvisible
  let v := q.1.1.1
  have hvint : originalResponseLowerCut Q (some a') < (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q (some b') :=
    ⟨q.2, q.1.2⟩
  have hvne : Q.zeta v.val.castSucc < Q.xi v.val.succ := by
    by_contra hn
    have hle := Q.zeta_le_xi_succ v.val
    have hempty : Q.xi v.val.succ = Q.zeta v.val.castSucc := by omega
    have hsep := c.original_incoming_unit_row_ne_empty P Q a (some b) u hu hune huint hmaxP
      0 a' (some b') q hempty hdist
    apply hsep
    let w := (x - originalResponseRows P p.1.1).toNat
    have hhigh := c.original_interval_nonselected_row_high P a (some b) p hu
    have hpos : 0 < x - originalResponseRows P p.1.1 := by have := c.top.pos; omega
    have hw : (w : ℤ) = x - originalResponseRows P p.1.1 := Int.toNat_of_nonneg hpos.le
    have hdegreeQ : (x' - originalResponseRows Q q.1.1).toNat = w := by rw [← hdist]
    change (c.originalResidueLeftEndpointPolynomial P (some a) (some b)).coeff w =
      (c.originalResidueLeftEndpointPolynomial Q (some a') (some b')).coeff
        (x' - originalResponseRows Q q.1.1).toNat
    rw [hdegreeQ]
    exact hcoeff w (by rw [hw]; exact hvisible)
  refine ⟨v, hq, hvne, hvint, hgroup, ?_⟩
  exact c.original_visible_unit_row_sets P Q i t ht i' t' ht' K hK hKP hKQ
    hmaxP hmaxQ hcoeff u v hu hq hune hvne huint hvint hgroup hband

/-- Visible outgoing profiles produce the matched positive block and its
complete original column set. No matched component or suffix recovery is assumed. -/
theorem original_visible_unit_cols_exists {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    ∃ v : OriginalBlocks Q, ¬ originalBlockSelected (hD := hD) Q v ∧
      Q.zeta v.val.castSucc < Q.xi v.val.succ ∧
      (originalResponseLowerCut Q (some (originalSelectedEnumeration Q i')) <
          (interiorBlock Q v.val : ℤ) ∧
        (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q
          (some (originalSelectedEnumeration Q t'))) ∧
      P.xi (interiorBlockFirst P u.val).succ -
          P.zeta (originalColSplitEquiv (hD := hD) P
            (.inl (some (originalSelectedEnumeration P t)))) =
        Q.xi (interiorBlockFirst Q v.val).succ -
          Q.zeta (originalColSplitEquiv (hD := hD) Q
            (.inl (some (originalSelectedEnumeration Q t')))) ∧
      originalUnitColDistances P (originalSelectedEnumeration P t) u =
        originalUnitColDistances Q (originalSelectedEnumeration Q t') v := by
  classical
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  let last : Fin (interiorBlockLength P u.val + 1) := Fin.last _
  let p := originalIntervalUnitIndex P (some a) (some b) u hu huint last
  have hcol := original_unit_col_lt_row_top P u hu hune (originalUnitIndex P u hu last)
  change originalResponseCols P p.1.1 < P.xi (interiorBlockFirst P u.val).succ at hcol
  have hband' : 2 * (P.xi (interiorBlockFirst P u.val).succ - y) ≤ K := hband
  have hvisible : 2 * (originalResponseCols P p.1.1 - y) < K := by omega
  obtain ⟨q, hq, hdist, hgroup⟩ := c.original_visible_outgoing_block_match P Q i t i' t' ht'
    K hK hKQ hmaxP hmaxQ hcoeff p hu hvisible
  let v := q.1.1.1
  have hvint : originalResponseLowerCut Q (some a') < (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q (some b') :=
    ⟨q.2, q.1.2⟩
  have hvne : Q.zeta v.val.castSucc < Q.xi v.val.succ := by
    by_contra hn
    have hle := Q.zeta_le_xi_succ v.val
    have hempty : Q.xi v.val.succ = Q.zeta v.val.castSucc := by omega
    have hsep := c.original_outgoing_unit_col_ne_empty P Q (some a) b u hu hune huint hmaxP
      last (some a') b' q hempty hdist
    apply hsep
    let w := (originalResponseCols P p.1.1 - y).toNat
    have hhigh := c.original_interval_nonselected_col_high P (some a) b p hu
    have hpos : 0 < originalResponseCols P p.1.1 - y := by have := c.top.pos; omega
    have hw : (w : ℤ) = originalResponseCols P p.1.1 - y := Int.toNat_of_nonneg hpos.le
    have hdegreeQ : (originalResponseCols Q q.1.1 - y').toNat = w := by rw [← hdist]
    change (c.originalResidueRightEndpointPolynomial P (some a) (some b)).coeff w =
      (c.originalResidueRightEndpointPolynomial Q (some a') (some b')).coeff
        (originalResponseCols Q q.1.1 - y').toNat
    rw [hdegreeQ]
    exact hcoeff w (by rw [hw]; exact hvisible)
  refine ⟨v, hq, hvne, hvint, hgroup, ?_⟩
  exact c.original_visible_unit_col_sets P Q i t ht i' t' ht' K hK hKP hKQ
    hmaxP hmaxQ hcoeff u v hu hq hune hvne huint hvint hgroup hband

end SkewCornerDescent.Matrix.SelectedCoordinate
