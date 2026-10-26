/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalProfileAtoms
import SkewCornerDescent.Matrix.OriginalEndpointProfileSupport
import SkewCornerDescent.Matrix.OriginalIntervalProfileBands

/-!
# Source-produced matching of visible original unit blocks

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Equality of visible complete profiles matches every original nonselected row
and its least-column coordinate, or every original nonselected column and its
greatest-row coordinate. The target is a genuine consecutive selected interval.
All nonzero coefficients, support positions, and protected affine models are
produced from the actual source. Whole-block reconstruction remains separate.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal visible incoming profiles match every original nonselected row and
its complete block's least column in a consecutive target interval. The source
interval may be longer. Both protected models are source-produced. -/
theorem original_visible_incoming_block_match {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (hp : ¬ originalBlockSelected (hD := hD) P p.1.1.1)
    (hvisible : 2 * (P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i)))) - originalResponseRows P p.1.1) < K) :
    ∃ q : OriginalResponseInterval (hD := hD) Q
        (some (originalSelectedEnumeration Q i')) (some (originalSelectedEnumeration Q t')),
      ¬ originalBlockSelected (hD := hD) Q q.1.1.1 ∧
      P.xi (originalRowSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P i)))) - originalResponseRows P p.1.1 =
        Q.xi (originalRowSplitEquiv (hD := hD) Q
          (.inl (some (originalSelectedEnumeration Q i')))) - originalResponseRows Q q.1.1 ∧
      P.xi (originalRowSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P i)))) - originalComponentTau P p.1.1.1 =
        Q.xi (originalRowSplitEquiv (hD := hD) Q
          (.inl (some (originalSelectedEnumeration Q i')))) - originalComponentTau Q q.1.1.1 := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  let w := (x - originalResponseRows P p.1.1).toNat
  have hhigh := c.original_interval_nonselected_row_high P a (some b) p hp
  have hpos : 0 < x - originalResponseRows P p.1.1 := by have := c.top.pos; omega
  have hw : (w : ℤ) = x - originalResponseRows P p.1.1 := Int.toNat_of_nonneg hpos.le
  have hw0 : w ≠ 0 := by omega
  have hwvis : 2 * (w : ℤ) < K := by rw [hw]; exact hvisible
  have hnonzero := c.original_nonselected_left_profile_ne_zero P a (some b) p hp hmaxP
  have hc := hcoeff w hwvis
  have hQnz : (c.originalResidueLeftEndpointPolynomial Q (some a') (some b')).coeff w ≠ 0 := by
    rw [← hc]
    exact hnonzero
  obtain ⟨q, hqdist⟩ := c.original_left_profile_nonzero_position Q (some a') (some b') w hw0 hQnz
  have hdist : x - originalResponseRows P p.1.1 = x' - originalResponseRows Q q.1.1 :=
    hw.symm.trans hqdist.symm
  have hvisibleQ : 2 * (x' - originalResponseRows Q q.1.1) < K := by
    rw [← hdist]
    exact hvisible
  have hunitQ : ¬ originalBlockSelected (hD := hD) Q q.1.1.1 := by
    rcases c.original_consecutive_visible_row_cases Q i' t' ht' q
      (by rw [hKQ]; exact hK) (by rw [hKQ]; exact hvisibleQ) with hsel | hunit
    · have hb := c.original_selected_row_distance_band Q a' q.1.1 hsel
      omega
    · exact hunit
  obtain ⟨J, hJe, hJ, α, hα, hα0, R, hR, hvalueP⟩ :=
    c.original_interval_incoming_atom P a (some b) p hp hmaxP
  obtain ⟨L, hLe, hL, β, hβ, hβ0, T, hT, hvalueQ⟩ :=
    c.original_interval_incoming_atom Q a' (some b') q hunitQ hmaxQ
  have hpc := c.original_left_profile_coeff_at_row P (some a) (some b) p
  have hqc := c.original_left_profile_coeff_at_row Q (some a') (some b') q
  dsimp only at hpc hqc hvalueP hvalueQ hJe hLe
  have hdegreeQ : (x' - originalResponseRows Q q.1.1).toNat = w := by rw [← hdist]
  have hceq :
      (c.originalResidueLeftEndpointPolynomial P (some a) (some b)).coeff
        (x - originalResponseRows P p.1.1).toNat =
      (c.originalResidueLeftEndpointPolynomial Q (some a') (some b')).coeff
        (x' - originalResponseRows Q q.1.1).toNat := by
    rw [hdegreeQ]
    exact hc
  rw [hpc, hqc] at hceq
  have hvalues := neg_inj.mp hceq
  rw [hvalueP, hvalueQ] at hvalues
  have hJL := c.residue_protected_affine_top_unique J L hJ hL α R β T
    hα hα0 hR hβ hβ0 hT hvalues
  have he := congrArg (fun v : ℕ+ => (v : ℤ)) hJL
  refine ⟨q, hunitQ, hdist, ?_⟩
  exact hJe.symm.trans (he.trans hLe)

/-- The complete visible outgoing profiles match every original nonselected
column and its component's actual greatest row in a consecutive target interval. -/
theorem original_visible_outgoing_block_match {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (hp : ¬ originalBlockSelected (hD := hD) P p.1.1.1)
    (hvisible : 2 * (originalResponseCols P p.1.1 -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t))))) < K) :
    ∃ q : OriginalResponseInterval (hD := hD) Q
        (some (originalSelectedEnumeration Q i')) (some (originalSelectedEnumeration Q t')),
      ¬ originalBlockSelected (hD := hD) Q q.1.1.1 ∧
      originalResponseCols P p.1.1 -
          P.zeta (originalColSplitEquiv (hD := hD) P
            (.inl (some (originalSelectedEnumeration P t)))) =
        originalResponseCols Q q.1.1 -
          Q.zeta (originalColSplitEquiv (hD := hD) Q
            (.inl (some (originalSelectedEnumeration Q t')))) ∧
      P.xi (interiorBlockFirst P p.1.1.1.val).succ -
          P.zeta (originalColSplitEquiv (hD := hD) P
            (.inl (some (originalSelectedEnumeration P t)))) =
        Q.xi (interiorBlockFirst Q q.1.1.1.val).succ -
          Q.zeta (originalColSplitEquiv (hD := hD) Q
            (.inl (some (originalSelectedEnumeration Q t')))) := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  let w := (originalResponseCols P p.1.1 - y).toNat
  have hhigh := c.original_interval_nonselected_col_high P (some a) b p hp
  have hpos : 0 < originalResponseCols P p.1.1 - y := by have := c.top.pos; omega
  have hw : (w : ℤ) = originalResponseCols P p.1.1 - y := Int.toNat_of_nonneg hpos.le
  have hw0 : w ≠ 0 := by omega
  have hwvis : 2 * (w : ℤ) < K := by rw [hw]; exact hvisible
  have hnonzero := c.original_nonselected_right_profile_ne_zero P (some a) b p hp hmaxP
  have hc := hcoeff w hwvis
  have hQnz : (c.originalResidueRightEndpointPolynomial Q (some a') (some b')).coeff w ≠ 0 := by
    rw [← hc]
    exact hnonzero
  obtain ⟨q, hqdist⟩ := c.original_right_profile_nonzero_position Q (some a') (some b') w hw0 hQnz
  have hdist : originalResponseCols P p.1.1 - y = originalResponseCols Q q.1.1 - y' :=
    hw.symm.trans hqdist.symm
  have hvisibleQ : 2 * (originalResponseCols Q q.1.1 - y') < K := by
    rw [← hdist]
    exact hvisible
  have hunitQ : ¬ originalBlockSelected (hD := hD) Q q.1.1.1 := by
    rcases c.original_consecutive_visible_col_cases Q i' t' ht' q
      (by rw [hKQ]; exact hK) (by rw [hKQ]; exact hvisibleQ) with hsel | hunit
    · have hb := c.original_selected_col_distance_band Q b' q.1.1 hsel
      omega
    · exact hunit
  obtain ⟨J, hJe, hJ, α, hα, hα0, R, hR, hvalueP⟩ :=
    c.original_interval_outgoing_atom P (some a) b p hp hmaxP
  obtain ⟨L, hLe, hL, β, hβ, hβ0, T, hT, hvalueQ⟩ :=
    c.original_interval_outgoing_atom Q (some a') b' q hunitQ hmaxQ
  have hpc := c.original_right_profile_coeff_at_col P (some a) (some b) p
  have hqc := c.original_right_profile_coeff_at_col Q (some a') (some b') q
  dsimp only at hpc hqc hvalueP hvalueQ hJe hLe
  have hdegreeQ : (originalResponseCols Q q.1.1 - y').toNat = w := by rw [← hdist]
  have hceq :
      (c.originalResidueRightEndpointPolynomial P (some a) (some b)).coeff
        (originalResponseCols P p.1.1 - y).toNat =
      (c.originalResidueRightEndpointPolynomial Q (some a') (some b')).coeff
        (originalResponseCols Q q.1.1 - y').toNat := by
    rw [hdegreeQ]
    exact hc
  rw [hpc, hqc] at hceq
  have hvalues := neg_inj.mp hceq
  rw [hvalueP, hvalueQ] at hvalues
  have hvalues' : residueGenerator c.top ⟨J, ne_of_gt hJ⟩ * α + R =
      residueGenerator c.top ⟨L, ne_of_gt hL⟩ * β + T := by
    simpa only [mul_comm α, mul_comm β] using hvalues
  have hJL := c.residue_protected_affine_top_unique J L hJ hL α R β T
    hα hα0 hR hβ hβ0 hT hvalues'
  have he := congrArg (fun v : ℕ+ => (v : ℤ)) hJL
  refine ⟨q, hunitQ, hdist, ?_⟩
  exact hJe.symm.trans (he.trans hLe)

end SkewCornerDescent.Matrix.SelectedCoordinate
