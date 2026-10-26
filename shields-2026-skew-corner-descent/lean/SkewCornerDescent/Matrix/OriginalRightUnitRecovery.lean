/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalRightUnitExtension
import SkewCornerDescent.Matrix.OriginalRightSuffixMatches
import SkewCornerDescent.Matrix.ProfileBetaRigidity

/-!
# Complete original unit reconstruction from the right

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Visible outgoing coefficients reconstruct every whole positive component
whose greatest row is at or below the midpoint.  Well-founded induction
constructs both actual suffixes, retaining terminal proper strips, later
positive components and empty pivots.  No suffix-copy or inverse-value
compatibility remains a theorem hypothesis.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Visible outgoing coefficients reconstruct every whole positive unit to
the right of the midpoint.  The complete actual suffixes are produced by
well-founded recursion, retaining proper strips and literal empty pivots. -/
theorem original_right_unit_recovery {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let shift := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t))))
    ∃ v : OriginalBlocks Q, ¬ originalBlockSelected (hD := hD) Q v ∧
      Q.zeta v.val.castSucc < Q.xi v.val.succ ∧
      (originalResponseLowerCut Q (some a') < (interiorBlock Q v.val : ℤ) ∧
        (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q (some b')) ∧
      ∃ e : Fin (originalRemovedSize (hD := hD) P u) ≃
          Fin (originalRemovedSize (hD := hD) Q v),
        ∀ k, originalRemainingRowBeta Q ⟨v, e k⟩ =
            originalRemainingRowBeta P ⟨u, k⟩ + shift ∧
          originalRemainingColBeta Q ⟨v, e k⟩ =
            originalRemainingColBeta P ⟨u, k⟩ + shift := by
  classical
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  let shift := y' - y
  obtain ⟨v, hv, hvint, hvne, hgroup, hextend⟩ := c.original_visible_right_unit_extension
    P Q i t ht i' t' ht' K hK hKP hKQ hmaxP hmaxQ hcoeff u hu hune huint hband
  change P.xi (interiorBlockFirst P u.val).succ - y =
    Q.xi (interiorBlockFirst Q v.val).succ - y' at hgroup
  change 2 * (P.xi (interiorBlockFirst P u.val).succ - y) ≤ K at hband
  have hvband : 2 * (Q.xi (interiorBlockFirst Q v.val).succ - y') ≤ K := by omega
  have hframe : Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) = shift := by
    change P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) - y = K at hKP
    change Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) - y' = K at hKQ
    dsimp only [shift]
    omega
  rw [hframe] at hextend
  have hpos : 0 < P.xi (interiorBlockFirst P u.val).succ - y := by
    let p := originalIntervalUnitIndex P (some a) (some b) u hu huint (Fin.last _)
    have hh := c.original_interval_nonselected_col_high P (some a) b p hu
    have hr := original_unit_col_lt_row_top P u hu hune (originalUnitIndex P u hu (Fin.last _))
    change (c.top : ℤ) <
      originalRemainingColBeta P ⟨u, originalUnitIndex P u hu (Fin.last _)⟩ - y at hh
    have := c.top.pos
    omega
  have hc := c.original_selected_end_core_literal P Q a b a' b'
    (original_consecutive_endpoint_label_le P i t ht)
    (original_consecutive_endpoint_label_le Q i' t' ht') K hK hcoeff
  have hselected := original_selected_endpoint_equiv_of_end_core_cells P Q b b' hc shift
    (by dsimp only [shift]; omega)
  have hselected' := original_selected_endpoint_equiv_of_end_core_cells Q P b' b hc.symm (-shift)
    (by dsimp only [shift]; omega)
  have hvisibleP : 2 * (originalComponentTau P u - y) < K := by
    have hh := original_unit_extremes_strict P u hu hune
    omega
  have hvisibleQ : 2 * (originalComponentTau Q v - y') < K := by
    have hh := original_unit_extremes_strict Q v hv hvne
    omega
  have hf := c.original_right_suffix_point_matches P Q i t ht i' t' ht' K hK hKP hKQ
    hmaxP hmaxQ hcoeff u v hu hv hvint hvisibleP hgroup hselected
  have hf' := c.original_right_suffix_point_matches Q P i' t' ht' i t ht K hK hKQ hKP
    hmaxQ hmaxP (fun w hw => (hcoeff w hw).symm) v u hv hu huint hvisibleQ
    hgroup.symm (by simpa only [shift, neg_sub] using hselected')
  have hprior : ∀ w : OriginalBlocks P, u < w →
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
              originalRemainingColBeta P ⟨w, k⟩ + shift := by
    intro w huw hw hwne hwint
    have htop := original_unit_row_top_strict P u w hu hw huw
    have hwband : 2 * (P.xi (interiorBlockFirst P w.val).succ - y) ≤ K := by omega
    have hd : (P.xi (interiorBlockFirst P w.val).succ - y).toNat <
        (P.xi (interiorBlockFirst P u.val).succ - y).toNat := by omega
    obtain ⟨z, hz, _, hzint, e, he⟩ := original_right_unit_recovery P Q i t ht i' t' ht'
      K hK hKP hKQ hmaxP hmaxQ hcoeff w hw hwne hwint hwband
    exact ⟨z, hz, hzint, e, he⟩
  have hprior' : ∀ w : OriginalBlocks Q, v < w →
      ¬ originalBlockSelected (hD := hD) Q w →
      Q.zeta w.val.castSucc < Q.xi w.val.succ →
      (originalResponseLowerCut Q (some a') < (interiorBlock Q w.val : ℤ) ∧
        (interiorBlock Q w.val : ℤ) < originalResponseUpperCut Q (some b')) →
      ∃ z : OriginalBlocks P, ¬ originalBlockSelected (hD := hD) P z ∧
        (originalResponseLowerCut P (some a) < (interiorBlock P z.val : ℤ) ∧
          (interiorBlock P z.val : ℤ) < originalResponseUpperCut P (some b)) ∧
        ∃ e : Fin (originalRemovedSize (hD := hD) Q w) ≃
            Fin (originalRemovedSize (hD := hD) P z),
          ∀ k, originalRemainingRowBeta P ⟨z, e k⟩ =
              originalRemainingRowBeta Q ⟨w, k⟩ + (y - y') ∧
            originalRemainingColBeta P ⟨z, e k⟩ =
              originalRemainingColBeta Q ⟨w, k⟩ + (y - y') := by
    intro w hvw hw hwne hwint
    have htop := original_unit_row_top_strict Q v w hv hw hvw
    have hwband : 2 * (Q.xi (interiorBlockFirst Q w.val).succ - y') ≤ K := by omega
    have hd : (Q.xi (interiorBlockFirst Q w.val).succ - y').toNat <
        (P.xi (interiorBlockFirst P u.val).succ - y).toNat := by omega
    obtain ⟨z, hz, _, hzint, e, he⟩ := original_right_unit_recovery Q P i' t' ht' i t ht
      K hK hKQ hKP hmaxQ hmaxP (fun w hw => (hcoeff w hw).symm) w hw hwne hwint hwband
    exact ⟨z, hz, hzint, e, he⟩
  have hforward := hf hprior
  have hbackward := hf' hprior'
  obtain ⟨e, he⟩ := original_interval_suffix_equiv_of_matches P Q (some a) (some b) u
    (some a') (some b') v shift hforward (by
      intro j
      obtain ⟨k, hr, hc⟩ := hbackward j
      refine ⟨k, ?_, ?_⟩ <;> dsimp only [shift, y, y', b, b'] at * <;> omega)
  obtain ⟨E, hE⟩ := hextend e (fun k => (he k).1) (fun k => (he k).2)
  exact ⟨v, hv, hvne, hvint, E, hE⟩
termination_by (P.xi (interiorBlockFirst P u.val).succ -
  P.zeta (originalColSplitEquiv (hD := hD) P
    (.inl (some (originalSelectedEnumeration P t))))).toNat
decreasing_by all_goals omega

end SkewCornerDescent.Matrix.SelectedCoordinate
