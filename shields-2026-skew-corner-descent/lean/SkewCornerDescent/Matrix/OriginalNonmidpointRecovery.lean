/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalPositiveUnitRecovery

/-!
# Actual endpoint recovery away from a literal midpoint pivot

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
The full positive-unit reconstruction, both selected-core producers and
visible empty-pivot reconstruction recover every retained interval point
except a literal empty block at the exact midpoint.  Both original paired
coordinates and exclusion of that exception are preserved.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The actual retained point of a literal empty block exactly at midpoint. -/
def originalIntervalMidpointVertex {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (p : OriginalResponseInterval (hD := hD) P (some a) (some b)) : Prop :=
  P.xi p.1.1.1.val.succ = P.zeta p.1.1.1.val.castSucc ∧
    2 * originalResponseRows P p.1.1 =
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) +
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))

variable (c : SelectedCoordinate D hD)

/-- Every actual interval point except a literal empty midpoint vertex is
recovered from the two visible endpoint jets.  The target point is also
outside that exception and both of its original coordinates are retained. -/
theorem original_nonmidpoint_point_match {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (p : OriginalResponseInterval (hD := hD) P
      (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t)))
    (hp : ¬ originalIntervalMidpointVertex P (originalSelectedEnumeration P i)
      (originalSelectedEnumeration P t) p) :
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
      P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i))))
    ∃ q : OriginalResponseInterval (hD := hD) Q (some a') (some b'),
      ¬ originalIntervalMidpointVertex Q a' b' q ∧
      originalResponseRows Q q.1.1 = originalResponseRows P p.1.1 + shift ∧
      originalResponseCols Q q.1.1 = originalResponseCols P p.1.1 + shift := by
  classical
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  let shift := x' - x
  have hheightP : x - y = K := hKP
  have hheightQ : x' - y' = K := hKQ
  have hshift : y' - y = shift := by dsimp only [shift]; omega
  have hcase := original_consecutive_interval_block_cases P i t ht p
  rcases p with ⟨⟨⟨u, kk⟩, hupper⟩, hlower⟩
  rcases hcase with hstart | hend | hunit
  · change u = a.val at hstart
    subst u
    have hc := c.original_selected_start_core_literal P Q a b a' b'
      (original_consecutive_endpoint_label_le P i t ht)
      (original_consecutive_endpoint_label_le Q i' t' ht') K hK hleft
    obtain ⟨e, he⟩ := original_selected_endpoint_equiv_of_core_cells P Q a a' hc shift
      (by dsimp only [shift]; omega)
    let q := originalSelectedStartIntervalIndex Q a' b'
      (original_consecutive_endpoint_label_le Q i' t' ht') (e kk)
    refine ⟨q, ?_, he kk⟩
    intro hmid
    have hempty : Q.xi a'.val.val.succ = Q.zeta a'.val.val.castSucc := hmid.1
    exact (ne_of_gt (originalBlockSelected_nonempty Q a'.val a'.property)) hempty
  · change u = b.val at hend
    subst u
    have hc := c.original_selected_end_core_literal P Q a b a' b'
      (original_consecutive_endpoint_label_le P i t ht)
      (original_consecutive_endpoint_label_le Q i' t' ht') K hK hright
    obtain ⟨e, he⟩ := original_selected_endpoint_equiv_of_end_core_cells P Q b b' hc shift
      (by change y' = y + shift; omega)
    let q := originalSelectedEndIntervalIndex Q a' b'
      (original_consecutive_endpoint_label_le Q i' t' ht') (e kk)
    refine ⟨q, ?_, he kk⟩
    intro hmid
    have hempty : Q.xi b'.val.val.succ = Q.zeta b'.val.val.castSucc := hmid.1
    exact (ne_of_gt (originalBlockSelected_nonempty Q b'.val b'.property)) hempty
  · change ¬ originalBlockSelected (hD := hD) P u at hunit
    by_cases hne : P.zeta u.val.castSucc < P.xi u.val.succ
    · obtain ⟨v, _, hvne, hvint, e, he⟩ := c.original_positive_unit_recovery
        P Q i t ht i' t' ht' K hK hKP hKQ hmaxP hmaxQ hleft hright u hunit hne
          ⟨hlower, hupper⟩
      let q : OriginalResponseInterval (hD := hD) Q (some a') (some b') :=
        ⟨⟨⟨v, e kk⟩, hvint.2⟩, hvint.1⟩
      refine ⟨q, ?_, he kk⟩
      intro hmid
      have hempty : Q.xi v.val.succ = Q.zeta v.val.castSucc := hmid.1
      exact (ne_of_gt hvne) hempty
    · have hempty : P.xi u.val.succ = P.zeta u.val.castSucc :=
        le_antisymm (le_of_not_gt hne) (P.zeta_le_xi_succ _)
      let p : OriginalResponseInterval (hD := hD) P (some a) (some b) :=
        ⟨⟨⟨u, kk⟩, hupper⟩, hlower⟩
      have hnotmid : 2 * originalResponseRows P p.1.1 ≠ x + y := by
        intro heq
        exact hp ⟨hempty, heq⟩
      have hpcol : originalResponseCols P p.1.1 = originalResponseRows P p.1.1 := by
        obtain ⟨hr, hc⟩ := originalEmptyBlock_remaining_endpoints P u hempty kk
        change P.zeta (originalRemovedCol P u kk).castSucc =
          P.xi (originalRemovedRow P u kk).succ
        rw [hr, hc, hempty]
      have hexists : ∃ q : OriginalResponseInterval (hD := hD) Q (some a') (some b'),
          ∃ e : Fin (originalRemovedSize (hD := hD) P u) ≃
              Fin (originalRemovedSize (hD := hD) Q q.1.1.1),
            ∀ k, originalRemainingRowBeta Q ⟨q.1.1.1, e k⟩ =
                originalRemainingRowBeta P ⟨u, k⟩ + shift ∧
              originalRemainingColBeta Q ⟨q.1.1.1, e k⟩ =
                originalRemainingColBeta P ⟨u, k⟩ + shift := by
        by_cases hvis : 2 * (x - originalResponseRows P p.1.1) < K
        · obtain ⟨q, _, e, he⟩ := c.original_visible_incoming_empty_recovery
            P Q i t i' t' ht' K hK hKQ hmaxP hmaxQ hleft p hempty hvis
          exact ⟨q, e, he⟩
        · have hvis' : 2 * (originalResponseCols P p.1.1 - y) < K := by
            rw [hpcol]
            omega
          obtain ⟨q, _, e, he⟩ := c.original_visible_outgoing_empty_recovery
            P Q i t i' t' ht' K hK hKQ hmaxP hmaxQ hright p hempty hvis'
          refine ⟨q, e, fun k => ?_⟩
          have hk : originalRemainingRowBeta Q ⟨q.1.1.1, e k⟩ =
              originalRemainingRowBeta P ⟨u, k⟩ + (y' - y) ∧
            originalRemainingColBeta Q ⟨q.1.1.1, e k⟩ =
              originalRemainingColBeta P ⟨u, k⟩ + (y' - y) := he k
          simpa only [hshift] using hk
      obtain ⟨q0, e, he⟩ := hexists
      let q : OriginalResponseInterval (hD := hD) Q (some a') (some b') :=
        ⟨⟨⟨q0.1.1.1, e kk⟩, q0.1.2⟩, q0.2⟩
      have hr : originalResponseRows Q q.1.1 = originalResponseRows P p.1.1 + shift := (he kk).1
      refine ⟨q, ?_, he kk⟩
      intro hmid
      have hm : 2 * originalResponseRows Q q.1.1 = x' + y' := hmid.2
      apply hnotmid
      dsimp only [shift] at hr
      omega

end SkewCornerDescent.Matrix.SelectedCoordinate
