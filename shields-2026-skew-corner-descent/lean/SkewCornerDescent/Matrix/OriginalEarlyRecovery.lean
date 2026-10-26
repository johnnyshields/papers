/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalMidpointPresence

/-!
# Complete original early recovery

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
The actual residue response and both endpoint jets strictly below half-height
produce an equivalence of every retained original row and column, with their
common beta translation.  All positive components, selected proper strips,
visible empty pivots and the possible invisible midpoint pivot are supplied
by the source reconstruction; no recovery or inverse-compatibility premise
remains.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual residue response and its two visible endpoint jets determine
the complete original paired row and column lists of a consecutive selected
interval.  No component, prefix, inverse-value or midpoint-match premise is
carried: all are constructed from the actual source. -/
theorem original_early_recovery_interval {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (hresponse : c.regularResidue (c.originalLocalResponse P
        (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t))) =
      c.regularResidue (c.originalLocalResponse Q
        (some (originalSelectedEnumeration Q i')) (some (originalSelectedEnumeration Q t')))) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P t
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    ∃ e : OriginalResponseInterval (hD := hD) P (some a) (some b) ≃
        OriginalResponseInterval (hD := hD) Q (some a') (some b'),
      ∀ p, originalResponseRows Q (e p).1.1 = originalResponseRows P p.1.1 + shift ∧
        originalResponseCols Q (e p).1.1 = originalResponseCols P p.1.1 + shift := by
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
  have hpresence := c.original_midpoint_presence_iff P Q i t ht i' t' ht' K hK
    hKP hKQ hmaxP hmaxQ hleft hright hresponse
  have hmidmatch (p : OriginalResponseInterval (hD := hD) P (some a) (some b))
      (hp : originalIntervalMidpointVertex P a b p)
      (q : OriginalResponseInterval (hD := hD) Q (some a') (some b'))
      (hq : originalIntervalMidpointVertex Q a' b' q) :
      originalResponseRows Q q.1.1 = originalResponseRows P p.1.1 + shift ∧
        originalResponseCols Q q.1.1 = originalResponseCols P p.1.1 + shift := by
    have hpcoord := original_interval_midpoint_coordinates P a b p hp
    have hqcoord := original_interval_midpoint_coordinates Q a' b' q hq
    have hp2 : 2 * originalResponseRows P p.1.1 = x + y := hp.2
    have hq2 : 2 * originalResponseRows Q q.1.1 = x' + y' := hq.2
    have hr : originalResponseRows Q q.1.1 = originalResponseRows P p.1.1 + shift := by
      dsimp only [shift]
      omega
    refine ⟨hr, ?_⟩
    rw [← hpcoord, ← hqcoord]
    exact hr
  apply original_interval_equiv_of_matches P Q (some a) (some b) (some a') (some b') shift
  · intro p
    by_cases hp : originalIntervalMidpointVertex P a b p
    · obtain ⟨q, hq⟩ := hpresence.mp ⟨p, hp⟩
      exact ⟨q, hmidmatch p hp q hq⟩
    · obtain ⟨q, _, hr, hc⟩ := c.original_nonmidpoint_point_match P Q i t ht i' t' ht'
        K hK hKP hKQ hmaxP hmaxQ hleft hright p hp
      exact ⟨q, hr, hc⟩
  · intro q
    by_cases hq : originalIntervalMidpointVertex Q a' b' q
    · obtain ⟨p, hp⟩ := hpresence.mpr ⟨q, hq⟩
      exact ⟨p, hmidmatch p hp q hq⟩
    · obtain ⟨p, _, hr, hc⟩ := c.original_nonmidpoint_point_match Q P i' t' ht' i t ht
        K hK hKQ hKP hmaxQ hmaxP (fun w hw => (hleft w hw).symm)
          (fun w hw => (hright w hw).symm) q hq
      refine ⟨p, ?_, ?_⟩ <;> dsimp only [shift, x, x', a, a'] at * <;> omega

end SkewCornerDescent.Matrix.SelectedCoordinate
