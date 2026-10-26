/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalStraddlingUnitRecovery

/-!
# Full original recovery of every positive unit component

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
The closed left and right inductions and the actual straddling reconstruction
recover every complete positive unit component from visible endpoint jets.
There is no midpoint-position, prefix-copy or inverse-value hypothesis.
The possible literal empty midpoint vertex is a separate obligation.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal visible actual endpoint profiles recover every positive full unit
component, with no midpoint-position restriction.  The two whole-side
inductions and the half-integer-safe straddling reconstruction cover all cases. -/
theorem original_positive_unit_recovery {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (u : OriginalBlocks P) (hu : ¬ originalBlockSelected (hD := hD) P u)
    (hune : P.zeta u.val.castSucc < P.xi u.val.succ)
    (huint : originalResponseLowerCut P (some (originalSelectedEnumeration P i)) <
        (interiorBlock P u.val : ℤ) ∧
      (interiorBlock P u.val : ℤ) < originalResponseUpperCut P
        (some (originalSelectedEnumeration P t))) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
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
  by_cases hleftBand : 2 * (P.xi (originalRowSplitEquiv (hD := hD) P
      (.inl (some (originalSelectedEnumeration P i)))) - originalComponentTau P u) ≤ K
  · exact c.original_left_unit_recovery P Q i t ht i' t' ht' K hK hKP hKQ
      hmaxP hmaxQ hleft u hu hune huint hleftBand
  by_cases hrightBand : 2 * (P.xi (interiorBlockFirst P u.val).succ -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t))))) ≤ K
  · obtain ⟨v, hv, hvne, hvint, e, he⟩ := c.original_right_unit_recovery P Q i t ht i' t' ht'
      K hK hKP hKQ hmaxP hmaxQ hright u hu hune huint hrightBand
    have hshift : Q.zeta (originalColSplitEquiv (hD := hD) Q
          (.inl (some (originalSelectedEnumeration Q t')))) -
        P.zeta (originalColSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P t)))) =
      Q.xi (originalRowSplitEquiv (hD := hD) Q
          (.inl (some (originalSelectedEnumeration Q i')))) -
        P.xi (originalRowSplitEquiv (hD := hD) P
          (.inl (some (originalSelectedEnumeration P i)))) := by omega
    refine ⟨v, hv, hvne, hvint, e, fun k => ?_⟩
    have hk := he k
    simpa only [hshift] using hk
  · exact c.original_straddling_unit_recovery P Q i t ht i' t' ht' K hK hKP hKQ
      hmaxP hmaxQ hleft hright u hu hune huint (by omega) (by omega)

end SkewCornerDescent.Matrix.SelectedCoordinate
