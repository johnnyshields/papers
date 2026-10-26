/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitSuffixRecovery
import SkewCornerDescent.Matrix.OriginalUnitLiteralFromLists

/-!
# Right-to-left original component reconstruction step

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Visible outgoing coefficients produce the target block, its full column list
and its extreme inverse value.  A paired suffix yields the full current
endpoint equivalence; suffix construction remains the induction input.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Visible outgoing coefficients produce the current target block.  Every
already reconstructed paired suffix extends to the full current original
endpoint equivalence; suffix construction is the explicit induction input. -/
theorem original_visible_right_unit_extension {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    ∃ v : OriginalBlocks Q, ∃ _hv : ¬ originalBlockSelected (hD := hD) Q v,
    ∃ _hvint : originalResponseLowerCut Q (some a') < (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q (some b'),
      Q.zeta v.val.castSucc < Q.xi v.val.succ ∧
      P.xi (interiorBlockFirst P u.val).succ -
          P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) =
        Q.xi (interiorBlockFirst Q v.val).succ -
          Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))) ∧
      ∀ e : OriginalIntervalUnitSuffix (hD := hD) P (some a) (some b) u ≃
          OriginalIntervalUnitSuffix (hD := hD) Q (some a') (some b') v,
        (∀ k, originalResponseRows Q (e k).1.1.1 = originalResponseRows P k.1.1.1 + shift) →
        (∀ k, originalResponseCols Q (e k).1.1.1 = originalResponseCols P k.1.1.1 + shift) →
        ∃ E : Fin (originalRemovedSize (hD := hD) P u) ≃
            Fin (originalRemovedSize (hD := hD) Q v),
          ∀ k, originalRemainingRowBeta Q ⟨v, E k⟩ =
              originalRemainingRowBeta P ⟨u, k⟩ + shift ∧
            originalRemainingColBeta Q ⟨v, E k⟩ =
              originalRemainingColBeta P ⟨u, k⟩ + shift := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  obtain ⟨v, hv, hvint, hvne, hgroup, _, hcols, hvalue⟩ :=
    c.original_visible_unit_outgoing_extreme P Q i t ht i' t' ht' K hK hKP hKQ
      hmaxP hmaxQ hcoeff u hu hune huint hband
  refine ⟨v, hv, hvint, hvne, hgroup, ?_⟩
  intro e hr hc
  have hheight : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) =
      Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
        Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))) :=
    hKP.trans hKQ.symm
  have hrows := c.original_unit_rows_of_suffix_copy P Q a b a' b' u v hu hv hune hvne
    huint hvint hmaxP hmaxQ hheight e hr hc hvalue
  exact original_unit_endpoint_equiv_of_lists P Q a b a' b' u v hu hv hune hvne
    hheight hrows hcols

end SkewCornerDescent.Matrix.SelectedCoordinate
