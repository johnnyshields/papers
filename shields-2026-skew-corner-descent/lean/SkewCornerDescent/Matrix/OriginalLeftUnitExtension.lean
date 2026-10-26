/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalUnitPrefixRecovery
import SkewCornerDescent.Matrix.OriginalUnitLiteralFromLists

/-!
# Left-to-right original component reconstruction step

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Visible incoming coefficients produce the target block, its full row list
and its extreme inverse value.  A paired prefix then yields the full
current endpoint equivalence.  Prefix construction is the induction input.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The visible profiles produce the current target block and a literal
reconstruction extension: every already reconstructed paired prefix yields
the whole current original endpoint equivalence. The prefix construction
itself is the explicit induction input, not a claimed consequence here. -/
theorem original_visible_left_unit_extension {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    ∃ v : OriginalBlocks Q, ∃ _hv : ¬ originalBlockSelected (hD := hD) Q v,
    ∃ _hvint : originalResponseLowerCut Q (some a') < (interiorBlock Q v.val : ℤ) ∧
      (interiorBlock Q v.val : ℤ) < originalResponseUpperCut Q (some b'),
      Q.zeta v.val.castSucc < Q.xi v.val.succ ∧
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) - originalComponentTau P u =
        Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) - originalComponentTau Q v ∧
      ∀ e : OriginalIntervalUnitPrefix (hD := hD) P (some a) (some b) u ≃
          OriginalIntervalUnitPrefix (hD := hD) Q (some a') (some b') v,
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
  obtain ⟨v, hv, hvint, hvne, hgroup, _, hrows, hvalue⟩ :=
    c.original_visible_unit_incoming_extreme P Q i t ht i' t' ht' K hK hKP hKQ
      hmaxP hmaxQ hcoeff u hu hune huint hband
  refine ⟨v, hv, hvint, hvne, hgroup, ?_⟩
  intro e hr hc
  have hheight : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b))) =
      Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
        Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b'))) :=
    hKP.trans hKQ.symm
  have hcols := c.original_unit_columns_of_prefix_copy P Q a b a' b' u v hu hv hune hvne
    huint hvint hmaxP hmaxQ hheight e hr hc hvalue
  exact original_unit_endpoint_equiv_of_lists P Q a b a' b' u v hu hv hune hvne
    hheight hrows hcols

end SkewCornerDescent.Matrix.SelectedCoordinate
