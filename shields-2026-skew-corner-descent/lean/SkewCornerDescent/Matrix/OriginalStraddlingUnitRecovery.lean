/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalStraddlingUnitMatch
import SkewCornerDescent.Matrix.OriginalVisibleUnitPrefix
import SkewCornerDescent.Matrix.OriginalVisibleUnitSuffix
import SkewCornerDescent.Matrix.OriginalProfileValueMatching

/-!
# Complete original reconstruction of a midpoint-straddling unit

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Actual incoming and outgoing visible coefficients identify one target block
and both boundaries.  Closed neighbor reconstruction produces both full
ordered copies and inverse values, then recovers the entire paired current
endpoint list.  Odd-height midpoints require no rounding.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Both actual visible profiles reconstruct every paired endpoint of a
component straddling the genuine midpoint, including odd interval heights.
Both complete ordered inverses are produced from reconstructed neighbors. -/
theorem original_straddling_unit_recovery {n m : ℕ} (P : Profile n) (Q : Profile m)
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
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let x := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  let x' := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a')))
  let y := P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some b)))
  let y' := Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some b')))
  have hheightP : x - y = K := hKP
  have hheightQ : x' - y' = K := hKQ
  have hheight : x - y = x' - y' := hheightP.trans hheightQ.symm
  have hlo' : 2 * originalComponentTau P u < x + y := hlo
  have hhi' : x + y < 2 * P.xi (interiorBlockFirst P u.val).succ := hhi
  obtain ⟨v, hv, hvne, hvint, hτ, htop⟩ := c.original_visible_straddling_unit_match
    P Q i t i' t' ht' K hK hKP hKQ hmaxP hmaxQ hleft hright u hu huint hlo hhi
  change x - originalComponentTau P u = x' - originalComponentTau Q v at hτ
  change P.xi (interiorBlockFirst P u.val).succ - y =
    Q.xi (interiorBlockFirst Q v.val).succ - y' at htop
  have hheadP : 2 * (x - P.xi (interiorBlockFirst P u.val).succ) < K := by omega
  have hheadQ : 2 * (x' - Q.xi (interiorBlockFirst Q v.val).succ) < K := by omega
  have htailP : 2 * (originalComponentTau P u - y) < K := by omega
  have htailQ : 2 * (originalComponentTau Q v - y') < K := by omega
  obtain ⟨eP, heP⟩ := c.original_visible_unit_prefix_equiv P Q i t ht i' t' ht' K hK hKP hKQ
    hmaxP hmaxQ hleft u v hu hv huint hvint hheadP hheadQ hτ
  obtain ⟨eS, heS⟩ := c.original_visible_unit_suffix_equiv P Q i t ht i' t' ht' K hK hKP hKQ
    hmaxP hmaxQ hright u v hu hv huint hvint htailP htailQ htop
  let p := originalIntervalUnitIndex P (some a) (some b) u hu huint 0
  let q := originalIntervalUnitIndex Q (some a') (some b') v hv hvint 0
  let p' := originalIntervalUnitIndex P (some a) (some b) u hu huint (Fin.last _)
  let q' := originalIntervalUnitIndex Q (some a') (some b') v hv hvint (Fin.last _)
  have hp : originalResponseRows P p.1.1 = P.xi (interiorBlockFirst P u.val).succ := by
    change P.xi (originalRemovedRow P u (originalUnitIndex P u hu 0)).succ = _
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first]
  have hq : originalResponseRows Q q.1.1 = Q.xi (interiorBlockFirst Q v.val).succ := by
    change Q.xi (originalRemovedRow Q v (originalUnitIndex Q v hv 0)).succ = _
    rw [originalRemovedRow, originalUnitIndex_row, originalBlockInterval_first]
  have hp' : originalResponseCols P p'.1.1 = originalComponentTau P u := by
    change P.zeta (originalRemovedCol P u (originalUnitIndex P u hu (Fin.last _))).castSucc = _
    rw [originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last]
    rfl
  have hq' : originalResponseCols Q q'.1.1 = originalComponentTau Q v := by
    change Q.zeta (originalRemovedCol Q v (originalUnitIndex Q v hv (Fin.last _))).castSucc = _
    rw [originalRemovedCol, originalUnitIndex_col, interiorBlock_slice_last]
    rfl
  have hin := c.original_incoming_value_of_profile_jet P Q a (some b) a' (some b') p q K hleft
    (by change x - _ = x' - _; rw [hp, hq]; omega)
    (by change 2 * (x - _) < K; rw [hp]; exact hheadP)
  have hout := c.original_outgoing_value_of_profile_jet P Q (some a) b (some a') b' p' q' K hright
    (by change _ - y = _ - y'; rw [hp', hq']; omega)
    (by change 2 * (_ - y) < K; rw [hp']; exact htailP)
  have hcols := c.original_unit_columns_of_prefix_copy P Q a b a' b' u v hu hv hune hvne
    huint hvint hmaxP hmaxQ hheight eP (fun k => (heP k).1) (fun k => (heP k).2) hin
  have hshift : y' - y = x' - x := by omega
  have hrS (k) : originalResponseRows Q (eS k).1.1.1 =
      originalResponseRows P k.1.1.1 + (x' - x) := by
    have hk : originalResponseRows Q (eS k).1.1.1 =
      originalResponseRows P k.1.1.1 + (y' - y) := (heS k).1
    rwa [hshift] at hk
  have hcS (k) : originalResponseCols Q (eS k).1.1.1 =
      originalResponseCols P k.1.1.1 + (x' - x) := by
    have hk : originalResponseCols Q (eS k).1.1.1 =
      originalResponseCols P k.1.1.1 + (y' - y) := (heS k).2
    rwa [hshift] at hk
  have hrows := c.original_unit_rows_of_suffix_copy P Q a b a' b' u v hu hv hune hvne
    huint hvint hmaxP hmaxQ hheight eS hrS hcS hout
  obtain ⟨E, hE⟩ := original_unit_endpoint_equiv_of_lists P Q a b a' b' u v hu hv hune hvne
    hheight hrows hcols
  exact ⟨v, hv, hvne, hvint, E, hE⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
