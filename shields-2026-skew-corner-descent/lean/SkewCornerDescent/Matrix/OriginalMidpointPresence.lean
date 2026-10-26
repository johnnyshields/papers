/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalMidpointDetection

/-!
# Equal original responses decide midpoint presence

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Visible endpoint jets produce the complete punctured-interval beta copy.
Actual source response transport and the nonzero original midpoint correction
then force the same presence or absence of the single remaining vertex.
No literal-copy, inverse-match or insertion-response premise is supplied.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
attribute [local instance] Classical.propDecidable
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal actual residue responses and visible endpoint jets force the same
presence or absence of the unique literal midpoint vertex.  Every punctured
matrix match and its inverse are produced from the original intervals. -/
theorem original_midpoint_presence_iff {n m : ℕ} (P : Profile n) (Q : Profile m)
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
    (∃ p, originalIntervalMidpointVertex P a b p) ↔
      ∃ q, originalIntervalMidpointVertex Q a' b' q := by
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
  let := c.originalNonmidpointIntervalInverse P a b
  let := c.originalNonmidpointIntervalInverse Q a' b'
  obtain ⟨e, he⟩ := c.original_nonmidpoint_interval_equiv P Q i t ht i' t' ht' K hK
    hKP hKQ hmaxP hmaxQ hleft hright
  have hcopy := vertexBetaResponse_affine_reindex c.residueMap e
    (fun p : OriginalNonmidpointInterval P a b => originalResponseRows P p.1.1.1)
    (fun p => originalResponseCols P p.1.1.1)
    (fun q => originalResponseRows Q q.1.1.1) (fun q => originalResponseCols Q q.1.1.1)
    x y shift (fun p => (he p).1) (fun p => (he p).2)
  have hx : x + shift = x' := by dsimp only [shift]; omega
  have hy : y + shift = y' := by
    change x - y = K at hKP
    change x' - y' = K at hKQ
    dsimp only [shift]
    omega
  rw [hx, hy] at hcopy
  dsimp only
  constructor
  · rintro ⟨p, hp⟩
    by_contra hn
    have hnone : ∀ q, ¬ originalIntervalMidpointVertex Q a' b' q := by
      simpa only [not_exists] using hn
    have hne := c.original_midpoint_response_ne_punctured P a b p hp
      (by change 2 * (c.top : ℤ) < x - y; change x - y = K at hKP; omega)
    apply hne
    exact hresponse.trans ((c.original_interval_without_midpoint_response Q a' b' hnone).trans
      hcopy.symm)
  · rintro ⟨q, hq⟩
    by_contra hn
    have hnone : ∀ p, ¬ originalIntervalMidpointVertex P a b p := by
      simpa only [not_exists] using hn
    have hne := c.original_midpoint_response_ne_punctured Q a' b' q hq
      (by change 2 * (c.top : ℤ) < x' - y'; change x' - y' = K at hKQ; omega)
    apply hne
    exact hresponse.symm.trans ((c.original_interval_without_midpoint_response P a b hnone).trans
      hcopy)

end SkewCornerDescent.Matrix.SelectedCoordinate
