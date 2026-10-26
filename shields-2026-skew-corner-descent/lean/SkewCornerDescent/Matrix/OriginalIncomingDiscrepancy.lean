/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNonliteralDiscrepancy
import SkewCornerDescent.Matrix.OriginalPairedEndpointProfiles

/-!
# Visible discrepancy from a distinct full original incoming profile

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`,
`prop:normal-interface`.  Complete paired beta copying preserves the entire
endpoint polynomial, so distinct full incoming profiles produce nonliteral
geometry.  Actual early recovery then supplies a visible first difference.
No discrepancy or half-height hypothesis is carried.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Distinct complete incoming profiles at equal-response original intervals
have a genuine visible least difference.  A literal paired copy would preserve
the entire incoming polynomial, so nonliterality is produced here. -/
theorem original_incoming_difference_visible {n m : ℕ} (P : Profile n) (Q : Profile m)
    (i t : Fin (originalSelectedCount (hD := hD) P)) (ht : t.val = i.val + 1)
    (i' t' : Fin (originalSelectedCount (hD := hD) Q)) (ht' : t'.val = i'.val + 1)
    (K : ℕ+) (hK : 2 * (c.top : ℕ) < (K : ℕ))
    (hKP : P.xi (originalRowSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P i)))) -
      P.zeta (originalColSplitEquiv (hD := hD) P
        (.inl (some (originalSelectedEnumeration P t)))) = (K : ℤ))
    (hKQ : Q.xi (originalRowSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q i')))) -
      Q.zeta (originalColSplitEquiv (hD := hD) Q
        (.inl (some (originalSelectedEnumeration Q t')))) = (K : ℤ))
    (hmaxP : ∀ C ∈ edgeComponents (diagramInterior P.cells), span C ≤ (c.top : ℕ))
    (hmaxQ : ∀ C ∈ edgeComponents (diagramInterior Q.cells), span C ≤ (c.top : ℕ))
    (hresponse : c.regularResidue (c.originalLocalResponse P
        (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t))) =
      c.regularResidue (c.originalLocalResponse Q
        (some (originalSelectedEnumeration Q i')) (some (originalSelectedEnumeration Q t'))))
    (hne : c.originalResidueLeftEndpointPolynomial P
        (some (originalSelectedEnumeration P i)) (some (originalSelectedEnumeration P t)) ≠
      c.originalResidueLeftEndpointPolynomial Q
        (some (originalSelectedEnumeration Q i')) (some (originalSelectedEnumeration Q t'))) :
    ∃ w : ℕ, 0 < w ∧ 2 * w < (K : ℕ) ∧
      (∀ l < w, (c.originalResidueLeftEndpointPolynomial P
          (some (originalSelectedEnumeration P i))
          (some (originalSelectedEnumeration P t))).coeff l =
        (c.originalResidueLeftEndpointPolynomial Q
          (some (originalSelectedEnumeration Q i'))
          (some (originalSelectedEnumeration Q t'))).coeff l) ∧
      (c.originalResidueLeftEndpointPolynomial P
          (some (originalSelectedEnumeration P i))
          (some (originalSelectedEnumeration P t))).coeff w -
        (c.originalResidueLeftEndpointPolynomial Q
          (some (originalSelectedEnumeration Q i'))
          (some (originalSelectedEnumeration Q t'))).coeff w ≠ 0 := by
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
  have hnonliteral : ¬ ∃ e : OriginalResponseInterval (hD := hD) P (some a) (some b) ≃
      OriginalResponseInterval (hD := hD) Q (some a') (some b'),
      ∀ p, originalResponseRows Q (e p).1.1 = originalResponseRows P p.1.1 + shift ∧
        originalResponseCols Q (e p).1.1 = originalResponseCols P p.1.1 + shift := by
    rintro ⟨e, he⟩
    apply hne
    exact (c.original_interval_endpoint_polynomials_of_copy P Q a b a' b' shift e he
      (by change x' = x + shift; dsimp only [shift]; omega)
      (by change y' = y + shift
          change x - y = (K : ℤ) at hKP
          change x' - y' = (K : ℤ) at hKQ
          dsimp only [shift]
          omega)).1
  obtain ⟨w, hw, hbound, hleft, _, hη, _, _⟩ :=
    c.original_nonliteral_first_profile_difference P Q i t ht i' t' ht' K hK
      hKP hKQ hmaxP hmaxQ hresponse hnonliteral
  exact ⟨w, hw, hbound, hleft, hη⟩

end SkewCornerDescent.Matrix.SelectedCoordinate
