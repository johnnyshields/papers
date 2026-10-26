/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalIncomingDiscrepancy

/-!
# A full incoming profile determines the literal original interval

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`,
`prop:normal-interface`.  At equal actual responses and heights, complete
incoming-profile equality is equivalent to the full paired original interval
copy.  Opposite first discrepancies supply the converse without assuming
any outgoing-profile equality.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- At equal actual responses and height, equality of the complete incoming
profiles is equivalent to a complete original paired interval copy.  The
reverse implication uses opposite first differences, not a supplied outgoing
profile or a geometric recovery premise. -/
theorem original_interval_literal_iff_incoming_eq {n m : ℕ} (P : Profile n) (Q : Profile m)
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
        (some (originalSelectedEnumeration Q i')) (some (originalSelectedEnumeration Q t')))) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P t
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    (∃ e : OriginalResponseInterval (hD := hD) P (some a) (some b) ≃
        OriginalResponseInterval (hD := hD) Q (some a') (some b'),
      ∀ p, originalResponseRows Q (e p).1.1 = originalResponseRows P p.1.1 + shift ∧
        originalResponseCols Q (e p).1.1 = originalResponseCols P p.1.1 + shift) ↔
      c.originalResidueLeftEndpointPolynomial P (some a) (some b) =
        c.originalResidueLeftEndpointPolynomial Q (some a') (some b') := by
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
  dsimp only
  constructor
  · rintro ⟨e, he⟩
    exact (c.original_interval_endpoint_polynomials_of_copy P Q a b a' b' shift e he
      (by change x' = x + shift; dsimp only [shift]; omega)
      (by change y' = y + shift
          change x - y = (K : ℤ) at hKP
          change x' - y' = (K : ℤ) at hKQ
          dsimp only [shift]
          omega)).1
  · intro hincoming
    by_contra hnonliteral
    obtain ⟨w, _, _, _, _, hη, _, _⟩ := c.original_nonliteral_first_profile_difference P Q
      i t ht i' t' ht' K hK hKP hKQ hmaxP hmaxQ hresponse hnonliteral
    apply hη
    exact sub_eq_zero.mpr (congrArg (fun f : Polynomial (OtherField c.top) => f.coeff w) hincoming)

end SkewCornerDescent.Matrix.SelectedCoordinate
