/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNonmidpointRecovery

/-!
# Whole original interval recovery outside a possible midpoint vertex

Formalizes `shields-2026-skew-corner-descent.tex`, `lem:early-recovery`.
Visible original endpoint jets produce a paired equivalence of the entire
interval with only a literal empty midpoint vertex excluded.  Such a vertex
is unique and has equal original row and column.  Deciding its presence
from the actual residue response remains a separate assembly obligation.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D}

/-- The genuine response interval with only its possible empty midpoint pivot excluded. -/
abbrev OriginalNonmidpointInterval {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P) :=
  {p : OriginalResponseInterval (hD := hD) P (some a) (some b) //
    ¬ originalIntervalMidpointVertex P a b p}

/-- An actual selected-end interval contains at most one literal midpoint vertex. -/
theorem original_interval_midpoint_unique {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (p q : OriginalResponseInterval (hD := hD) P (some a) (some b))
    (hp : originalIntervalMidpointVertex P a b p)
    (hq : originalIntervalMidpointVertex P a b q) : p = q := by
  have hr : originalResponseRows P p.1.1 = originalResponseRows P q.1.1 := by
    have hp' := hp.2
    have hq' := hq.2
    omega
  exact Subtype.ext (Subtype.ext (original_response_rows_injective P hr))

/-- The single genuine midpoint pivot has identical original row and column. -/
theorem original_interval_midpoint_coordinates {n : ℕ} (P : Profile n)
    (a b : OriginalSelectedBlocks (hD := hD) P)
    (p : OriginalResponseInterval (hD := hD) P (some a) (some b))
    (hp : originalIntervalMidpointVertex P a b p) :
    originalResponseRows P p.1.1 = originalResponseCols P p.1.1 := by
  have h := originalEmptyBlock_remaining_endpoints P p.1.1.1 hp.1 p.1.1.2
  change P.xi (originalRemovedRow P p.1.1.1 p.1.1.2).succ =
    P.zeta (originalRemovedCol P p.1.1.1 p.1.1.2).castSucc
  rw [h.1, h.2, hp.1]

variable (c : SelectedCoordinate D hD)

/-- The two actual visible endpoint jets determine the whole original paired
interval except its unique possible literal empty midpoint vertex. -/
theorem original_nonmidpoint_interval_equiv {n m : ℕ} (P : Profile n) (Q : Profile m)
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
        (some (originalSelectedEnumeration Q t'))).coeff w) :
    let a := originalSelectedEnumeration (hD := hD) P i
    let b := originalSelectedEnumeration (hD := hD) P t
    let a' := originalSelectedEnumeration (hD := hD) Q i'
    let b' := originalSelectedEnumeration (hD := hD) Q t'
    let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
    ∃ e : OriginalNonmidpointInterval P a b ≃ OriginalNonmidpointInterval Q a' b',
      ∀ k, originalResponseRows Q (e k).1.1.1 = originalResponseRows P k.1.1.1 + shift ∧
        originalResponseCols Q (e k).1.1.1 = originalResponseCols P k.1.1.1 + shift := by
  let a := originalSelectedEnumeration (hD := hD) P i
  let b := originalSelectedEnumeration (hD := hD) P t
  let a' := originalSelectedEnumeration (hD := hD) Q i'
  let b' := originalSelectedEnumeration (hD := hD) Q t'
  let shift := Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some a'))) -
    P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some a)))
  apply original_interval_kept_equiv_of_matches P Q (some a) (some b) (some a') (some b')
    (fun p => ¬ originalIntervalMidpointVertex P a b p)
    (fun q => ¬ originalIntervalMidpointVertex Q a' b' q) shift
  · intro p
    obtain ⟨q, hq, hr, hc⟩ := c.original_nonmidpoint_point_match P Q i t ht i' t' ht'
      K hK hKP hKQ hmaxP hmaxQ hleft hright p.1 p.2
    exact ⟨⟨q, hq⟩, hr, hc⟩
  · intro q
    obtain ⟨p, hp, hr, hc⟩ := c.original_nonmidpoint_point_match Q P i' t' ht' i t ht
      K hK hKQ hKP hmaxQ hmaxP (fun w hw => (hleft w hw).symm)
        (fun w hw => (hright w hw).symm) q.1 q.2
    refine ⟨⟨p, hp⟩, ?_, ?_⟩ <;> dsimp only [shift, a, a'] at * <;> omega

end SkewCornerDescent.Matrix.SelectedCoordinate
