/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalResidueEndpointProfiles

/-!
# Actual profile product jets from equal complete original responses

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Higher-generator differentiation supplies equality of the full endpoint
product coefficient below the half-span. No product coefficient equality is
carried as an extra premise. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- Equal actual residue responses of the same selected-to-selected span
have equal full profile-product jets below half that span. -/
theorem original_equal_response_profile_product_jet {n m : ℕ}
    (P : Profile n) (Q : Profile m)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (b' d' : Option (OriginalSelectedBlocks (hD := hD) Q))
    (K : ℕ+) (hKN : 2 * (c.top : ℕ) < (K : ℕ))
    (hspanP : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hspanQ : Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl b')) -
      Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl d')) = (K : ℤ))
    (hresponse : c.regularResidue (c.originalLocalResponse P b d) =
      c.regularResidue (c.originalLocalResponse Q b' d'))
    (w : ℕ) (hw : 2 * w < (K : ℕ)) :
    (c.originalResidueLeftEndpointPolynomial P b d *
        c.originalResidueRightEndpointPolynomial P b d).coeff w =
      (c.originalResidueLeftEndpointPolynomial Q b' d' *
        c.originalResidueRightEndpointPolynomial Q b' d').coeff w := by
  let j : ℕ+ := ⟨(K : ℕ) - w, by omega⟩
  have hj : c.top < j := by change (c.top : ℕ) < (K : ℕ) - w; omega
  have hexp : (K : ℤ) - (j : ℤ) = (w : ℤ) := by
    change ((K : ℕ) : ℤ) - (((K : ℕ) - w : ℕ) : ℤ) = (w : ℤ)
    omega
  have h := congrArg (residueGeneratorDeriv c.top ⟨j, ne_of_gt hj⟩) hresponse
  rw [c.originalLocalResponse_residue_profile_gradient P b d j hj,
    c.originalLocalResponse_residue_profile_gradient Q b' d' j hj,
    hspanP, hspanQ, hexp] at h
  have hcoeff (f : Polynomial (OtherField c.top)) : f.toLaurent.coeff (w : ℤ) = f.coeff w := by
    change (Finsupp.mapDomain (fun k : ℕ => (k : ℤ)) f.toFinsupp.coeff) (w : ℤ) = _
    exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ w
  rwa [hcoeff, hcoeff] at h

/-- A visible difference between two equal actual responses has a least degree
and nonzero opposite endpoint differences. Existence of a visible discrepancy is
the input here; complete-list reconstruction is a separate obligation. -/
theorem original_visible_first_difference {n m : ℕ}
    (P : Profile n) (Q : Profile m)
    (b d : Option (OriginalSelectedBlocks (hD := hD) P))
    (b' d' : Option (OriginalSelectedBlocks (hD := hD) Q))
    (K : ℕ+) (hKN : 2 * (c.top : ℕ) < (K : ℕ))
    (hspanP : P.xi (originalRowSplitEquiv (hD := hD) P (.inl b)) -
      P.zeta (originalColSplitEquiv (hD := hD) P (.inl d)) = (K : ℤ))
    (hspanQ : Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl b')) -
      Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl d')) = (K : ℤ))
    (hresponse : c.regularResidue (c.originalLocalResponse P b d) =
      c.regularResidue (c.originalLocalResponse Q b' d'))
    (hvisible : ∃ k, 2 * k < (K : ℕ) ∧
      ((c.originalResidueLeftEndpointPolynomial P b d).coeff k ≠
        (c.originalResidueLeftEndpointPolynomial Q b' d').coeff k ∨
      (c.originalResidueRightEndpointPolynomial P b d).coeff k ≠
        (c.originalResidueRightEndpointPolynomial Q b' d').coeff k)) :
    ∃ w, 0 < w ∧ 2 * w < (K : ℕ) ∧
      (∀ k < w, (c.originalResidueLeftEndpointPolynomial P b d).coeff k =
        (c.originalResidueLeftEndpointPolynomial Q b' d').coeff k) ∧
      (∀ k < w, (c.originalResidueRightEndpointPolynomial P b d).coeff k =
        (c.originalResidueRightEndpointPolynomial Q b' d').coeff k) ∧
      (c.originalResidueLeftEndpointPolynomial P b d).coeff w -
        (c.originalResidueLeftEndpointPolynomial Q b' d').coeff w ≠ 0 ∧
      (c.originalResidueLeftEndpointPolynomial P b d).coeff w -
        (c.originalResidueLeftEndpointPolynomial Q b' d').coeff w =
      -((c.originalResidueRightEndpointPolynomial P b d).coeff w -
        (c.originalResidueRightEndpointPolynomial Q b' d').coeff w) := by
  classical
  let w := Nat.find hvisible
  have hw := Nat.find_spec hvisible
  change 2 * w < (K : ℕ) ∧ _ at hw
  have hzero : w ≠ 0 := by
    intro hz
    rcases hw.2 with h | h
    · apply h
      change (c.originalResidueLeftEndpointPolynomial P b d).coeff w =
        (c.originalResidueLeftEndpointPolynomial Q b' d').coeff w
      rw [hz, c.originalResidueLeftEndpointPolynomial_coeff_zero,
        c.originalResidueLeftEndpointPolynomial_coeff_zero]
    · apply h
      change (c.originalResidueRightEndpointPolynomial P b d).coeff w =
        (c.originalResidueRightEndpointPolynomial Q b' d').coeff w
      rw [hz, c.originalResidueRightEndpointPolynomial_coeff_zero,
        c.originalResidueRightEndpointPolynomial_coeff_zero]
  have hleft : ∀ k < w, (c.originalResidueLeftEndpointPolynomial P b d).coeff k =
      (c.originalResidueLeftEndpointPolynomial Q b' d').coeff k := by
    intro k hk
    by_contra he
    exact Nat.find_min hvisible hk ⟨by omega, Or.inl he⟩
  have hright : ∀ k < w, (c.originalResidueRightEndpointPolynomial P b d).coeff k =
      (c.originalResidueRightEndpointPolynomial Q b' d').coeff k := by
    intro k hk
    by_contra he
    exact Nat.find_min hvisible hk ⟨by omega, Or.inr he⟩
  have hop := c.original_response_first_differences_opposite P Q b d b' d'
    (hspanP.trans hspanQ.symm) hresponse w (by rw [hspanP]; omega) hleft hright
  refine ⟨w, Nat.pos_of_ne_zero hzero, hw.1, hleft, hright, ?_, hop⟩
  intro he
  have hl := sub_eq_zero.mp he
  have hr := sub_eq_zero.mp (neg_eq_zero.mp (hop.symm.trans he))
  exact hw.2.elim (fun h => h hl) (fun h => h hr)

end SkewCornerDescent.Matrix.SelectedCoordinate
