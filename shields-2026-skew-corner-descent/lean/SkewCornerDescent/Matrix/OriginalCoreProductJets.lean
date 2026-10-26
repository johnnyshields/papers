/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalSelectedCoreProfiles

/-!
# Low mixed proper-core product jets of actual original intervals

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`,
`prop:closure-pin`). Both source-selected strips are identified with their own
literal proper cores. Finite coefficient convolution then identifies the entire
low product jet, with no supplied product-jet assumption. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

private theorem polynomial_product_coeff_congr {F : Type*} [CommSemiring F]
    (A B C D : Polynomial F) (k : ℕ)
    (hA : ∀ i ≤ k, A.coeff i = C.coeff i) (hB : ∀ i ≤ k, B.coeff i = D.coeff i) :
    (A * B).coeff k = (C * D).coeff k := by
  rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
  apply Finset.sum_congr rfl
  rintro ⟨i, j⟩ hij
  have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  rw [hA i (by omega), hB j (by omega)]

namespace SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual incoming profile has its source-selected proper core jet,
including degree exactly equal to the selected span. -/
theorem original_left_profile_low_core {n : ℕ} (P : Profile n)
    (b : OriginalSelectedBlocks (hD := hD) P)
    (d : Option (OriginalSelectedBlocks (hD := hD) P))
    (hupper : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P d)
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalResidueLeftEndpointPolynomial P (some b) d).coeff k =
      (c.selectedCoreLeftPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm).coeff k := by
  rw [c.original_left_profile_low_strip P b d k hk,
    c.original_left_strip_eq_selected_core P b d hupper]

/-- The exact symmetric low outgoing core jet is also supplied by the source. -/
theorem original_right_profile_low_core {n : ℕ} (P : Profile n)
    (b : Option (OriginalSelectedBlocks (hD := hD) P))
    (d : OriginalSelectedBlocks (hD := hD) P)
    (hlower : originalResponseLowerCut P b < (interiorBlock P d.val.val : ℤ))
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalResidueRightEndpointPolynomial P b (some d)).coeff k =
      (c.selectedCoreRightPolynomial
        (interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property))
        (originalSelectedProfile_schur P d).symm).coeff k := by
  rw [c.original_right_profile_low_strip P b d k hk,
    c.original_right_strip_eq_selected_core P b d hlower]

/-- The full original interval's low profile-product coefficients are exactly
those of its two own selected proper cores. Every unit and off-diagonal inverse
entry remains in the full profile on the left side. -/
theorem original_profile_product_low_cores {n : ℕ} (P : Profile n)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (horder : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.originalResidueLeftEndpointPolynomial P (some b) (some d) *
      c.originalResidueRightEndpointPolynomial P (some b) (some d)).coeff k =
    (c.selectedCoreLeftPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm *
      c.selectedCoreRightPolynomial
        (interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property))
        (originalSelectedProfile_schur P d).symm).coeff k := by
  have hupper : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P (some d) := by
    change (interiorBlock P b.val.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1
    omega
  have hlower : originalResponseLowerCut P (some b) < (interiorBlock P d.val.val : ℤ) := by
    change (interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P d.val.val : ℤ)
    omega
  apply polynomial_product_coeff_congr
  · intro i hi
    exact c.original_left_profile_low_core P b (some d) hupper i (hi.trans hk)
  · intro i hi
    exact c.original_right_profile_low_core P (some b) d hlower i (hi.trans hk)

/-- Equal actual original responses with common span greater than twice the
selected span give equal low mixed proper-core products. The raw derivative
and both source-core profile bridges supply the complete product comparison. -/
theorem original_equal_response_core_products {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (b' d' : OriginalSelectedBlocks (hD := hD) Q)
    (horderP : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (horderQ : interiorBlock Q b'.val.val ≤ interiorBlock Q d'.val.val)
    (hspan : P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))) =
      Q.xi (originalRowSplitEquiv (hD := hD) Q (.inl (some b'))) -
        Q.zeta (originalColSplitEquiv (hD := hD) Q (.inl (some d'))))
    (hK : 2 * (c.top : ℤ) <
      P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
        P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d))))
    (hresponse : c.regularResidue (c.originalLocalResponse P (some b) (some d)) =
      c.regularResidue (c.originalLocalResponse Q (some b') (some d')))
    (k : ℕ) (hk : k ≤ (c.top : ℕ)) :
    (c.selectedCoreLeftPolynomial
        (interiorBlockProfile P b.val.val (originalBlockSelected_nonempty P b.val b.property))
        (originalSelectedProfile_schur P b).symm *
      c.selectedCoreRightPolynomial
        (interiorBlockProfile P d.val.val (originalBlockSelected_nonempty P d.val d.property))
        (originalSelectedProfile_schur P d).symm).coeff k =
    (c.selectedCoreLeftPolynomial
        (interiorBlockProfile Q b'.val.val (originalBlockSelected_nonempty Q b'.val b'.property))
        (originalSelectedProfile_schur Q b').symm *
      c.selectedCoreRightPolynomial
        (interiorBlockProfile Q d'.val.val (originalBlockSelected_nonempty Q d'.val d'.property))
        (originalSelectedProfile_schur Q d').symm).coeff k := by
  let K := P.xi (originalRowSplitEquiv (hD := hD) P (.inl (some b))) -
    P.zeta (originalColSplitEquiv (hD := hD) P (.inl (some d)))
  have hNK : (c.top : ℤ) < K - (k : ℤ) := by
    dsimp only [K]
    omega
  let j : ℕ+ := ⟨(K - (k : ℤ)).toNat, by have := c.top.pos; omega⟩
  have hj : (j : ℤ) = K - (k : ℤ) := Int.toNat_of_nonneg (by have := c.top.pos; omega)
  have hNj : c.top < j := by
    have he : ((c.top : ℕ) : ℤ) < ((j : ℕ) : ℤ) := by rw [hj]; exact hNK
    exact_mod_cast he
  have hp := congrArg (residueGeneratorDeriv c.top ⟨j, ne_of_gt hNj⟩) hresponse
  rw [c.originalLocalResponse_residue_profile_gradient P (some b) (some d) j hNj,
    c.originalLocalResponse_residue_profile_gradient Q (some b') (some d') j hNj] at hp
  have hdegree : K - (j : ℤ) = (k : ℤ) := by omega
  change (_ : LaurentPolynomial (OtherField c.top)).coeff (K - (j : ℤ)) = _ at hp
  rw [hdegree, ← hspan, hdegree] at hp
  have hnat (p : Polynomial (OtherField c.top)) :
      p.toLaurent.coeff (k : ℤ) = p.coeff k := by
    change (Finsupp.mapDomain (fun x : ℕ => (x : ℤ)) p.toFinsupp.coeff) (k : ℤ) = _
    exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k
  rw [hnat, hnat, c.original_profile_product_low_cores P b d horderP k hk,
    c.original_profile_product_low_cores Q b' d' horderQ k hk] at hp
  exact hp

end SelectedCoordinate
end SkewCornerDescent.Matrix
