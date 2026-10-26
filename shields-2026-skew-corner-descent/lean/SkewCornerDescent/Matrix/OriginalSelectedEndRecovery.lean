/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalCoreProductJets
import SkewCornerDescent.Matrix.SelectedCoreLiteralTransport
import SkewCornerDescent.Matrix.SelectedCoreSeries

/-!
# Literal selected-end recovery from complete interval profiles

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`).
Actual low-core profile bridges and the common selected gradient recover both
normalized selected ending components from visible full endpoint coefficients.
The opposite core profile is produced, not assumed. Whole intervening unit
blocks and a possible midpoint vertex are separate obligations. Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate
open SkewGluing
variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The full right-core jet determines its left mate and hence the actual
normalized selected component. The common product is produced from its prime. -/
theorem selected_core_literal_of_right_jet {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (hright : ∀ k < (c.top : ℕ),
      (c.selectedCoreRightPolynomial P hP).coeff k =
        (c.selectedCoreRightPolynomial Q hQ).coeff k) : P.cells = Q.cells := by
  have hleft := SkewCornerDescent.unit_jet_product_right
    (c.selectedCoreRightPolynomial P hP : PowerSeries (OtherField c.top))
    (c.selectedCoreLeftPolynomial P hP : PowerSeries (OtherField c.top))
    (c.selectedCoreRightPolynomial Q hQ : PowerSeries (OtherField c.top))
    (c.selectedCoreLeftPolynomial Q hQ : PowerSeries (OtherField c.top))
    (c.top : ℕ) ?_ ?_ ?_
  · apply c.selected_core_literal_of_left_jet P Q hP hQ
    simpa only [Polynomial.coeff_coe] using hleft
  · rw [← PowerSeries.coeff_zero_eq_constantCoeff,
      Polynomial.coeff_coe, c.selected_core_right_constant P hP]
    exact one_ne_zero
  · intro k hk
    simpa only [Polynomial.coeff_coe] using hright k hk
  · intro k hk
    simp only [← Polynomial.coe_mul, Polynomial.coeff_coe]
    rw [mul_comm (c.selectedCoreRightPolynomial P hP),
      mul_comm (c.selectedCoreRightPolynomial Q hQ)]
    exact c.selected_core_polynomial_product_coeff_eq P Q hP hQ k hk

/-- The visible part of the actual full incoming profiles already recovers
both normalized selected starting components, with every other inverse coupling
retained in the profiles being compared. -/
theorem original_selected_start_core_literal {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (b' d' : OriginalSelectedBlocks (hD := hD) Q)
    (horderP : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (horderQ : interiorBlock Q b'.val.val ≤ interiorBlock Q d'.val.val)
    (K : ℤ) (hK : 2 * (c.top : ℤ) < K)
    (hcoeff : ∀ k : ℕ, 2 * (k : ℤ) < K →
      (c.originalResidueLeftEndpointPolynomial P (some b) (some d)).coeff k =
        (c.originalResidueLeftEndpointPolynomial Q (some b') (some d')).coeff k) :
    (interiorBlockProfile P b.val.val
      (originalBlockSelected_nonempty P b.val b.property)).cells =
      (interiorBlockProfile Q b'.val.val
        (originalBlockSelected_nonempty Q b'.val b'.property)).cells := by
  have hupperP : (interiorBlock P b.val.val : ℤ) < originalResponseUpperCut P (some d) := by
    change (interiorBlock P b.val.val : ℤ) < (interiorBlock P d.val.val : ℤ) + 1
    omega
  have hupperQ : (interiorBlock Q b'.val.val : ℤ) < originalResponseUpperCut Q (some d') := by
    change (interiorBlock Q b'.val.val : ℤ) < (interiorBlock Q d'.val.val : ℤ) + 1
    omega
  apply c.selected_core_literal_of_left_jet _ _
    (originalSelectedProfile_schur P b).symm (originalSelectedProfile_schur Q b').symm
  intro k hk
  rw [← c.original_left_profile_low_core P b (some d) hupperP k hk.le,
    ← c.original_left_profile_low_core Q b' (some d') hupperQ k hk.le]
  exact hcoeff k (by omega)

/-- The symmetric visible outgoing profiles recover the full normalized
selected ending components, not merely their common Schur function. -/
theorem original_selected_end_core_literal {n m : ℕ} (P : Profile n) (Q : Profile m)
    (b d : OriginalSelectedBlocks (hD := hD) P)
    (b' d' : OriginalSelectedBlocks (hD := hD) Q)
    (horderP : interiorBlock P b.val.val ≤ interiorBlock P d.val.val)
    (horderQ : interiorBlock Q b'.val.val ≤ interiorBlock Q d'.val.val)
    (K : ℤ) (hK : 2 * (c.top : ℤ) < K)
    (hcoeff : ∀ k : ℕ, 2 * (k : ℤ) < K →
      (c.originalResidueRightEndpointPolynomial P (some b) (some d)).coeff k =
        (c.originalResidueRightEndpointPolynomial Q (some b') (some d')).coeff k) :
    (interiorBlockProfile P d.val.val
      (originalBlockSelected_nonempty P d.val d.property)).cells =
      (interiorBlockProfile Q d'.val.val
        (originalBlockSelected_nonempty Q d'.val d'.property)).cells := by
  have hlowerP : originalResponseLowerCut P (some b) < (interiorBlock P d.val.val : ℤ) := by
    change (interiorBlock P b.val.val : ℤ) - 1 < (interiorBlock P d.val.val : ℤ)
    omega
  have hlowerQ : originalResponseLowerCut Q (some b') < (interiorBlock Q d'.val.val : ℤ) := by
    change (interiorBlock Q b'.val.val : ℤ) - 1 < (interiorBlock Q d'.val.val : ℤ)
    omega
  apply c.selected_core_literal_of_right_jet _ _
    (originalSelectedProfile_schur P d).symm (originalSelectedProfile_schur Q d').symm
  intro k hk
  rw [← c.original_right_profile_low_core P (some b) d hlowerP k hk.le,
    ← c.original_right_profile_low_core Q (some b') d' hlowerQ k hk.le]
  exact hcoeff k (by omega)

end SkewCornerDescent.Matrix.SelectedCoordinate
