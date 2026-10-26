/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedCorePolynomialGradient

/-!
# Cross-core product coefficients on a matched proper-core phase

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A matched outgoing proper-core jet identifies the cross product with the actual
raw selected-function gradient. The phase-matching premise is DERIVED; the original
source phase producer must supply it before the normal comparison closes.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- A produced common outgoing core jet normalizes the full cross-core coefficient
by the actual selected top cofactor, not by an assumed common gradient. -/
theorem selected_core_cross_polynomial_gradient {n m : ℕ} (P : Profile n) (Q : Profile m)
    (hP : cellSchur D hD.1 = P.schur) (hQ : cellSchur D hD.1 = Q.schur)
    (J : ℕ+) (k : ℕ) (hdegree : (c.top : ℤ) - (J : ℤ) = (k : ℤ))
    (hright : ∀ i ≤ k, (c.selectedCoreRightPolynomial Q hQ).coeff i =
      (c.selectedCoreRightPolynomial P hP).coeff i) :
    (c.selectedCoreLeftPolynomial P hP * c.selectedCoreRightPolynomial Q hQ).coeff k =
      c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1)) := by
  calc
    _ = (c.selectedCoreLeftPolynomial P hP * c.selectedCoreRightPolynomial P hP).coeff k := by
      rw [Polynomial.coeff_mul, Polynomial.coeff_mul]
      apply Finset.sum_congr rfl
      rintro ⟨i, j⟩ hij
      have h := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [hright j (by omega)]
    _ = _ := c.selected_core_polynomial_product_coeff P hP J k hdegree

end SkewCornerDescent.Matrix.SelectedCoordinate
