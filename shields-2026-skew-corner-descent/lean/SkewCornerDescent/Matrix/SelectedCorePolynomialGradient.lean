/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.SelectedCoreSeries
import SkewCornerDescent.Matrix.OriginalNormalHessenberg

/-!
# Proper-core polynomial coefficients are the actual raw selected-function gradient

Supports `shields-2026-skew-corner-descent.tex` (`lem:early-recovery`, `prop:normal-interface`).
The actual affine coefficient equals the raw top partial before taking residue.
It therefore normalizes each literal selected-core product coefficient without
assuming a common gradient or differentiating the identically zero residue.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing MvPolynomial

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- The actual affine normal coefficient is the raw top partial of the original selected prime. -/
theorem selected_prime_top_partial :
    MvPolynomial.pderiv c.top (cellSchur D hD.1) = c.coefficient := by
  rw [c.prime_eq]
  simp [affineCoordinate, MvPolynomial.pderiv_eq_zero_of_notMem_vars c.top_notMem_coefficient,
    MvPolynomial.pderiv_eq_zero_of_notMem_vars c.top_notMem_remainder]

/-- The complete top cofactor has exactly its original residue normal coefficient. -/
theorem residue_coefficient_eq_normal : c.residueMap c.coefficient = c.normalCoefficient := by
  have h := congrArg PowerSeries.constantCoeff c.normalSeries_coefficient
  simpa only [c.normalSeries_constant_apply, c.regularResidue_polynomial,
    PowerSeries.constantCoeff_C] using h

private theorem coeff_toLaurent_nat {R : Type*} [CommRing R] (p : Polynomial R) (k : ℕ) :
    p.toLaurent.coeff (k : ℤ) = p.coeff k := by
  change (Finsupp.mapDomain (fun x : ℕ => (x : ℤ)) p.toFinsupp.coeff) (k : ℤ) = _
  exact Finsupp.mapDomain_apply_of_injective Nat.cast_injective _ k

/-- Every low proper-core product coefficient is the full raw selected-function gradient,
normalized by its actual top cofactor. The natural/Laurent representation bridge is proved. -/
theorem selected_core_polynomial_product_gradient {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (J : ℕ+) (k : ℕ)
    (hdegree : (c.top : ℤ) - (J : ℤ) = (k : ℤ)) :
    c.normalCoefficient *
        (c.selectedCoreLeftPolynomial P hP * c.selectedCoreRightPolynomial P hP).coeff k =
      c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1)) := by
  have hcorner : ((jtMatrix P.xi P.zeta).map c.residueMap).adjugate (Fin.last n) 0 =
      c.normalCoefficient := by
    rw [← c.original_profile_top_gradient P, ← c.top_eq_profile P hP, ← hP,
      c.selected_prime_top_partial, c.residue_coefficient_eq_normal]
  have h := c.selected_core_profile_product_gradient P hP J
  rw [hcorner, ← c.selected_core_left_toLaurent P hP,
    ← c.selected_core_right_toLaurent P hP, ← map_mul, hdegree, coeff_toLaurent_nat,
    ← hP] at h
  exact h

/-- Dividing by the produced nonzero cofactor gives the actual normalized raw gradient. -/
theorem selected_core_polynomial_product_coeff {n : ℕ} (P : Profile n)
    (hP : cellSchur D hD.1 = P.schur) (J : ℕ+) (k : ℕ)
    (hdegree : (c.top : ℤ) - (J : ℤ) = (k : ℤ)) :
    (c.selectedCoreLeftPolynomial P hP * c.selectedCoreRightPolynomial P hP).coeff k =
      c.normalCoefficient⁻¹ * c.residueMap (MvPolynomial.pderiv J (cellSchur D hD.1)) := by
  rw [← c.selected_core_polynomial_product_gradient P hP J k hdegree]
  simp only [← mul_assoc, inv_mul_cancel₀ c.normalCoefficient_ne_zero, one_mul]

end SkewCornerDescent.Matrix.SelectedCoordinate
