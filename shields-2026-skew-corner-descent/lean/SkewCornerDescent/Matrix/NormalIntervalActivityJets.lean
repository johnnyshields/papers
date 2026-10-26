/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalInverseProductJets

/-!
# Complete inverse-jet contribution of a high interval activity

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A constant complete high numerator gradient leaves the full inverse diagonal
product intact. Its first normal jet counts every original diagonal slope.
The numerator-gradient and diagonal-independence premises are DERIVED; actual
period responses and actual short-entry producers must supply them. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F] [Algebra ℚ F]

private theorem series_deriv_prod_zero {ι : Type*}
    (D : @Derivation ℚ (PowerSeries F) (PowerSeries F) _ _ _ _ _
      (inferInstance : Algebra ℚ (PowerSeries F)).toModule)
    (s : Finset ι) (p : ι → PowerSeries F) (hp : ∀ i ∈ s, D (p i) = 0) :
    D (∏ i ∈ s, p i) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, D.leibniz,
      hp i (Finset.mem_insert_self _ _), ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)),
      smul_zero, smul_zero, add_zero]

/-- The high gradient of the full activity amplitude retains its complete inverse product.
Every original inverse jet remains; only genuine high-generator independence is used. -/
theorem normal_activity_amplitude_gradient {ι : Type*}
    (D : @Derivation ℚ (PowerSeries F) (PowerSeries F) _ _ _ _ _
      (inferInstance : Algebra ℚ (PowerSeries F)).toModule)
    (s : Finset ι) (p : ι → PowerSeries F) (q : PowerSeries F) (γ : F)
    (hunit : ∀ i ∈ s, PowerSeries.constantCoeff (p i) ≠ 0)
    (hdiag : ∀ i ∈ s, D (p i) = 0) (hq : D q = PowerSeries.C γ) :
    D (q * ∏ i ∈ s, (p i)⁻¹) = PowerSeries.C γ * ∏ i ∈ s, (p i)⁻¹ := by
  have hi (i) (his : i ∈ s) : D (p i)⁻¹ = 0 := by
    rw [normal_series_deriv_inverse D (p i) (hunit i his), hdiag i his, mul_zero]
  rw [D.leibniz, series_deriv_prod_zero D s (fun i => (p i)⁻¹) hi,
    hq, smul_zero, zero_add, smul_eq_mul, mul_comm]

/-- The first high normal activity jet is the complete inverse product's actual slope sum.
This is the denominator-jet contribution before its cyclic positional multiplicity is counted. -/
theorem normal_activity_amplitude_gradient_coeff_one {ι : Type*}
    (D : @Derivation ℚ (PowerSeries F) (PowerSeries F) _ _ _ _ _
      (inferInstance : Algebra ℚ (PowerSeries F)).toModule)
    (s : Finset ι) (p : ι → PowerSeries F) (q : PowerSeries F) (γ : F)
    (hunit : ∀ i ∈ s, PowerSeries.constantCoeff (p i) ≠ 0)
    (hdiag : ∀ i ∈ s, D (p i) = 0) (hq : D q = PowerSeries.C γ) :
    PowerSeries.coeff 1 (D (q * ∏ i ∈ s, (p i)⁻¹)) =
      -γ * (∏ i ∈ s, (PowerSeries.constantCoeff (p i))⁻¹) *
        ∑ i ∈ s, PowerSeries.coeff 1 (p i) * (PowerSeries.constantCoeff (p i))⁻¹ := by
  rw [normal_activity_amplitude_gradient D s p q γ hunit hdiag hq,
    PowerSeries.coeff_C_mul, normal_inverse_product_coeff_one s p hunit]
  ring

end SkewCornerDescent.Matrix
