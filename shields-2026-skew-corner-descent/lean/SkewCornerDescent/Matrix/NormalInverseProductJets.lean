/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalSeries
import SkewCornerDescent.Matrix.NormalCoefficientLeibniz

/-!
# Complete first normal jets of inverse diagonal products

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Every complete diagonal inverse contributes its actual first jet. The full
finite product gives the negative weighted sum of all original diagonal slopes,
including repeated occurrences. Genuine nonzero residues supply each inverse.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F]

/-- The complete reciprocal's first jet follows from its genuine inverse identity.
No residue-only reciprocal is substituted for the original normal series. -/
theorem normal_inverse_coeff_one (p : PowerSeries F) (hp : PowerSeries.constantCoeff p ≠ 0) :
    PowerSeries.coeff 1 p⁻¹ = -(PowerSeries.constantCoeff p)⁻¹ ^ 2 * PowerSeries.coeff 1 p := by
  have h := congrArg (PowerSeries.coeff 1) (PowerSeries.mul_inv_cancel p hp)
  rw [PowerSeries.coeff_one_mul, PowerSeries.constantCoeff_inv, PowerSeries.coeff_one] at h
  norm_num at h
  have hm := congrArg (fun x : F => x * (PowerSeries.constantCoeff p)⁻¹) h
  simp only [add_mul, mul_assoc, mul_inv_cancel₀ hp, mul_one, zero_mul] at hm
  linear_combination hm

/-- The first jet of the entire complete inverse diagonal product retains every
original slope and every repeated position. All inverses have produced unit residues. -/
theorem normal_inverse_product_coeff_one {ι : Type*} (s : Finset ι) (p : ι → PowerSeries F)
    (hp : ∀ i ∈ s, PowerSeries.constantCoeff (p i) ≠ 0) :
    PowerSeries.coeff 1 (∏ i ∈ s, (p i)⁻¹) =
      -(∏ i ∈ s, (PowerSeries.constantCoeff (p i))⁻¹) *
        ∑ i ∈ s, PowerSeries.coeff 1 (p i) * (PowerSeries.constantCoeff (p i))⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, PowerSeries.coeff_one_mul,
      normal_inverse_coeff_one (p i) (hp i (Finset.mem_insert_self _ _)),
      map_prod, PowerSeries.constantCoeff_inv,
      ih (fun j hj => hp j (Finset.mem_insert_of_mem hj)),
      Finset.prod_insert hi, Finset.sum_insert hi]
    simp only [PowerSeries.constantCoeff_inv]
    ring

/-- A coefficient derivation retains the full reciprocal derivative on its genuine unit domain. -/
theorem normal_series_deriv_inverse [Algebra ℚ F]
    (D : @Derivation ℚ (PowerSeries F) (PowerSeries F) _ _ _ _ _
      (inferInstance : Algebra ℚ (PowerSeries F)).toModule)
    (p : PowerSeries F) (hp : PowerSeries.constantCoeff p ≠ 0) :
    D p⁻¹ = -p⁻¹ ^ 2 * D p := by
  simpa only [smul_eq_mul] using D.leibniz_of_mul_eq_one (PowerSeries.inv_mul_cancel p hp)

end SkewCornerDescent.Matrix
