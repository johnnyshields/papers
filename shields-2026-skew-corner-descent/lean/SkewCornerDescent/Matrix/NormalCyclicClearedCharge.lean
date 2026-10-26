/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalPrefixCycles

/-!
# Exact clearing of the common actual residue in cyclic first charges

Supports `shields-2026-skew-corner-descent.tex` (`thm:pure-primitive-first`).
The common onsite residue may depend on the resolving generator. Multiplying
the actual first-normal charge by its square clears the complete onsite
and pair denominators without replacing any normal germ by a constant.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open scoped BigOperators

/-- Clear the actual common residue denominator of a complete cyclic first
charge. In particular, this formula does not require the residue to be
independent of a later resolving generator. -/
theorem normalCyclicFirstCharge_clear_common_residue {F : Type*} [Field F]
    {T : ℕ} [NeZero T] (f q : ZMod T → PowerSeries F)
    (a S : F) (ha : a ≠ 0) (hS : S ≠ 0)
    (hf : ∀ i, PowerSeries.constantCoeff (f i) = S) :
    a * S^2 * normalCyclicFirstCharge f q a⁻¹ =
      a*S*(∑ i, PowerSeries.coeff 1 (f i)) - ∑ i, PowerSeries.constantCoeff (q i) := by
  simp_rw [normalCyclicFirstCharge, hf]
  rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul]
  field_simp

/-- The weighted two-cycle charge has exactly the complete cleared onsite
and pair numerator, with both actual normal families retained. -/
theorem weighted_normalCyclicFirstCharge_clear_common_residue {F : Type*} [Field F]
    {b d : ℕ} [NeZero b] [NeZero d]
    (fP qP : ZMod d → PowerSeries F) (fQ qQ : ZMod b → PowerSeries F)
    (a S : F) (ha : a ≠ 0) (hS : S ≠ 0)
    (hP : ∀ i, PowerSeries.constantCoeff (fP i) = S)
    (hQ : ∀ i, PowerSeries.constantCoeff (fQ i) = S) :
    a*S^2 * (b • normalCyclicFirstCharge fP qP a⁻¹ -
      d • normalCyclicFirstCharge fQ qQ a⁻¹) =
      a*S*((b : F)*(∑ i, PowerSeries.coeff 1 (fP i)) -
        (d : F)*(∑ i, PowerSeries.coeff 1 (fQ i))) -
      ((b : F)*(∑ i, PowerSeries.constantCoeff (qP i)) -
        (d : F)*(∑ i, PowerSeries.constantCoeff (qQ i))) := by
  have hp := normalCyclicFirstCharge_clear_common_residue fP qP a S ha hS hP
  have hq := normalCyclicFirstCharge_clear_common_residue fQ qQ a S ha hS hQ
  simp only [nsmul_eq_mul]
  linear_combination (b : F)*hp - (d : F)*hq

/-- Equal produced cycle lengths give the same charge of the unchanged
actual matrix. This identifies the dependent cyclic index types explicitly. -/
theorem normalCyclicFirstCharge_matrix_length_congr {F : Type*} [Field F]
    {N T U : ℕ} [NeZero T] [NeZero U]
    (M : Matrix (Fin N) (Fin N) (PowerSeries F)) (a : F)
    (hT : T ≤ N - 1) (hU : U ≤ N - 1) (h : T = U) :
    normalCyclicFirstCharge (normalDiagonalCycle M (show T ≤ N by omega))
      (normalAdjacentCycle M hT) a =
    normalCyclicFirstCharge (normalDiagonalCycle M (show U ≤ N by omega))
      (normalAdjacentCycle M hU) a := by
  subst U
  rfl

end SkewCornerDescent.Matrix
