/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalPrefixCycles
import SkewCornerDescent.Matrix.ResidueGeneratorDerivation

/-!
# Protected derivatives of complete first-normal cyclic charges

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full onsite jets and genuine adjacent-entry gradients are retained.
Only their produced higher-generator derivatives are factored. Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open scoped BigOperators

/-- The derivative retains the full onsite jet and both genuine pair endpoints.
If only the pair entries move, their common gradient factors out of the cycle. -/
theorem normalCyclicFirstCharge_deriv {T : ℕ} {F : Type*} [Field F] [Algebra ℚ F]
    {m : Module ℚ F} [NeZero T] (δ : @Derivation ℚ F F _ _ _ _ _ m)
    (f q : ZMod T → PowerSeries F) (b γ : F)
    (hb : δ b = 0) (hf0 : ∀ s, δ (PowerSeries.constantCoeff (f s)) = 0)
    (hf1 : ∀ s, δ (PowerSeries.coeff 1 (f s)) = 0)
    (hq : ∀ s, δ (PowerSeries.constantCoeff (q s)) = γ) :
    δ (normalCyclicFirstCharge f q b) =
      -(b * γ) * ∑ s : ZMod T,
        (PowerSeries.constantCoeff (f s))⁻¹ *
          (PowerSeries.constantCoeff (f (s + 1)))⁻¹ := by
  simp only [normalCyclicFirstCharge, map_sub, map_sum, δ.leibniz, δ.leibniz_inv,
    hb, hf0, hf1, hq, smul_eq_mul, mul_zero, zero_add, add_zero,
    Finset.sum_const_zero, zero_sub]
  simp_rw [Finset.mul_sum, neg_mul, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro s _
  ring

/-- When every true adjacent entry is also fixed, the entire first-normal
cyclic charge is independent of the protected generator. -/
theorem normalCyclicFirstCharge_deriv_zero {T : ℕ} {F : Type*} [Field F] [Algebra ℚ F]
    {m : Module ℚ F} [NeZero T] (δ : @Derivation ℚ F F _ _ _ _ _ m)
    (f q : ZMod T → PowerSeries F) (b : F)
    (hb : δ b = 0) (hf0 : ∀ s, δ (PowerSeries.constantCoeff (f s)) = 0)
    (hf1 : ∀ s, δ (PowerSeries.coeff 1 (f s)) = 0)
    (hq : ∀ s, δ (PowerSeries.constantCoeff (q s)) = 0) :
    δ (normalCyclicFirstCharge f q b) = 0 := by
  rw [normalCyclicFirstCharge_deriv δ f q b 0 hb hf0 hf1 hq]
  ring

end SkewCornerDescent.Matrix
