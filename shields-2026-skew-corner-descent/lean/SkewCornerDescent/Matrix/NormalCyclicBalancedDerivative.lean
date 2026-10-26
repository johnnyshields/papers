/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalCyclicChargeDerivative

/-!
# Balanced first-normal pair derivatives

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Exact original weighted counts cancel a uniform moving pair contribution.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix
open scoped BigOperators

/-- Exact weighted occurrence balance cancels the moving pair contribution
when each genuine inverse pair has the same complete residue product. -/
theorem normalCyclicFirstCharge_balanced_deriv {N M : ℕ} {F : Type*}
    [Field F] [Algebra ℚ F] {m : Module ℚ F} [NeZero N] [NeZero M]
    (δ : @Derivation ℚ F F _ _ _ _ _ m)
    (f p : ZMod N → PowerSeries F) (g q : ZMod M → PowerSeries F)
    (α γ Z : F) (b d : ℕ) (hcount : b * N = d * M)
    (hα : δ α = 0)
    (hf0 : ∀ s, δ (PowerSeries.constantCoeff (f s)) = 0)
    (hf1 : ∀ s, δ (PowerSeries.coeff 1 (f s)) = 0)
    (hg0 : ∀ s, δ (PowerSeries.constantCoeff (g s)) = 0)
    (hg1 : ∀ s, δ (PowerSeries.coeff 1 (g s)) = 0)
    (hp : ∀ s, δ (PowerSeries.constantCoeff (p s)) = γ)
    (hq : ∀ s, δ (PowerSeries.constantCoeff (q s)) = γ)
    (hZf : ∀ s, (PowerSeries.constantCoeff (f s))⁻¹ *
      (PowerSeries.constantCoeff (f (s + 1)))⁻¹ = Z)
    (hZg : ∀ s, (PowerSeries.constantCoeff (g s))⁻¹ *
      (PowerSeries.constantCoeff (g (s + 1)))⁻¹ = Z) :
    δ (b • normalCyclicFirstCharge f p α - d • normalCyclicFirstCharge g q α) = 0 := by
  rw [map_sub, map_nsmul, map_nsmul,
    normalCyclicFirstCharge_deriv δ f p α γ hα hf0 hf1 hp,
    normalCyclicFirstCharge_deriv δ g q α γ hα hg0 hg1 hq]
  simp_rw [hZf, hZg]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  have hc : (b : F) * (N : F) = (d : F) * (M : F) := by
    rw [← Nat.cast_mul, ← Nat.cast_mul, hcount]
  calc
    _ = -α * γ * Z * ((b : F) * N - (d : F) * M) := by ring
    _ = 0 := by rw [hc, sub_self, mul_zero]

end SkewCornerDescent.Matrix
