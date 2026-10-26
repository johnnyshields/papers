/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.OriginalNormalDerivative

/-!
# Coefficientwise surviving-generator derivations of complete normal series

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
A genuine coefficient derivation acts on every complete normal jet. The
construction uses its additive map, rational-constant rule and full Leibniz
identity, avoiding an implicit change of the coefficient field's module convention.
Sorry-free.
-/

noncomputable section

namespace SkewCornerDescent.Matrix

variable {F : Type*} [CommRing F] [Algebra ℚ F]

/-- Extend a genuine additive coefficient derivation through every complete normal series.
Its rational and Leibniz laws are supplied explicitly and proved for the resulting series map. -/
def powerSeriesCoefficientDerivation (D : F →+ F)
    (hRat : ∀ q : ℚ, D (algebraMap ℚ F q) = 0)
    (hOne : D 1 = 0) (hMul : ∀ f g : F, D (f * g) = f * D g + g * D f) :
    @Derivation ℚ (PowerSeries F) (PowerSeries F) _ _ _ _ _
      (inferInstance : Algebra ℚ (PowerSeries F)).toModule where
  toFun f := PowerSeries.mk fun n => D (PowerSeries.coeff n f)
  map_add' f g := by
    ext n
    simp only [PowerSeries.coeff_mk, map_add]
  map_smul' q f := by
    ext n
    simp only [PowerSeries.coeff_mk, Algebra.smul_def, RingHom.id_apply]
    rw [PowerSeries.algebraMap_apply, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, hMul, hRat, mul_zero, add_zero]
  map_one_eq_zero' := by
    ext n
    change PowerSeries.coeff n (PowerSeries.mk (fun n => D (PowerSeries.coeff n 1))) = 0
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs <;> simp [hOne]
  leibniz' f g := by
    ext n
    simp only [smul_eq_mul]
    change PowerSeries.coeff n (PowerSeries.mk (fun n => D (PowerSeries.coeff n (f * g)))) =
      PowerSeries.coeff n (f * PowerSeries.mk (fun n => D (PowerSeries.coeff n g)) +
        g * PowerSeries.mk (fun n => D (PowerSeries.coeff n f)))
    rw [mul_comm g (PowerSeries.mk (fun n => D (PowerSeries.coeff n f)))]
    simp only [PowerSeries.coeff_mul, map_sum, map_add, PowerSeries.coeff_mk, hMul,
      Finset.sum_add_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact mul_comm _ _

/-- The complete series derivation acts on exactly its original coefficient at every order. -/
theorem powerSeriesCoefficientDerivation_coeff (D : F →+ F)
    (hRat : ∀ q : ℚ, D (algebraMap ℚ F q) = 0)
    (hOne : D 1 = 0) (hMul : ∀ f g : F, D (f * g) = f * D g + g * D f)
    (f : PowerSeries F) (n : ℕ) :
    PowerSeries.coeff n (powerSeriesCoefficientDerivation D hRat hOne hMul f) =
      D (PowerSeries.coeff n f) := by
  change PowerSeries.coeff n (PowerSeries.mk (fun n => D (PowerSeries.coeff n f))) = _
  exact PowerSeries.coeff_mk n _

/-- Constant series retain their genuine coefficient derivative, rather than being frozen. -/
theorem powerSeriesCoefficientDerivation_C (D : F →+ F)
    (hRat : ∀ q : ℚ, D (algebraMap ℚ F q) = 0)
    (hOne : D 1 = 0) (hMul : ∀ f g : F, D (f * g) = f * D g + g * D f) (x : F) :
    powerSeriesCoefficientDerivation D hRat hOne hMul (PowerSeries.C x) = PowerSeries.C (D x) := by
  ext n
  rw [powerSeriesCoefficientDerivation_coeff, PowerSeries.coeff_C, PowerSeries.coeff_C]
  split_ifs <;> simp

/-- The normal variable itself is independent of every coefficient-field generator. -/
theorem powerSeriesCoefficientDerivation_X (D : F →+ F)
    (hRat : ∀ q : ℚ, D (algebraMap ℚ F q) = 0)
    (hOne : D 1 = 0) (hMul : ∀ f g : F, D (f * g) = f * D g + g * D f) :
    powerSeriesCoefficientDerivation D hRat hOne hMul PowerSeries.X = 0 := by
  ext n
  rw [powerSeriesCoefficientDerivation_coeff, PowerSeries.coeff_X, map_zero]
  split_ifs <;> simp [hOne]

end SkewCornerDescent.Matrix
