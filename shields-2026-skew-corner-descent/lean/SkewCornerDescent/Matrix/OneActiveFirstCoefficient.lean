/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalInverseProductJets

/-!
# Complete first coefficient of a residue-matched one-active comparison

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
All three original series retain their actual first jets. Exact residue matching
and produced unit constants turn the ratio's first coefficient into the signed
sum of complete logarithmic slopes, including the whole closure denominator.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F]

private theorem first_slope_mul (p q : PowerSeries F)
    (hp : PowerSeries.constantCoeff p ≠ 0) (hq : PowerSeries.constantCoeff q ≠ 0) :
    PowerSeries.coeff 1 (p * q) * (PowerSeries.constantCoeff (p * q))⁻¹ =
      PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹ +
        PowerSeries.coeff 1 q * (PowerSeries.constantCoeff q)⁻¹ := by
  rw [PowerSeries.coeff_one_mul, map_mul]
  field_simp [hp, hq]

private theorem first_slope_inverse (p : PowerSeries F)
    (hp : PowerSeries.constantCoeff p ≠ 0) :
    PowerSeries.coeff 1 p⁻¹ * (PowerSeries.constantCoeff p⁻¹)⁻¹ =
      -(PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹) := by
  rw [normal_inverse_coeff_one p hp, PowerSeries.constantCoeff_inv, inv_inv]
  field_simp [hp]

private theorem first_slope_pow (p : PowerSeries F)
    (hp : PowerSeries.constantCoeff p ≠ 0) (n : ℕ) :
    PowerSeries.coeff 1 (p ^ n) * (PowerSeries.constantCoeff (p ^ n))⁻¹ =
      (n : F) * (PowerSeries.coeff 1 p * (PowerSeries.constantCoeff p)⁻¹) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, first_slope_mul _ _ (by simpa using pow_ne_zero n hp) hp, ih]
    push_cast
    ring

/-- Exact original residue matching supplies the whole ratio's first coefficient,
including its actual constant orientation scalar. Every first jet remains;
the scalar's nonvanishing follows from residue matching and the three unit constants. -/
theorem one_active_comparison_coeff_one (E f T : PowerSeries F) (κ : F) (b v d : ℕ)
    (hE : PowerSeries.constantCoeff E ≠ 0)
    (hf : PowerSeries.constantCoeff f ≠ 0)
    (hT : PowerSeries.constantCoeff T ≠ 0)
    (hmatch : PowerSeries.constantCoeff E ^ b =
      κ * (PowerSeries.constantCoeff f ^ v * PowerSeries.constantCoeff T ^ d)) :
    PowerSeries.coeff 1 (PowerSeries.C κ⁻¹ * (E ^ b * (f ^ v * T ^ d)⁻¹)) =
      (b : F) * (PowerSeries.coeff 1 E * (PowerSeries.constantCoeff E)⁻¹) -
      (v : F) * (PowerSeries.coeff 1 f * (PowerSeries.constantCoeff f)⁻¹) -
      (d : F) * (PowerSeries.coeff 1 T * (PowerSeries.constantCoeff T)⁻¹) := by
  have hden : PowerSeries.constantCoeff (f ^ v * T ^ d) ≠ 0 := by
    rw [map_mul, map_pow, map_pow]
    exact mul_ne_zero (pow_ne_zero v hf) (pow_ne_zero d hT)
  have hEpow : PowerSeries.constantCoeff (E ^ b) ≠ 0 := by
    simpa using pow_ne_zero b hE
  have hfPow : PowerSeries.constantCoeff (f ^ v) ≠ 0 := by
    simpa using pow_ne_zero v hf
  have hTPow : PowerSeries.constantCoeff (T ^ d) ≠ 0 := by
    simpa using pow_ne_zero d hT
  have hunit : PowerSeries.constantCoeff (E ^ b * (f ^ v * T ^ d)⁻¹) = κ := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_inv, map_mul, map_pow, map_pow,
      hmatch, mul_assoc,
      mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero v hf) (pow_ne_zero d hT)), mul_one]
  calc
    _ = PowerSeries.coeff 1 (E ^ b * (f ^ v * T ^ d)⁻¹) *
        (PowerSeries.constantCoeff (E ^ b * (f ^ v * T ^ d)⁻¹))⁻¹ := by
      rw [PowerSeries.coeff_C_mul, hunit]
      exact mul_comm _ _
    _ = _ := by
      rw [first_slope_mul _ _ hEpow (by
        rw [PowerSeries.constantCoeff_inv]
        exact inv_ne_zero hden), first_slope_pow E hE b,
        first_slope_inverse _ hden, first_slope_mul _ _ hfPow hTPow,
        first_slope_pow f hf v, first_slope_pow T hT d]
      ring

end SkewCornerDescent.Matrix
