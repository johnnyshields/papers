/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.FormalLogProduct

/-!
# Complete normalized logarithms of scalar factors and balanced products

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
Exact constant normalization removes orientation scalars. Exact product powers
cancel the whole logarithm at every normal order, not only a fresh derivative.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- A nonzero constant orientation scalar changes no normalized logarithm. -/
theorem normalized_log_constant_mul {F : Type*} [Field F] [Algebra ℚ F]
    (p : PowerSeries F) (κ : F) (hκ : κ ≠ 0) :
    PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff (PowerSeries.C κ * p))⁻¹ * (PowerSeries.C κ * p)) =
      PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p) := by
  have hc : ((κ * PowerSeries.constantCoeff p)⁻¹) * κ =
      (PowerSeries.constantCoeff p)⁻¹ := by
    rw [mul_inv_rev, mul_assoc, inv_mul_cancel₀ hκ, mul_one]
  apply congrArg PowerSeries.logOf
  calc
    _ = PowerSeries.C (κ * PowerSeries.constantCoeff p)⁻¹ * (PowerSeries.C κ * p) := by
      rw [map_mul, PowerSeries.constantCoeff_C]
    _ = PowerSeries.C (((κ * PowerSeries.constantCoeff p)⁻¹) * κ) * p := by
      rw [map_mul, mul_assoc]
    _ = _ := by rw [hc]

/-- A genuine unit power contributes its entire multiplicity to the full
normalized logarithm, without an earlier-coefficient independence premise. -/
theorem normalized_log_pow_complete {F : Type*} [Field F] [Algebra ℚ F]
    (p : PowerSeries F) (hp : PowerSeries.constantCoeff p ≠ 0) (k : ℕ) :
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (p ^ k))⁻¹ * p ^ k) =
      k • PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p) := by
  induction k with
  | zero =>
    simp only [pow_zero, map_one, inv_one, one_mul, zero_nsmul]
    rw [PowerSeries.logOf_eq, sub_self]
    exact PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log
  | succ k ih =>
    rw [pow_succ, normalized_log_mul_complete _ p (by simpa using pow_ne_zero k hp) hp,
      ih, succ_nsmul]

/-- Exact balance of complete unit powers cancels every coefficient of the
weighted normalized logarithms, including their full first jets. -/
theorem normalized_log_balanced_powers {F : Type*} [Field F] [Algebra ℚ F]
    (E f T : PowerSeries F) (b a d : ℕ)
    (hE : PowerSeries.constantCoeff E ≠ 0)
    (hf : PowerSeries.constantCoeff f ≠ 0)
    (hT : PowerSeries.constantCoeff T ≠ 0) (hpower : E ^ b = f ^ a * T ^ d) :
    b • PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff E)⁻¹ * E) -
      a • PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f) -
      d • PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff T)⁻¹ * T) = 0 := by
  have h := congrArg (fun p : PowerSeries F =>
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)) hpower
  rw [normalized_log_pow_complete E hE b,
    normalized_log_mul_complete _ _ (by simpa using pow_ne_zero a hf)
      (by simpa using pow_ne_zero d hT),
    normalized_log_pow_complete f hf a, normalized_log_pow_complete T hT d] at h
  rw [h]
  abel

/-- The whole normalized logarithm of a genuine unit inverse is the negative
of its whole original logarithm, with every normal coefficient retained. -/
theorem normalized_log_inv_complete {F : Type*} [Field F] [Algebra ℚ F]
    (p : PowerSeries F) (hp : PowerSeries.constantCoeff p ≠ 0) :
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p⁻¹)⁻¹ * p⁻¹) =
      -PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p) := by
  have hi : PowerSeries.constantCoeff p⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]
    exact inv_ne_zero hp
  have h1 : PowerSeries.logOf (1 : PowerSeries F) = 0 := by
    rw [PowerSeries.logOf_eq, sub_self]
    exact PowerSeries.subst_zero_of_constantCoeff_zero PowerSeries.constantCoeff_log
  have h := normalized_log_mul_complete p p⁻¹ hp hi
  rw [PowerSeries.mul_inv_cancel p hp] at h
  simp only [map_one, inv_one, one_mul, h1] at h
  linear_combination -h

/-- Exact residue normalization identifies the complete logarithm of the whole
comparison ratio with the signed weighted normalized logarithms. This is a full
series identity, not only an identity of first jets. -/
theorem residue_matched_ratio_log {F : Type*} [Field F] [Algebra ℚ F]
    (E f T : PowerSeries F) (κ : F) (b a d : ℕ)
    (hE : PowerSeries.constantCoeff E ≠ 0)
    (hf : PowerSeries.constantCoeff f ≠ 0)
    (hT : PowerSeries.constantCoeff T ≠ 0)
    (hmatch : PowerSeries.constantCoeff E ^ b =
      κ * (PowerSeries.constantCoeff f ^ a * PowerSeries.constantCoeff T ^ d)) :
    PowerSeries.logOf (PowerSeries.C κ⁻¹ * (E ^ b * (f ^ a * T ^ d)⁻¹)) =
      b • PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff E)⁻¹ * E) -
      a • PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff f)⁻¹ * f) -
      d • PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff T)⁻¹ * T) := by
  have hden : PowerSeries.constantCoeff (f ^ a * T ^ d) ≠ 0 := by
    rw [map_mul, map_pow, map_pow]
    exact mul_ne_zero (pow_ne_zero a hf) (pow_ne_zero d hT)
  have hfpow : PowerSeries.constantCoeff (f ^ a) ≠ 0 := by simpa using pow_ne_zero a hf
  have hTpow : PowerSeries.constantCoeff (T ^ d) ≠ 0 := by simpa using pow_ne_zero d hT
  have hEpow : PowerSeries.constantCoeff (E ^ b) ≠ 0 := by simpa using pow_ne_zero b hE
  have hinv : PowerSeries.constantCoeff (f ^ a * T ^ d)⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]
    exact inv_ne_zero hden
  have hunit : PowerSeries.constantCoeff (E ^ b * (f ^ a * T ^ d)⁻¹) = κ := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_inv, map_mul, map_pow, map_pow,
      hmatch, mul_assoc,
      mul_inv_cancel₀ (mul_ne_zero (pow_ne_zero a hf) (pow_ne_zero d hT)), mul_one]
  rw [← hunit, normalized_log_mul_complete _ _ hEpow hinv,
    normalized_log_pow_complete E hE b, normalized_log_inv_complete _ hden,
    normalized_log_mul_complete _ _ hfpow hTpow,
    normalized_log_pow_complete f hf a, normalized_log_pow_complete T hT d]
  abel

end SkewCornerDescent.Matrix
