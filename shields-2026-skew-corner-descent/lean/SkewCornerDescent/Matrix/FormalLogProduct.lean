/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import Vendor.AlgebraicCombinatorics.FPS.NonIntegerPowers
import Mathlib.RingTheory.PowerSeries.Log

/-!
# The complete native formal logarithm product law

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The held formal logarithm is identified coefficientwise with Mathlib's logOf.
Its complete product law therefore retains all normal jets. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

/-- The held and native logarithm series use equivalent sign conventions. -/
theorem held_log_series_eq_native {F : Type*} [CommRing F] [Algebra ℚ F] :
    AlgebraicCombinatorics.FPS.logSeries (K := F) = PowerSeries.log F := by
  ext n
  rw [AlgebraicCombinatorics.FPS.coeff_logSeries, PowerSeries.coeff_log]
  by_cases hn : n = 0
  · simp only [hn, ite_true]
  · rw [ite_eq_right hn, ite_eq_right hn]
    have he : n + 1 = (n - 1) + 2 := by omega
    rw [he, pow_add]
    norm_num

/-- The held full logarithm and native logOf are the same object, not merely morally equal. -/
theorem held_log_eq_native {F : Type*} [CommRing F] [Algebra ℚ F]
    (p : PowerSeries F) :
    AlgebraicCombinatorics.FPS.fpsLog p = PowerSeries.logOf p := by
  rw [AlgebraicCombinatorics.FPS.fpsLog, PowerSeries.logOf, held_log_series_eq_native]

/-- Complete normalized logarithms are additive, with no fresh-jet independence premise. -/
theorem logOf_mul_complete {F : Type*} [CommRing F] [Algebra ℚ F]
    (p q : PowerSeries F)
    (hp : PowerSeries.constantCoeff p = 1) (hq : PowerSeries.constantCoeff q = 1) :
    PowerSeries.logOf (p * q) = PowerSeries.logOf p + PowerSeries.logOf q := by
  rw [← held_log_eq_native, ← held_log_eq_native, ← held_log_eq_native]
  exact AlgebraicCombinatorics.FPS.fpsLog_mul hp hq

/-- Equality of complete normalized jets gives equality of every corresponding log jet. -/
theorem logOf_coeff_congr {F : Type*} [CommRing F] [Algebra ℚ F]
    (p q : PowerSeries F) (hp : PowerSeries.constantCoeff p = 1)
    (hq : PowerSeries.constantCoeff q = 1) (n : ℕ)
    (hjet : ∀ k ≤ n, PowerSeries.coeff k p = PowerSeries.coeff k q) :
    ∀ k ≤ n, PowerSeries.coeff k (PowerSeries.logOf p) =
      PowerSeries.coeff k (PowerSeries.logOf q) := by
  have hzP : PowerSeries.constantCoeff (p - 1) = 0 := by simp [hp]
  have hzQ : PowerSeries.constantCoeff (q - 1) = 0 := by simp [hq]
  have hsub : PowerSeries.XnEquiv n (p - 1) (q - 1) := by
    intro k hk
    simp only [map_sub, hjet k hk]
  exact PowerSeries.xnEquiv_subst
    (fun k hk => rfl) hsub hzP hzQ

/-- Complete unit logarithms are additive after their actual constant normalization. -/
theorem normalized_log_mul_complete {F : Type*} [Field F] [Algebra ℚ F]
    (p q : PowerSeries F)
    (hp : PowerSeries.constantCoeff p ≠ 0) (hq : PowerSeries.constantCoeff q ≠ 0) :
    PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (p * q))⁻¹ * (p * q)) =
      PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p) +
        PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff q)⁻¹ * q) := by
  have hP : PowerSeries.constantCoeff (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p) = 1 :=
    by simp [hp]
  have hQ : PowerSeries.constantCoeff (PowerSeries.C (PowerSeries.constantCoeff q)⁻¹ * q) = 1 :=
    by simp [hq]
  have he :
      (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p) *
        (PowerSeries.C (PowerSeries.constantCoeff q)⁻¹ * q) =
      PowerSeries.C (PowerSeries.constantCoeff (p * q))⁻¹ * (p * q) := by
    rw [map_mul, mul_inv_rev, map_mul]
    ring
  rw [← he]
  exact logOf_mul_complete _ _ hP hQ

/-- Normalization and logging preserve all equal unit jets, including the constant jet. -/
theorem normalized_log_coeff_congr {F : Type*} [Field F] [Algebra ℚ F]
    (p q : PowerSeries F)
    (hp : PowerSeries.constantCoeff p ≠ 0) (hq : PowerSeries.constantCoeff q ≠ 0)
    (n : ℕ) (hjet : ∀ k ≤ n, PowerSeries.coeff k p = PowerSeries.coeff k q) :
    ∀ k ≤ n,
      PowerSeries.coeff k
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)) =
      PowerSeries.coeff k
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff q)⁻¹ * q)) := by
  have h0 : PowerSeries.constantCoeff p = PowerSeries.constantCoeff q := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff] using hjet 0 (Nat.zero_le n)
  apply logOf_coeff_congr _ _ (by simp [hp]) (by simp [hq]) n
  intro k hk
  simp only [PowerSeries.coeff_C_mul, h0, hjet k hk]

end SkewCornerDescent.Matrix
