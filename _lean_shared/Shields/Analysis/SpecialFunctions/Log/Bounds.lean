/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.MeanInequalitiesPow

/-!
# Three bounds on the logarithm

Mathlib carries `Real.log x ≤ x - 1` and its reciprocal form `1 - x⁻¹ ≤ Real.log x`.  Three
consequences used repeatedly in envelope estimates are collected here.

## Main results

* `Shields.log_le_div_exp_one` — `log x ≤ x / e`, the tangent bound at `x = e`, and
  `Shields.mul_log_div_le_div_exp_one` — `x * log (y / x) ≤ y / e`, which is the same
  statement homogenized.  This is the sharp form of "a logarithm is beaten by a linear
  function", and the constant `1 / e` is attained.
* `Shields.two_mul_sub_div_add_le_log` — `2 (x - 1) / (x + 1) ≤ log x` for `x ≥ 1`, the
  Padé lower bound, which is Mathlib's `Real.le_log_one_add_of_nonneg` written at base
  point `1` rather than `0`, and `Shields.two_mul_sub_div_add_le_log_sub`, its two-argument
  form `2 (a - b) / (a + b) ≤ log a - log b`.  The weaker `1 - x⁻¹ ≤ log x` loses a factor
  of two at `x` near one and is not enough for a ratio of two nearby quantities.
* `Shields.mul_log_one_add_div_mono` — `k ↦ k * log (1 + v / k)` is monotone, which is
  `(1 + v / k) ^ k` increasing in `k` in logarithmic form, proved from Bernoulli's
  inequality rather than by differentiating.

## Papers depending on this file

* `growing-rank-edrei` — the hole and particle envelopes of `lem:trace-norm`.
-/

namespace Shields

open Real Set

/-- `log x ≤ x / e`: the logarithm lies below its tangent at `x = e`. -/
theorem log_le_div_exp_one {x : ℝ} (hx : 0 < x) : Real.log x ≤ x / Real.exp 1 := by
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h := Real.log_le_sub_one_of_pos (x := x / Real.exp 1) (div_pos hx he)
  rw [Real.log_div (ne_of_gt hx) (ne_of_gt he), Real.log_exp] at h
  linarith

/-- `x log (y / x) ≤ y / e`, the homogeneous form of `log_le_div_exp_one`. -/
theorem mul_log_div_le_div_exp_one {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    x * Real.log (y / x) ≤ y / Real.exp 1 := by
  have h := log_le_div_exp_one (x := y / x) (div_pos hy hx)
  have := mul_le_mul_of_nonneg_left h (le_of_lt hx)
  calc x * Real.log (y / x) ≤ x * (y / x / Real.exp 1) := this
    _ = y / Real.exp 1 := by field_simp

/-- **The Padé lower bound** `2 (x - 1) / (x + 1) ≤ log x` for `x ≥ 1`. -/
theorem two_mul_sub_div_add_le_log {x : ℝ} (hx : 1 ≤ x) :
    2 * (x - 1) / (x + 1) ≤ Real.log x := by
  have h := Real.le_log_one_add_of_nonneg (x := x - 1) (by linarith)
  rwa [show x - 1 + 2 = x + 1 by ring, show (1 : ℝ) + (x - 1) = x by ring] at h

/-- The two-argument form: for `0 < b ≤ a`, `2 (a - b) / (a + b) ≤ log a - log b`. -/
theorem two_mul_sub_div_add_le_log_sub {a b : ℝ} (hb : 0 < b) (hab : b ≤ a) :
    2 * (a - b) / (a + b) ≤ Real.log a - Real.log b := by
  have ha : 0 < a := lt_of_lt_of_le hb hab
  have h1 : (1 : ℝ) ≤ a / b := (one_le_div hb).mpr hab
  have h := two_mul_sub_div_add_le_log h1
  rw [Real.log_div (ne_of_gt ha) (ne_of_gt hb)] at h
  have hb' : b ≠ 0 := ne_of_gt hb
  have hab0 : a + b ≠ 0 := by positivity
  have hq : a / b + 1 ≠ 0 := by
    have : 0 < a / b + 1 := by positivity
    exact ne_of_gt this
  refine le_trans (le_of_eq ?_) h
  field_simp

/-- **`k ↦ k log (1 + v / k)` is monotone.**  Equivalently `(1 + v / k) ^ k` increases with
`k`, by Bernoulli's inequality applied to the exponent ratio. -/
theorem mul_log_one_add_div_mono {v K k : ℝ} (hv : 0 ≤ v) (hK : 0 < K) (hk : K ≤ k) :
    K * Real.log (1 + v / K) ≤ k * Real.log (1 + v / k) := by
  have hk0 : 0 < k := lt_of_lt_of_le hK hk
  have hr : 1 ≤ k / K := (one_le_div hK).mpr hk
  have hs : (-1 : ℝ) ≤ v / k := le_trans (by norm_num) (div_nonneg hv (le_of_lt hk0))
  have hb := one_add_mul_self_le_rpow_one_add hs hr
  -- `1 + (k / K) * (v / k) ≤ (1 + v / k) ^ (k / K)`
  have hkK : (k / K) * (v / k) = v / K := by field_simp
  rw [hkK] at hb
  have hpos : (0 : ℝ) < 1 + v / k := by
    have : (0 : ℝ) ≤ v / k := div_nonneg hv (le_of_lt hk0)
    linarith
  have hlog := Real.log_le_log (by positivity) hb
  rw [Real.log_rpow hpos] at hlog
  have := mul_le_mul_of_nonneg_left hlog (le_of_lt hK)
  calc K * Real.log (1 + v / K) ≤ K * ((k / K) * Real.log (1 + v / k)) := this
    _ = k * Real.log (1 + v / k) := by field_simp


/-! ### Axiom footprint -/

/-- info: 'Shields.mul_log_div_le_div_exp_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mul_log_div_le_div_exp_one

/-- info: 'Shields.two_mul_sub_div_add_le_log_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms two_mul_sub_div_add_le_log_sub

/-- info: 'Shields.mul_log_one_add_div_mono' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms mul_log_one_add_div_mono

end Shields
