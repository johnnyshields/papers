/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import TuranBessel.Degree

/-!
# Negative-order failure of coefficientwise positivity

Formalizes the algebraic part of `shields-2026-turan-bessel.tex`, Appendix B
«Beyond the positive-series domain» (`app:continuation`,
`prop:negative-coeff-failure`, via `lem:coefficient-continuation`): the degree-two
coefficient of `Δ` continues meromorphically to `-2 < a < -1` and is **negative**
there, so the sharp coefficientwise theorem cannot extend past the positive-series
domain.

The trigamma series `∑(a+n)⁻²` continues to negative non-integer `a`
(`trigamma_summable_shift`, `trigamma_succ_of_summable`), the `Q_*` identity
`Δ_2 = Q_*/(a⁶(a+1)³ψ₁(a))` (`Dcoeff_two_eq`) holds there, and for `-2<a<-1`:
`Q_* > 0` (paper's `b`-substitution polynomial estimate) while the denominator is
negative, so `Δ_2 < 0`.

The `log|I_ν|` convention of `sec:context`, the small-`z` expansion `eq:small-z-D`,
and the accompanying statement that the leading small-`z` term keeps its positive sign
away from the poles all need the modified Bessel functions absent from Mathlib, and
are out of scope.

Sorry-free.
-/

namespace TuranBessel

variable {a : ℝ}

/-- On `-2 < a < -1`, `ψ₁(a+1) > 0` (`a+1 ∈ (-1,0)`). -/
theorem trigamma_succ_pos_neg (ha2 : -2 < a) (ha3 : a < -1) : 0 < trigamma (a + 1) := by
  have hsum1 : Summable (fun n : ℕ => (a + 1 + (n : ℝ))⁻¹ ^ 2) :=
    trigamma_summable_shift (k := 1) (by push_cast; linarith)
  have hrec := trigamma_succ_of_summable hsum1
  rw [show a + 1 + 1 = a + 2 from by ring] at hrec
  have hnn : 0 ≤ trigamma (a + 2) := by
    rw [trigamma]; exact tsum_nonneg (fun n => by positivity)
  have hp : 0 < ((a + 1)⁻¹) ^ 2 := by
    have : (a + 1)⁻¹ ≠ 0 := inv_ne_zero (by linarith)
    positivity
  linarith

/-- Continuation of the recurrences to `-2 < a < -1`. -/
theorem trigamma_recurrences_neg (ha2 : -2 < a) (ha3 : a < -1) :
    trigamma (a + 1) = trigamma a - (a ^ 2)⁻¹ ∧
    trigamma (a + 2) = trigamma a - (a ^ 2)⁻¹ - ((a + 1) ^ 2)⁻¹ := by
  have hsa : Summable (fun n : ℕ => (a + (n : ℝ))⁻¹ ^ 2) :=
    trigamma_summable_shift (k := 2) (by push_cast; linarith)
  have hsa1 : Summable (fun n : ℕ => (a + 1 + (n : ℝ))⁻¹ ^ 2) :=
    trigamma_summable_shift (k := 1) (by push_cast; linarith)
  have h1 := trigamma_succ_of_summable hsa
  rw [inv_pow] at h1
  have h2 := trigamma_succ_of_summable hsa1
  rw [show a + 1 + 1 = a + 2 from by ring, inv_pow] at h2
  exact ⟨by linarith, by linarith⟩

/-- `ψ₁(a) > 0` on `-2 < a < -1`. -/
theorem trigamma_pos_neg (ha2 : -2 < a) (ha3 : a < -1) : 0 < trigamma a := by
  have hsa : Summable (fun n : ℕ => (a + (n : ℝ))⁻¹ ^ 2) :=
    trigamma_summable_shift (k := 2) (by push_cast; linarith)
  have hrec := trigamma_succ_of_summable hsa
  have hp : 0 < (a⁻¹) ^ 2 := by
    have : a⁻¹ ≠ 0 := inv_ne_zero (by linarith)
    positivity
  rw [hrec]; linarith [trigamma_succ_pos_neg ha2 ha3]

/-- `Q_* > 0` on `-2 < a < -1` (paper's `b = -a` estimate): the first term is
`≥ 0`, and the `R`-term dominates the constant because `R(a+1) < -1`. -/
theorem Qstar2_pos_of_neg (ha2 : -2 < a) (ha3 : a < -1) : 0 < Qstar2 a := by
  obtain ⟨ht1, _⟩ := trigamma_recurrences_neg ha2 ha3
  have hga1 := trigamma_succ_pos_neg ha2 ha3
  have ha1neg : a + 1 < 0 := by linarith
  have hRval : Rval a = trigamma (a + 1) - (a + 1)⁻¹ := by unfold Rval; rw [ht1]
  have hRb : Rval a * (a + 1) < -1 := by
    rw [hRval, sub_mul, inv_mul_cancel₀ (by linarith : a + 1 ≠ 0)]
    nlinarith [mul_neg_of_pos_of_neg hga1 ha1neg]
  have hs : (0 : ℝ) < -1 - a := by linarith
  have hpoly : 0 < -8 * a ^ 3 - 3 * a ^ 2 + 4 * a + 3 := by
    nlinarith [hs, mul_pos hs hs, mul_pos (mul_pos hs hs) hs]
  have h2a1 : (0 : ℝ) < 2 * a * (a + 1) := by nlinarith
  have hane : a ≠ 0 := (show a < 0 by linarith).ne
  have hcoeffneg : 2 * a ^ 2 * (a + 1) * (8 * a ^ 2 + 3 * a + 1) < 0 := by
    have h8 : 0 < 8 * a ^ 2 + 3 * a + 1 := by nlinarith [sq_nonneg a]
    have hc : 0 < a ^ 2 * (-(a + 1)) * (8 * a ^ 2 + 3 * a + 1) :=
      mul_pos (mul_pos (by positivity) (by linarith)) h8
    nlinarith [hc]
  have hfirst : 0 ≤ 2 * a ^ 4 * (a + 1) ^ 2 * (Rval a) ^ 2 := by positivity
  have hbracket : 0 < 2 * a ^ 2 * (a + 1) ^ 2 * (8 * a ^ 2 + 3 * a + 1) * (Rval a)
      + 2 * a * (a + 1) * (5 * a + 3) := by
    nlinarith [mul_pos h2a1 hpoly,
      mul_pos_of_neg_of_neg hcoeffneg (show Rval a * (a + 1) + 1 < 0 by linarith)]
  unfold Qstar2
  linarith

/-- **`prop:negative-coeff-failure`.**  For `-2 < a < -1` (equivalently
`-3 < ν < -2`), the degree-two coefficient is negative: `Δ_2(a) < 0`, so the sharp
coefficientwise theorem does not extend beyond `a > 0`. -/
theorem Dcoeff_two_neg (ha2 : -2 < a) (ha3 : a < -1) : Dcoeff a 2 < 0 := by
  obtain ⟨ht1, ht2⟩ := trigamma_recurrences_neg ha2 ha3
  have hga : 0 < trigamma a := trigamma_pos_neg ha2 ha3
  have hane : a ≠ 0 := (show a < 0 by linarith).ne
  have ha1ne : a + 1 ≠ 0 := (show a + 1 < 0 by linarith).ne
  have h2a1ne : (2 * a + 1) ≠ 0 := (show 2 * a + 1 < 0 by linarith).ne
  rw [Dcoeff_two_eq hane ha1ne h2a1ne hga.ne' ht1 ht2]
  have h6 : 0 < a ^ 6 := by positivity
  have h3 : (a + 1) ^ 3 < 0 := Odd.pow_neg (by norm_num) (by linarith)
  have hden : a ^ 6 * (a + 1) ^ 3 * trigamma a < 0 :=
    mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h6 h3) hga
  exact div_neg_of_pos_of_neg (Qstar2_pos_of_neg ha2 ha3) hden

end TuranBessel
