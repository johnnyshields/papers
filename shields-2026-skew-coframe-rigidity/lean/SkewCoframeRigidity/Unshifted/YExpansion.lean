/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.ClippedOperator
import Mathlib.Tactic.LinearCombination

/-!
# Expansion of the clipped operator in the top letter

Formalizes the algebraic core of `shields-2026-skew-coframe-rigidity.tex`,
«Unshifted opposite-end exclusion» (`sec:unshifted`, `ph:unshifted-exclusion`): the expansion in
`y = H_m`, `m = M - 1`, of the unshifted equation `𝒯_{G,C}(H^p)`.  With `G = G₀ + y a`,
`C = C₀ + y b` and `H = h + y z^m`, the operator is bilinear in the coframe pair, the powers of `H`
beyond the first order in `y` are killed by the literal truncation at `M`, and the explicit
`y z^m` term contributes only through the constant coefficients of the two coframes.  Sorry-free.
-/

namespace SkewCoframeRigidity.Unshifted

open PowerSeries Polynomial

variable {R : Type*} [CommRing R]

/-- Clipping a series by `X^m * ·` at cutoff `m + 1` keeps only the constant coefficient. -/
theorem trunc_succ_X_pow_mul (m : ℕ) (f : R⟦X⟧) :
    trunc (m + 1) (PowerSeries.X ^ m * f) = Polynomial.C (constantCoeff f) * Polynomial.X ^ m := by
  ext n
  rw [coeff_trunc, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : n < m + 1
  · rw [if_pos h, PowerSeries.coeff_X_pow_mul']
    by_cases hn : n = m
    · subst hn; simp
    · have : ¬ m ≤ n := by omega
      simp [hn, this]
  · have : ¬ n = m := by omega
    simp [h, this]

/-- Truncation of a scalar multiple of a product with a polynomial. -/
theorem trunc_mul_C_poly (M : ℕ) (y : R) (u : R⟦X⟧) (b : R[X]) :
    trunc M (u * ((Polynomial.C y * b : R[X]) : R⟦X⟧)) =
      Polynomial.C y * trunc M (u * (b : R⟦X⟧)) := by
  rw [Polynomial.coe_mul, Polynomial.coe_C, mul_left_comm, trunc_C_mul]

/-- Bilinear expansion of the clipped operator in the scalar `y` carried by the coframes
`G = G₀ + y a`, `C = C₀ + y b`. -/
theorem clippedOp_expand (M : ℕ) (y : R) (G₀ C₀ a b : R[X]) (u : R⟦X⟧) :
    clippedOp M (G₀ + Polynomial.C y * a) (C₀ + Polynomial.C y * b) u =
      clippedOp M G₀ C₀ u + Polynomial.C y * (clippedOp M a C₀ u + clippedOp M G₀ b u) +
        Polynomial.C y ^ 2 * clippedOp M a b u := by
  unfold clippedOp
  simp only [Polynomial.coe_add, mul_add, map_add, trunc_mul_C_poly]
  ring

/-- `𝒯` is additive in the series. -/
theorem clippedOp_add_right (M : ℕ) (G C : R[X]) (u v : R⟦X⟧) :
    clippedOp M G C (u + v) = clippedOp M G C u + clippedOp M G C v := by
  unfold clippedOp
  rw [add_mul, add_mul, map_add, map_add]; ring

/-- Multiplying the series by `X^m` and clipping at `M = m + 1` keeps only the constant
coefficients of the two coframes: `𝒯_{A,B}(u z^m) = u₀ z^m (B₀ A - A₀ B)`. -/
theorem clippedOp_X_pow_mul (m : ℕ) (A B : R[X]) (u : R⟦X⟧) :
    clippedOp (m + 1) A B (u * PowerSeries.X ^ m) =
      Polynomial.C (constantCoeff u) * Polynomial.X ^ m *
        (Polynomial.C (B.coeff 0) * A - Polynomial.C (A.coeff 0) * B) := by
  unfold clippedOp
  have h : ∀ F : R[X], trunc (m + 1) (u * PowerSeries.X ^ m * (F : R⟦X⟧)) =
      Polynomial.C (constantCoeff u * F.coeff 0) * Polynomial.X ^ m := by
    intro F
    have : u * PowerSeries.X ^ m * ((F : R[X]) : R⟦X⟧) =
        PowerSeries.X ^ m * (u * ((F : R[X]) : R⟦X⟧)) := by ring
    rw [this, trunc_succ_X_pow_mul]
    simp [Polynomial.coeff_zero_eq_eval_zero, map_mul]
  rw [h, h]
  simp only [Polynomial.C_mul]
  ring

/-- Terms of `u` beyond the second order in `z^m` are killed by the literal truncation at
`M = m + 1` whenever `2 m ≥ M`. -/
theorem clippedOp_X_pow_two_mul (m : ℕ) (hm : 1 ≤ m) (A B : R[X]) (w : R⟦X⟧) :
    clippedOp (m + 1) A B (PowerSeries.X ^ (2 * m) * w) = 0 := by
  unfold clippedOp
  have h : ∀ F : R⟦X⟧, trunc (m + 1) (PowerSeries.X ^ (2 * m) * w * F) = 0 := by
    intro F
    have : PowerSeries.X ^ (2 * m) * w * F =
        PowerSeries.X ^ (m + 1) * (PowerSeries.X ^ (m - 1) * (w * F)) := by
      rw [show 2 * m = (m + 1) + (m - 1) by omega, pow_add]; ring
    rw [this, trunc_X_pow_self_mul]
  simp only [h, mul_zero, sub_zero]

/-- Binomial expansion of `(h + t)^p` to first order in `t`. -/
theorem pow_add_expand (h t : R⟦X⟧) (p : ℕ) :
    ∃ w : R⟦X⟧, (h + t) ^ (p + 2) = h ^ (p + 2) + (p + 2 : R⟦X⟧) * t * h ^ (p + 1) + t ^ 2 * w := by
  induction p with
  | zero => exact ⟨1, by push_cast; ring⟩
  | succ p ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨h * w + (p + 2 : R⟦X⟧) * h ^ (p + 1) + t * w, ?_⟩
    push_cast
    linear_combination (h + t) * hw

/-- `𝒯` is homogeneous in the series. -/
theorem clippedOp_C_mul (M : ℕ) (G C : R[X]) (c : R) (u : R⟦X⟧) :
    clippedOp M G C (PowerSeries.C c * u) = Polynomial.C c * clippedOp M G C u := by
  unfold clippedOp
  simp only [mul_assoc, trunc_C_mul]
  ring

/-- The unshifted operator on `H^p`, `H = h + y z^m`, `M = m + 1`, `m ≥ 1`, `p = q + 2`: to
first order in `y` it is `𝒯(h^p) + p y ϑ^{p-1} z^m (C₀ G - G₀ C)`, where `ϑ = h₀`; the
literal truncation removes every higher order in `y`. -/
theorem clippedOp_power_expand (m q : ℕ) (hm : 1 ≤ m) (A B : R[X]) (h : R⟦X⟧) (y : R) :
    clippedOp (m + 1) A B ((h + PowerSeries.C y * PowerSeries.X ^ m) ^ (q + 2)) =
      clippedOp (m + 1) A B (h ^ (q + 2)) +
        Polynomial.C (y * (q + 2 : R) * constantCoeff h ^ (q + 1)) * Polynomial.X ^ m *
          (Polynomial.C (B.coeff 0) * A - Polynomial.C (A.coeff 0) * B) := by
  obtain ⟨w, hw⟩ := pow_add_expand h (PowerSeries.C y * PowerSeries.X ^ m) q
  have e : (PowerSeries.C y * PowerSeries.X ^ m) ^ 2 * w =
      PowerSeries.X ^ (2 * m) * (PowerSeries.C (y ^ 2) * w) := by
    rw [mul_pow, ← map_pow, pow_mul]; ring
  have e2 : ((q + 2 : R⟦X⟧)) * (PowerSeries.C y * PowerSeries.X ^ m) * h ^ (q + 1) =
      PowerSeries.C (y * (q + 2 : R)) * (h ^ (q + 1) * PowerSeries.X ^ m) := by
    simp only [map_mul, map_add, map_natCast, map_ofNat]; ring
  rw [hw, e, e2, clippedOp_add_right, clippedOp_add_right, clippedOp_X_pow_two_mul m hm,
    clippedOp_C_mul, clippedOp_X_pow_mul]
  simp only [map_pow, add_zero, map_mul, map_add, map_natCast, map_ofNat]
  ring

/-- For two polynomials with constant term one, `𝒯_{A,B}(u z^m) = u₀ z^m (A - B)`: the identity
`𝒯_{W₀}(z^m) = z^m Δ` of the expansion. -/
theorem clippedOp_X_pow_mul_of_const_one (m : ℕ) (A B : R[X]) (hA : A.coeff 0 = 1)
    (hB : B.coeff 0 = 1) (u : R⟦X⟧) :
    clippedOp (m + 1) A B (u * PowerSeries.X ^ m) =
      Polynomial.C (constantCoeff u) * Polynomial.X ^ m * (A - B) := by
  rw [clippedOp_X_pow_mul, hA, hB]; simp

/-- If one coframe has zero constant term (an extreme-port vector) the operator keeps only
the other: `𝒯_{a,B}(u z^m) = u₀ z^m a` for `a₀ = 0`, `B₀ = 1`. -/
theorem clippedOp_X_pow_mul_of_zero_left (m : ℕ) (a B : R[X]) (ha : a.coeff 0 = 0)
    (hB : B.coeff 0 = 1) (u : R⟦X⟧) :
    clippedOp (m + 1) a B (u * PowerSeries.X ^ m) =
      Polynomial.C (constantCoeff u) * Polynomial.X ^ m * a := by
  rw [clippedOp_X_pow_mul, ha, hB]; simp

/-- Both vectors with zero constant term give `𝒯_{W₂}(z^m) = 0`. -/
theorem clippedOp_X_pow_mul_of_zero (m : ℕ) (a b : R[X]) (ha : a.coeff 0 = 0)
    (hb : b.coeff 0 = 0) (u : R⟦X⟧) :
    clippedOp (m + 1) a b (u * PowerSeries.X ^ m) = 0 := by
  rw [clippedOp_X_pow_mul, ha, hb]; simp

end SkewCoframeRigidity.Unshifted
