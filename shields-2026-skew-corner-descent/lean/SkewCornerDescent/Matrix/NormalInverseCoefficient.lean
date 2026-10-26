/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalLogCoefficient

/-!
# First fresh coefficients of full inverse normal series

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The inverse is never replaced by its constant. Its earlier generator independence and
first derivative follow from the full product identity. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F] [CharZero F] [Module ℚ F]

/-- Every earlier coefficient of the full inverse remains independent of a fresh generator. -/
theorem coeff_deriv_inv_zero (D : Derivation ℚ F F) (p : PowerSeries F) (n : ℕ)
    (hunit : PowerSeries.constantCoeff p ≠ 0)
    (hp : ∀ k, k ≤ n → D (PowerSeries.coeff k p) = 0) :
    D (PowerSeries.coeff n p⁻¹) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have he := coeff_deriv_mul_first D p p⁻¹ n
      (fun k hk => hp k hk.le)
      (fun k hk => ih k hk (fun l hl => hp l (hl.trans hk.le)))
    rw [PowerSeries.mul_inv_cancel p hunit, PowerSeries.coeff_one] at he
    have hz : D (if n = 0 then (1 : F) else 0) = 0 := by
      split_ifs <;> simp
    rw [hz, hp n le_rfl, smul_zero, add_zero, smul_eq_mul] at he
    exact (mul_eq_zero.mp he.symm).resolve_left hunit

/-- At the first fresh order, differentiating the complete inverse gives the exact inverse
square of the constant times the source derivative, with the negative sign. -/
theorem coeff_deriv_inv_first (D : Derivation ℚ F F) (p : PowerSeries F) (n : ℕ)
    (hn : 0 < n) (hunit : PowerSeries.constantCoeff p ≠ 0)
    (hp : ∀ k, k < n → D (PowerSeries.coeff k p) = 0) :
    D (PowerSeries.coeff n p⁻¹) =
      -(PowerSeries.constantCoeff p)⁻¹ ^ 2 * D (PowerSeries.coeff n p) := by
  have he := coeff_deriv_mul_first D p p⁻¹ n hp
    (fun k hk => coeff_deriv_inv_zero D p k hunit (fun l hl => hp l (hl.trans_lt hk)))
  rw [PowerSeries.mul_inv_cancel p hunit, PowerSeries.coeff_one,
    ite_eq_right hn.ne', map_zero, PowerSeries.constantCoeff_inv, smul_eq_mul, smul_eq_mul] at he
  field_simp at he ⊢
  linear_combination -he

/-- The full quotient logarithm at its first fresh order is the difference of the two
normalized determinant derivatives, with source multiplicity two. -/
theorem coeff_deriv_normalized_quotient_log_first (D : Derivation ℚ F F)
    (p q : PowerSeries F) (n : ℕ) (hn : 0 < n)
    (hp0 : PowerSeries.constantCoeff p ≠ 0) (hq0 : PowerSeries.constantCoeff q ≠ 0)
    (hp : ∀ k, k < n → D (PowerSeries.coeff k p) = 0)
    (hq : ∀ k, k < n → D (PowerSeries.coeff k q) = 0) :
    let u := q * p⁻¹ ^ 2
    D (PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff u)⁻¹ * u))) =
      (PowerSeries.constantCoeff q)⁻¹ * D (PowerSeries.coeff n q) -
        2 * (PowerSeries.constantCoeff p)⁻¹ * D (PowerSeries.coeff n p) := by
  have hi : ∀ k, k < n → D (PowerSeries.coeff k p⁻¹) = 0 :=
    fun k hk => coeff_deriv_inv_zero D p k hp0 (fun l hl => hp l (hl.trans_lt hk))
  have hi2 : ∀ k, k < n → D (PowerSeries.coeff k (p⁻¹ ^ 2)) = 0 :=
    fun k hk => coeff_deriv_pow_zero D p⁻¹ k (fun l hl => hi l (hl.trans_lt hk)) 2
  have hu : ∀ k, k < n → D (PowerSeries.coeff k (q * p⁻¹ ^ 2)) = 0 :=
    fun k hk => coeff_deriv_mul_zero D q (p⁻¹ ^ 2) k
      (fun l hl => hq l (hl.trans_lt hk)) (fun l hl => hi2 l (hl.trans_lt hk))
  have hu0 : PowerSeries.constantCoeff (q * p⁻¹ ^ 2) ≠ 0 := by
    rw [map_mul, map_pow, PowerSeries.constantCoeff_inv]
    exact mul_ne_zero hq0 (pow_ne_zero 2 (inv_ne_zero hp0))
  have hs := coeff_deriv_mul_first D p⁻¹ p⁻¹ n hi hi
  rw [← pow_two, PowerSeries.constantCoeff_inv,
    coeff_deriv_inv_first D p n hn hp0 hp, smul_eq_mul] at hs
  dsimp only
  rw [coeff_deriv_normalized_log_first D _ n hn hu0 hu,
    coeff_deriv_mul_first D q (p⁻¹ ^ 2) n hq hi2, hs,
    map_mul, map_pow, PowerSeries.constantCoeff_inv, smul_eq_mul]
  simp only [mul_inv_rev, inv_pow, inv_inv]
  generalize PowerSeries.constantCoeff p = a at *
  generalize PowerSeries.constantCoeff q = b at *
  field_simp [hp0, hq0]
  calc
    _ = -((a * a⁻¹) ^ 3 * D (PowerSeries.coeff n p) * b * 2) +
        a * (a * a⁻¹) ^ 2 * D (PowerSeries.coeff n q) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hp0]; ring

end SkewCornerDescent.Matrix
