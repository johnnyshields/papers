/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalLogCoefficient

/-!
# Fresh coefficients of an original virtual difference

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
The original two summands are differentiated before unit normalization and
logging. A residue cancellation changes the denominator, not the original
normal coefficients. Earlier intrinsic coefficients need not vanish.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F : Type*} [Field F] [CharZero F] [Module ℚ F]

/-- The first generator-dependent logarithmic coefficient of an original difference
is the residue-weighted difference of the two original logarithmic coefficients.
Only their generator derivatives at earlier orders vanish. -/
theorem coeff_deriv_normalized_difference_first (D : Derivation ℚ F F)
    (p q : PowerSeries F) (α : F) (hα : D α = 0) (n : ℕ) (hn : 0 < n)
    (hp0 : PowerSeries.constantCoeff p ≠ 0) (hq0 : PowerSeries.constantCoeff q ≠ 0)
    (ht0 : PowerSeries.constantCoeff p - α * PowerSeries.constantCoeff q ≠ 0)
    (hp : ∀ k, k < n → D (PowerSeries.coeff k p) = 0)
    (hq : ∀ k, k < n → D (PowerSeries.coeff k q) = 0) :
    D (PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff
        (p - PowerSeries.C α * q))⁻¹ * (p - PowerSeries.C α * q)))) =
      (PowerSeries.constantCoeff p * D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) -
        α * PowerSeries.constantCoeff q * D (PowerSeries.coeff n
          (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff q)⁻¹ * q)))) /
        (PowerSeries.constantCoeff p - α * PowerSeries.constantCoeff q) := by
  have htprev (k : ℕ) (hk : k < n) :
      D (PowerSeries.coeff k (p - PowerSeries.C α * q)) = 0 := by
    rw [map_sub, PowerSeries.coeff_C_mul, map_sub, Derivation.leibniz,
      hp k hk, hq k hk, hα, smul_zero, smul_zero, add_zero, sub_zero]
  have htunit : PowerSeries.constantCoeff (p - PowerSeries.C α * q) ≠ 0 := by
    simpa only [map_sub, map_mul, PowerSeries.constantCoeff_C] using ht0
  rw [coeff_deriv_normalized_log_first D _ n hn htunit htprev,
    coeff_deriv_normalized_log_first D p n hn hp0 hp,
    coeff_deriv_normalized_log_first D q n hn hq0 hq]
  simp only [map_sub, map_mul, PowerSeries.constantCoeff_C,
    PowerSeries.coeff_C_mul, Derivation.leibniz, hα, smul_eq_mul, mul_zero, add_zero]
  field_simp

/-- The original virtual closure `β - α f²` has its exact fresh logarithmic coefficient.
Only its own residue must be a unit; neither original summand is normalized away. -/
theorem coeff_deriv_virtual_closure_first (D : Derivation ℚ F F)
    (β f : PowerSeries F) (α : F) (hα : D α = 0) (n : ℕ) (hn : 0 < n)
    (ht0 : PowerSeries.constantCoeff β - α * PowerSeries.constantCoeff f ^ 2 ≠ 0)
    (hβ : ∀ k, k < n → D (PowerSeries.coeff k β) = 0)
    (hf : ∀ k, k < n → D (PowerSeries.coeff k f) = 0) :
    D (PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff
        (β - PowerSeries.C α * f ^ 2))⁻¹ * (β - PowerSeries.C α * f ^ 2)))) =
      (D (PowerSeries.coeff n β) -
        2 * α * PowerSeries.constantCoeff f * D (PowerSeries.coeff n f)) /
        (PowerSeries.constantCoeff β - α * PowerSeries.constantCoeff f ^ 2) := by
  have hsquare (k : ℕ) (hk : k < n) : D (PowerSeries.coeff k (f ^ 2)) = 0 :=
    coeff_deriv_pow_zero D f k (fun l hl => hf l (hl.trans_lt hk)) 2
  have htprev (k : ℕ) (hk : k < n) :
      D (PowerSeries.coeff k (β - PowerSeries.C α * f ^ 2)) = 0 := by
    rw [map_sub, PowerSeries.coeff_C_mul, map_sub, Derivation.leibniz,
      hβ k hk, hsquare k hk, hα, smul_zero, smul_zero, add_zero, sub_zero]
  have htunit : PowerSeries.constantCoeff (β - PowerSeries.C α * f ^ 2) ≠ 0 := by
    simpa only [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_C] using ht0
  rw [coeff_deriv_normalized_log_first D _ n hn htunit htprev]
  simp only [map_sub, map_mul, map_pow, PowerSeries.constantCoeff_C,
    PowerSeries.coeff_C_mul, Derivation.leibniz, hα, smul_eq_mul, mul_zero, add_zero]
  rw [pow_two f, coeff_deriv_mul_first D f f n hf hf]
  simp only [smul_eq_mul, div_eq_mul_inv]
  ring

end SkewCornerDescent.Matrix
