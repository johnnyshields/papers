/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.SquareWordCoordinate

/-!
# Full first normal comparison jet for the five-copy square word

Supports `shields-2026-skew-corner-descent.tex` (`rem:square-word`).
The first coefficient retains both complete denominator inverses. It is a
power-series identity, not a formula imposed on a surrogate coefficient.
Sorry-free.
-/

namespace SkewCornerDescent.SquareWordProfiles

/-- The full inverse first jet, including every actual first denominator coefficient. -/
private theorem coeff_one_inv {F : Type*} [Field F] (p : PowerSeries F) :
    PowerSeries.coeff 1 p⁻¹ =
      -PowerSeries.coeff 1 p / PowerSeries.constantCoeff p ^ 2 := by
  have ha : Finset.HasAntidiagonal.antidiagonal 1 = {(0,1),(1,0)} := rfl
  rw [PowerSeries.coeff_inv, ha]
  norm_num [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.constantCoeff_inv]
  ring

/-- The complete source/union/closure comparison at its first normal order. -/
theorem square_comparison_first_jet {F : Type*} [Field F]
    (u a q : PowerSeries F)
    (hu : PowerSeries.constantCoeff u ≠ 0) (hq : PowerSeries.constantCoeff q ≠ 0) :
    let u0 := PowerSeries.constantCoeff u
    let a0 := PowerSeries.constantCoeff a
    let q0 := PowerSeries.constantCoeff q
    let u1 := PowerSeries.coeff 1 u
    let a1 := PowerSeries.coeff 1 a
    let q1 := PowerSeries.coeff 1 q
    let x0 := q0 / u0 ^ 2
    PowerSeries.coeff 1
        (u ^ 2 * (a * u⁻¹ ^ 2) ^ 5 - (1 - q * u⁻¹ ^ 2) ^ 4 * (q * u⁻¹ ^ 2)⁻¹) =
      5 * a0 ^ 4 * a1 / u0 ^ 8 - 8 * a0 ^ 5 * u1 / u0 ^ 9 +
      (4 * (1 - x0) ^ 3 / x0 + (1 - x0) ^ 4 / x0 ^ 2) *
        (q1 / u0 ^ 2 - 2 * q0 * u1 / u0 ^ 3) := by
  dsimp only
  simp only [map_sub, PowerSeries.coeff_one_mul, PowerSeries.coeff_one_pow,
    map_mul, map_pow, PowerSeries.constantCoeff_inv, coeff_one_inv, map_one,
    PowerSeries.coeff_one]
  norm_num
  field_simp
  ring

/-- A surviving higher partial reads the full first normal jet. It annihilates
only the three stated residues, never their complete first coefficients. -/
theorem square_comparison_mixed_first_jet {F : Type*} [Field F]
    (D : F →+ F) (hMul : ∀ x y, D (x * y) = x * D y + y * D x)
    (u a q : PowerSeries F)
    (hu : PowerSeries.constantCoeff u ≠ 0) (hq : PowerSeries.constantCoeff q ≠ 0)
    (hDu : D (PowerSeries.constantCoeff u) = 0)
    (hDa : D (PowerSeries.constantCoeff a) = 0)
    (hDq : D (PowerSeries.constantCoeff q) = 0) :
    let u0 := PowerSeries.constantCoeff u
    let a0 := PowerSeries.constantCoeff a
    let q0 := PowerSeries.constantCoeff q
    let du1 := D (PowerSeries.coeff 1 u)
    let da1 := D (PowerSeries.coeff 1 a)
    let dq1 := D (PowerSeries.coeff 1 q)
    let x0 := q0 / u0 ^ 2
    D (PowerSeries.coeff 1
        (u ^ 2 * (a * u⁻¹ ^ 2) ^ 5 - (1 - q * u⁻¹ ^ 2) ^ 4 * (q * u⁻¹ ^ 2)⁻¹)) =
      5 * a0 ^ 4 * da1 / u0 ^ 8 - 8 * a0 ^ 5 * du1 / u0 ^ 9 +
      (4 * (1 - x0) ^ 3 / x0 + (1 - x0) ^ 4 / x0 ^ 2) *
        (dq1 / u0 ^ 2 - 2 * q0 * du1 / u0 ^ 3) := by
  have h1 : D (1 : F) = 0 := by
    have h := hMul 1 1
    simp only [one_mul, mul_one] at h
    linear_combination -h
  let δ : Derivation ℤ F F :=
    { toFun := D
      map_add' := D.map_add
      map_smul' n x := D.map_zsmul n x
      map_one_eq_zero' := h1
      leibniz' x y := by
        change D (x * y) = x * D y + y * D x
        exact hMul x y }
  have he : (δ : F → F) = (D : F → F) := rfl
  have hδu : δ (PowerSeries.constantCoeff u) = 0 := hDu
  have hδa : δ (PowerSeries.constantCoeff a) = 0 := hDa
  have hδq : δ (PowerSeries.constantCoeff q) = 0 := hDq
  dsimp only
  rw [square_comparison_first_jet u a q hu hq, ← he]
  have h2 : δ (2 : F) = 0 := δ.map_natCast 2
  have h4 : δ (4 : F) = 0 := δ.map_natCast 4
  have h5 : δ (5 : F) = 0 := δ.map_natCast 5
  have h8 : δ (8 : F) = 0 := δ.map_natCast 8
  simp [Derivation.leibniz, Derivation.leibniz_div, smul_eq_mul,
    hδu, hδa, hδq, h2, h4, h5, h8]
  field_simp

end SkewCornerDescent.SquareWordProfiles
