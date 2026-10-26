/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.TranscendentalRationalFunctions
import SkewCornerDescent.Matrix.SignedNormalProducts

/-!
# Full rational series representation from a transcendental residue

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`,
`eq:original-defect`). Polynomial cross identities transport the actual rational
function to its complete signed normal-series expression. Both denominator units
are produced from the transcendental residue, not assumed. Sorry-free.
-/

namespace SkewCornerDescent

open scoped BigOperators

noncomputable def signedRationalNumerator (ε : ℤ) (s : Finset ℚ) (e : ℚ → ℤ) : Polynomial ℚ :=
  Polynomial.C (ε : ℚ) * ∏ α ∈ s, (Polynomial.X - Polynomial.C α) ^ (e α).toNat

noncomputable def signedRationalDenominator (s : Finset ℚ) (e : ℚ → ℤ) : Polynomial ℚ :=
  ∏ α ∈ s, (Polynomial.X - Polynomial.C α) ^ (-e α).toNat

theorem signedRationalDenominator_ne_zero (s : Finset ℚ) (e : ℚ → ℤ) :
    signedRationalDenominator s e ≠ 0 := by
  classical
  exact Finset.prod_ne_zero_iff.mpr (fun α _ =>
    pow_ne_zero _ (Polynomial.monic_X_sub_C α).ne_zero)

theorem signedRational_aeval {F : Type*} [Field F] [CharZero F] [Algebra ℚ F]
    (u : F) (ε : ℤ) (s : Finset ℚ) (e : ℚ → ℤ) :
    Polynomial.aeval u (signedRationalNumerator ε s e) /
      Polynomial.aeval u (signedRationalDenominator s e) =
      (ε : F) * ∏ α ∈ s, (u - (α : F)) ^ e α := by
  classical
  have hcast (α : ℚ) : algebraMap ℚ F α = (α : F) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ F) α
  simp only [signedRationalNumerator, signedRationalDenominator, map_mul, map_prod,
    map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hcast, Rat.cast_intCast]
  rw [mul_div_assoc, div_eq_mul_inv, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro α _
  cases e α with
  | ofNat n => simp
  | negSucc n => simp [zpow_negSucc]

theorem signedRational_series_eval {F : Type*} [Field F] [CharZero F] [Algebra ℚ F]
    (u : PowerSeries F) (ε : ℤ) (s : Finset ℚ) (e : ℚ → ℤ) :
    Polynomial.aeval u (signedRationalNumerator ε s e) *
        (Polynomial.aeval u (signedRationalDenominator s e))⁻¹ =
      PowerSeries.C (ε : F) * Matrix.signedNormalProduct s
        (fun α => u - PowerSeries.C (α : F)) e := by
  classical
  have hcast (α : ℚ) : algebraMap ℚ F α = (α : F) := by
    simpa only [Rat.cast_id] using map_ratCast (algebraMap ℚ F) α
  simp only [signedRationalNumerator, signedRationalDenominator, map_mul, map_prod,
    map_pow, map_sub, Polynomial.aeval_X, Polynomial.aeval_C,
    PowerSeries.algebraMap_apply, hcast, Rat.cast_intCast]
  unfold Matrix.signedNormalProduct
  rw [mul_assoc]

theorem constantCoeff_aeval_series {F : Type*} [Field F] [Algebra ℚ F]
    (u : PowerSeries F) (p : Polynomial ℚ) :
    PowerSeries.constantCoeff (Polynomial.aeval u p) =
      Polynomial.aeval (PowerSeries.constantCoeff u) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp only [map_add, hp, hq]
  | monomial n a =>
    simp only [Polynomial.aeval_monomial, map_mul, map_pow, PowerSeries.algebraMap_apply,
      PowerSeries.constantCoeff_C]

private theorem regular_series_quotient_eq {F : Type*} [Field F]
    (p q n d : PowerSeries F)
    (hq : PowerSeries.constantCoeff q ≠ 0) (hd : PowerSeries.constantCoeff d ≠ 0)
    (hcross : p * d = n * q) : p * q⁻¹ = n * d⁻¹ := by
  have hqne : q ≠ 0 := by
    intro hz
    exact hq (by rw [hz, map_zero])
  have hdne : d ≠ 0 := by
    intro hz
    exact hd (by rw [hz, map_zero])
  have hiq : q⁻¹ * q = 1 := by rw [mul_comm]; exact PowerSeries.mul_inv_cancel q hq
  have hid : d⁻¹ * d = 1 := by rw [mul_comm]; exact PowerSeries.mul_inv_cancel d hd
  apply mul_right_cancel₀ (mul_ne_zero hqne hdne)
  calc
    (p * q⁻¹) * (q * d) = p * (q⁻¹ * q) * d := by ring
    _ = p * d := by rw [hiq, mul_one]
    _ = n * q := hcross
    _ = n * (d⁻¹ * d) * q := by rw [hid, mul_one]
    _ = (n * d⁻¹) * (q * d) := by ring

theorem signedRational_series_transfer {F : Type*} [Field F] [CharZero F] [Algebra ℚ F]
    (u₀ : F) (hu₀ : Transcendental ℚ u₀) (u : PowerSeries F)
    (hu : PowerSeries.constantCoeff u = u₀)
    (p q : Polynomial ℚ) (hq : q ≠ 0) (ε : ℤ) (s : Finset ℚ) (e : ℚ → ℤ)
    (hfactor : Polynomial.aeval u₀ p / Polynomial.aeval u₀ q =
      (ε : F) * ∏ α ∈ s, (u₀ - (α : F)) ^ e α) :
    Polynomial.aeval u p * (Polynomial.aeval u q)⁻¹ =
      PowerSeries.C (ε : F) * Matrix.signedNormalProduct s
        (fun α => u - PowerSeries.C (α : F)) e := by
  have hden := signedRationalDenominator_ne_zero s e
  have hcross := transcendental_rational_representation_unique hu₀ p q
    (signedRationalNumerator ε s e) (signedRationalDenominator s e) hq hden
    (hfactor.trans (signedRational_aeval u₀ ε s e).symm)
  have hi := transcendental_iff_injective.mp hu₀
  have hq0 : PowerSeries.constantCoeff (Polynomial.aeval u q) ≠ 0 := by
    rw [constantCoeff_aeval_series, hu]
    intro hz
    exact hq (hi (hz.trans (map_zero _).symm))
  have hd0 : PowerSeries.constantCoeff
      (Polynomial.aeval u (signedRationalDenominator s e)) ≠ 0 := by
    rw [constantCoeff_aeval_series, hu]
    intro hz
    exact hden (hi (hz.trans (map_zero _).symm))
  have hc : Polynomial.aeval u p * Polynomial.aeval u (signedRationalDenominator s e) =
      Polynomial.aeval u (signedRationalNumerator ε s e) * Polynomial.aeval u q := by
    simpa only [map_mul] using congrArg (Polynomial.aeval u) hcross
  rw [regular_series_quotient_eq _ _ _ _ hq0 hd0 hc, signedRational_series_eval]

end SkewCornerDescent
