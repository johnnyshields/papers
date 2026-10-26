/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.OriginalNormalSeries
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Data.ENat.SuccOrder

/-!
# Original prime order and full normal coefficients

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Vanishing of all normal coefficients below an arbitrary natural order is equivalent to
that power of the actual selected prime dividing the original numerator. Regular
original denominators do not change this equivalence. The boundary order zero is included.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix.SelectedCoordinate

open SkewGluing

variable {D : Diagram} {hD : IsConnectedSkew D} (c : SelectedCoordinate D hD)

/-- No power divisibility is lost in the actual affine normal chart. -/
theorem normalChart_prime_pow_dvd_iff (f : Lambda) (k : ℕ) :
    Polynomial.X ^ k ∣ c.normalChart f ↔ (cellSchur D hD.1) ^ k ∣ f := by
  change IsSkew D ∧ IsEdgeConnected D at hD
  let := invertibleOfNonzero c.normalCoefficient_ne_zero
  let : NormalizedGCDMonoid (OtherPolynomial c.top) := Classical.arbitrary _
  have hprim : ((splitGenerator c.top (cellSchur D hD.1)) ^ k).IsPrimitive := by
    induction k with
    | zero => simpa only [pow_zero] using Polynomial.isPrimitive_one
    | succ k ih => simpa only [pow_succ] using ih.mul c.split_prime_isPrimitive
  rw [← c.normalChart_prime, ← map_pow]
  change (Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm
      (splitOverField c.top ((cellSchur D hD.1) ^ k)) ∣
    (Polynomial.algEquivCMulXAddC c.normalCoefficient c.normalRemainder).symm
      (splitOverField c.top f) ↔ _
  rw [map_dvd_iff]
  have hg : splitOverField c.top ((cellSchur D hD.1) ^ k) ∣ splitOverField c.top f ↔
      (splitGenerator c.top (cellSchur D hD.1)) ^ k ∣ splitGenerator c.top f := by
    convert! (hprim.dvd_iff_fraction_map_dvd_fraction_map (OtherField c.top)
      (q := splitGenerator c.top f)).symm using 1
    simp [splitOverField]
  have hs : (splitGenerator c.top (cellSchur D hD.1)) ^ k ∣ splitGenerator c.top f ↔
      (cellSchur D hD.1) ^ k ∣ f := by
    simpa only [map_pow] using
      (map_dvd_iff (splitGenerator c.top) :
        splitGenerator c.top ((cellSchur D hD.1) ^ k) ∣ splitGenerator c.top f ↔
          (cellSchur D hD.1) ^ k ∣ f)
  exact hg.trans hs

/-- Full normal-series coefficients of an original polynomial detect exactly its prime power. -/
theorem normalPolynomialSeries_coeff_vanish_iff (f : Lambda) (k : ℕ) :
    (∀ j, j < k → PowerSeries.coeff j (c.normalPolynomialSeries f) = 0) ↔
      (cellSchur D hD.1) ^ k ∣ f := by
  simp only [normalPolynomialSeries, RingHom.comp_apply,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe]
  rw [← Polynomial.X_pow_dvd_iff]
  exact c.normalChart_prime_pow_dvd_iff f k

/-- Inverting the full regular denominator changes no normal vanishing order. -/
theorem normalSeries_fraction_coeff_vanish_iff (f : Lambda)
    (y : c.selectedIdeal.primeCompl) (k : ℕ) :
    (∀ j, j < k → PowerSeries.coeff j
      (c.normalSeries (IsLocalization.mk' c.RegularRing f y)) = 0) ↔
      (cellSchur D hD.1) ^ k ∣ f := by
  rw [← PowerSeries.X_pow_dvd_iff, c.normalSeries_fraction]
  have hy : PowerSeries.constantCoeff (c.normalPolynomialSeries y) ≠ 0 := by
    simpa only [c.normalPolynomialSeries_constant] using c.regularDenominator_residue_ne_zero y
  have he : (PowerSeries.X : PowerSeries (OtherField c.top)) ^ k ∣
      c.normalPolynomialSeries f * (c.normalPolynomialSeries y)⁻¹ ↔
      (PowerSeries.X : PowerSeries (OtherField c.top)) ^ k ∣ c.normalPolynomialSeries f := by
    constructor
    · intro h
      have hm := dvd_mul_of_dvd_left h (c.normalPolynomialSeries y)
      simpa only [mul_assoc, PowerSeries.inv_mul_cancel _ hy, mul_one] using hm
    · intro h
      exact dvd_mul_of_dvd_left h _
  rw [he, PowerSeries.X_pow_dvd_iff]
  exact c.normalPolynomialSeries_coeff_vanish_iff f k

/-- A detected full original coefficient bounds the genuine extended prime order.
The numerator is consequently nonzero; zero cannot acquire a spurious finite order. -/
theorem normalSeries_fraction_order_le (f : Lambda)
    (y : c.selectedIdeal.primeCompl) (k : ℕ)
    (hk : PowerSeries.coeff k
      (c.normalSeries (IsLocalization.mk' c.RegularRing f y)) ≠ 0) :
    emultiplicity (cellSchur D hD.1) f ≤ (k : ℕ∞) := by
  have hn : ¬ (cellSchur D hD.1) ^ (k + 1) ∣ f := by
    intro h
    exact hk ((c.normalSeries_fraction_coeff_vanish_iff f y (k + 1)).mpr h k
      (Nat.lt_succ_self k))
  apply ENat.lt_natCast_add_one_iff.mp
  apply lt_of_not_ge
  intro h
  exact hn (pow_dvd_of_le_emultiplicity (by simpa only [Nat.cast_add, Nat.cast_one] using h))

end SkewCornerDescent.Matrix.SelectedCoordinate
