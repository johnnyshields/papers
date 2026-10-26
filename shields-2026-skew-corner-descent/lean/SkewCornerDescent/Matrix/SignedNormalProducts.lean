/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalProductLog

/-!
# Signed products of complete original normal series

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Positive and negative multiplicities are represented by complete numerator and
inverse denominator series. Logging preserves the signed count of every factor;
earlier intrinsic coefficients are retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {F : Type*} [Field F] [CharZero F] [Module ℚ F]

/-- The complete signed product, not a residue-only denominator substitution. -/
noncomputable def signedNormalProduct {ι : Type*} (s : Finset ι)
    (p : ι → PowerSeries F) (e : ι → ℤ) : PowerSeries F :=
  (∏ i ∈ s, p i ^ (e i).toNat) * (∏ i ∈ s, p i ^ (-e i).toNat)⁻¹

omit [CharZero F] [Module ℚ F] in
/-- The full signed product specializes to the ordinary integer-power residue product. -/
theorem signedNormalProduct_constant {ι : Type*} (s : Finset ι)
    (p : ι → PowerSeries F) (e : ι → ℤ) :
    PowerSeries.constantCoeff (signedNormalProduct s p e) =
      ∏ i ∈ s, PowerSeries.constantCoeff (p i) ^ e i := by
  classical
  unfold signedNormalProduct
  simp only [map_mul, map_prod, map_pow, PowerSeries.constantCoeff_inv]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  cases e i with
  | ofNat a => simp
  | negSucc a => simp [zpow_negSucc]

omit [CharZero F] [Module ℚ F] in
/-- A complete signed product remains a normal unit when all original factors are units. -/
theorem signedNormalProduct_constant_ne_zero {ι : Type*} (s : Finset ι)
    (p : ι → PowerSeries F) (e : ι → ℤ)
    (hp0 : ∀ i ∈ s, PowerSeries.constantCoeff (p i) ≠ 0) :
    PowerSeries.constantCoeff (signedNormalProduct s p e) ≠ 0 := by
  classical
  unfold signedNormalProduct
  simp only [map_mul, map_prod, map_pow, PowerSeries.constantCoeff_inv]
  apply mul_ne_zero
  · exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hp0 i hi))
  · exact inv_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hp0 i hi)))

/-- Complete inverse factors cannot introduce a resolving generator at an earlier order. -/
theorem coeff_deriv_signed_product_zero {ι : Type*} (D : Derivation ℚ F F)
    (s : Finset ι) (p : ι → PowerSeries F) (e : ι → ℤ) (n : ℕ)
    (hp0 : ∀ i ∈ s, PowerSeries.constantCoeff (p i) ≠ 0)
    (hp : ∀ i ∈ s, ∀ k, k ≤ n → D (PowerSeries.coeff k (p i)) = 0) :
    D (PowerSeries.coeff n (signedNormalProduct s p e)) = 0 := by
  classical
  have ha (a : ι → ℕ) (k : ℕ) (hk : k ≤ n) :
      D (PowerSeries.coeff k (∏ i ∈ s, p i ^ a i)) = 0 :=
    coeff_deriv_prod_zero D s (fun i => p i ^ a i) k
      (fun i hi l hl => coeff_deriv_pow_zero D (p i) l
        (fun j hj => hp i hi j (hj.trans (hl.trans hk))) (a i))
  have hneg0 : PowerSeries.constantCoeff (∏ i ∈ s, p i ^ (-e i).toNat) ≠ 0 := by
    simp only [map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hp0 i hi))
  apply coeff_deriv_mul_zero D _ _ n (ha _)
  intro k hk
  exact coeff_deriv_inv_zero D _ k hneg0 (fun l hl => ha _ l (hl.trans hk))

/-- The first fresh normalized logarithmic coefficient has the exact signed factor sum. -/
theorem coeff_deriv_normalized_signed_product_log_first {ι : Type*}
    (D : Derivation ℚ F F) (s : Finset ι) (p : ι → PowerSeries F) (e : ι → ℤ)
    (n : ℕ) (hn : 0 < n)
    (hp0 : ∀ i ∈ s, PowerSeries.constantCoeff (p i) ≠ 0)
    (hp : ∀ i ∈ s, ∀ k, k < n → D (PowerSeries.coeff k (p i)) = 0) :
    D (PowerSeries.coeff n (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff (signedNormalProduct s p e))⁻¹ *
        signedNormalProduct s p e))) =
      ∑ i ∈ s, (e i : F) * D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (p i))⁻¹ * p i))) := by
  classical
  have ha (a : ι → ℕ) :
      ∀ k, k < n → D (PowerSeries.coeff k (∏ i ∈ s, p i ^ a i)) = 0 :=
    fun k hk => coeff_deriv_prod_zero D s (fun i => p i ^ a i) k
      (fun i hi l hl => coeff_deriv_pow_zero D (p i) l
        (fun j hj => hp i hi j (hj.trans_lt (hl.trans_lt hk))) (a i))
  have ha0 (a : ι → ℕ) : PowerSeries.constantCoeff (∏ i ∈ s, p i ^ a i) ≠ 0 := by
    simp only [map_prod, map_pow]
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => pow_ne_zero _ (hp0 i hi))
  have hi : ∀ k, k < n →
      D (PowerSeries.coeff k (∏ i ∈ s, p i ^ (-e i).toNat)⁻¹) = 0 :=
    fun k hk => coeff_deriv_inv_zero D _ k (ha0 _)
      (fun l hl => ha _ l (hl.trans_lt hk))
  have hi0 : PowerSeries.constantCoeff (∏ i ∈ s, p i ^ (-e i).toNat)⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]
    exact inv_ne_zero (ha0 _)
  have hl (a : ι → ℕ) :
      D (PowerSeries.coeff n (PowerSeries.logOf
        (PowerSeries.C (PowerSeries.constantCoeff (∏ i ∈ s, p i ^ a i))⁻¹ *
          ∏ i ∈ s, p i ^ a i))) =
        ∑ i ∈ s, (a i : F) * D (PowerSeries.coeff n
          (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (p i))⁻¹ * p i))) := by
    rw [coeff_deriv_normalized_prod_log_first D s _ n hn
      (fun i hi => by rw [map_pow]; exact pow_ne_zero _ (hp0 i hi))
      (fun i hi k hk => coeff_deriv_pow_zero D (p i) k
        (fun l hl => hp i hi l (hl.trans_lt hk)) _)]
    apply Finset.sum_congr rfl
    intro i hi
    exact coeff_deriv_normalized_pow_log_first D _ n hn (hp0 i hi) (hp i hi) _
  unfold signedNormalProduct
  rw [coeff_deriv_normalized_mul_log_first D _ _ n hn (ha0 _) hi0 (ha _) hi,
    coeff_deriv_normalized_inv_log_first D _ n hn (ha0 _) (ha _)]
  rw [hl, hl, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← sub_mul]
  congr 1
  have he : ((e i).toNat : ℤ) - ((-e i).toNat : ℤ) = e i := by omega
  exact_mod_cast he

end SkewCornerDescent.Matrix
