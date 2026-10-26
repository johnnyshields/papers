/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCornerDescent.Matrix.NormalInverseCoefficient

/-!
# Fresh logarithmic coefficients of complete normal products

Supports `shields-2026-skew-corner-descent.tex` (`lem:original-transfer`).
Complete product and inverse series remain in the expressions. Earlier intrinsic
coefficients need not vanish: only their resolving-generator derivatives do.
Repeated factors and their integer multiplicities are retained. Sorry-free.
-/

namespace SkewCornerDescent.Matrix

open scoped BigOperators

variable {F : Type*} [Field F] [CharZero F] [Module ℚ F]

/-- At the first fresh order, the normalized logarithm of a complete product is additive. -/
theorem coeff_deriv_normalized_mul_log_first (D : Derivation ℚ F F)
    (p q : PowerSeries F) (n : ℕ) (hn : 0 < n)
    (hp0 : PowerSeries.constantCoeff p ≠ 0) (hq0 : PowerSeries.constantCoeff q ≠ 0)
    (hp : ∀ k, k < n → D (PowerSeries.coeff k p) = 0)
    (hq : ∀ k, k < n → D (PowerSeries.coeff k q) = 0) :
    D (PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (p * q))⁻¹ * (p * q)))) =
      D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) +
      D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff q)⁻¹ * q))) := by
  have hpq : ∀ k, k < n → D (PowerSeries.coeff k (p * q)) = 0 :=
    fun k hk => coeff_deriv_mul_zero D p q k
      (fun l hl => hp l (hl.trans_lt hk)) (fun l hl => hq l (hl.trans_lt hk))
  have hpq0 : PowerSeries.constantCoeff (p * q) ≠ 0 := by
    rw [map_mul]
    exact mul_ne_zero hp0 hq0
  rw [coeff_deriv_normalized_log_first D _ n hn hpq0 hpq,
    coeff_deriv_normalized_log_first D p n hn hp0 hp,
    coeff_deriv_normalized_log_first D q n hn hq0 hq,
    coeff_deriv_mul_first D p q n hp hq, map_mul]
  simp only [smul_eq_mul]
  field_simp [hp0, hq0]
  ring

/-- Logging the complete inverse negates the original normalized logarithmic derivative. -/
theorem coeff_deriv_normalized_inv_log_first (D : Derivation ℚ F F)
    (p : PowerSeries F) (n : ℕ) (hn : 0 < n)
    (hp0 : PowerSeries.constantCoeff p ≠ 0)
    (hp : ∀ k, k < n → D (PowerSeries.coeff k p) = 0) :
    D (PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p⁻¹)⁻¹ * p⁻¹))) =
      -D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) := by
  have hi : ∀ k, k < n → D (PowerSeries.coeff k p⁻¹) = 0 :=
    fun k hk => coeff_deriv_inv_zero D p k hp0 (fun l hl => hp l (hl.trans_lt hk))
  have hi0 : PowerSeries.constantCoeff p⁻¹ ≠ 0 := by
    rw [PowerSeries.constantCoeff_inv]
    exact inv_ne_zero hp0
  rw [coeff_deriv_normalized_log_first D _ n hn hi0 hi,
    coeff_deriv_normalized_log_first D p n hn hp0 hp,
    coeff_deriv_inv_first D p n hn hp0 hp, PowerSeries.constantCoeff_inv]
  simp only [smul_eq_mul, inv_inv]
  field_simp [hp0]

/-- An actual power contributes its entire multiplicity to the fresh logarithmic coefficient. -/
theorem coeff_deriv_normalized_pow_log_first (D : Derivation ℚ F F)
    (p : PowerSeries F) (n : ℕ) (hn : 0 < n)
    (hp0 : PowerSeries.constantCoeff p ≠ 0)
    (hp : ∀ k, k < n → D (PowerSeries.coeff k p) = 0) (a : ℕ) :
    D (PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (p ^ a))⁻¹ * p ^ a))) =
      (a : F) * D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) := by
  induction a with
  | zero =>
    rw [pow_zero, coeff_deriv_normalized_log_first D 1 n hn (by simp)
      (fun k hk => by simp only [PowerSeries.coeff_one]; split_ifs <;> simp)]
    simp [PowerSeries.coeff_one, hn.ne']
  | succ a ih =>
    have ha0 : PowerSeries.constantCoeff (p ^ a) ≠ 0 := by
      rw [map_pow]
      exact pow_ne_zero a hp0
    have ha : ∀ k, k < n → D (PowerSeries.coeff k (p ^ a)) = 0 :=
      fun k hk => coeff_deriv_pow_zero D p k (fun l hl => hp l (hl.trans_lt hk)) a
    rw [pow_succ, coeff_deriv_normalized_mul_log_first D _ p n hn ha0 hp0 ha hp,
      ih, Nat.cast_add, Nat.cast_one]
    ring

/-- A complete finite product contributes all original occurrences, not just distinct values. -/
theorem coeff_deriv_normalized_prod_log_first {ι : Type*}
    (D : Derivation ℚ F F) (s : Finset ι) (p : ι → PowerSeries F)
    (n : ℕ) (hn : 0 < n)
    (hp0 : ∀ i ∈ s, PowerSeries.constantCoeff (p i) ≠ 0)
    (hp : ∀ i ∈ s, ∀ k, k < n → D (PowerSeries.coeff k (p i)) = 0) :
    D (PowerSeries.coeff n (PowerSeries.logOf
      (PowerSeries.C (PowerSeries.constantCoeff (∏ i ∈ s, p i))⁻¹ * ∏ i ∈ s, p i))) =
      ∑ i ∈ s, D (PowerSeries.coeff n
        (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff (p i))⁻¹ * p i))) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, coeff_deriv_normalized_log_first D 1 n hn (by simp)
      (fun k hk => by simp only [PowerSeries.coeff_one]; split_ifs <;> simp)]
    simp [PowerSeries.coeff_one, hn.ne']
  | @insert i s hi ih =>
    have hs0 : PowerSeries.constantCoeff (∏ j ∈ s, p j) ≠ 0 := by
      rw [map_prod]
      exact Finset.prod_ne_zero_iff.mpr
        (fun j hj => hp0 j (Finset.mem_insert_of_mem hj))
    have hs : ∀ k, k < n → D (PowerSeries.coeff k (∏ j ∈ s, p j)) = 0 :=
      fun k hk => coeff_deriv_prod_zero D s p k
        (fun j hj l hl => hp j (Finset.mem_insert_of_mem hj) l (hl.trans_lt hk))
    rw [Finset.prod_insert hi, coeff_deriv_normalized_mul_log_first D _ _ n hn
      (hp0 i (Finset.mem_insert_self _ _)) hs0
      (hp i (Finset.mem_insert_self _ _)) hs,
      ih (fun j hj => hp0 j (Finset.mem_insert_of_mem hj))
        (fun j hj => hp j (Finset.mem_insert_of_mem hj)), Finset.sum_insert hi]

end SkewCornerDescent.Matrix
