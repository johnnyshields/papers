/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/

import SkewCornerDescent.Matrix.NormalNextCoefficientLeibniz
import SkewCornerDescent.Matrix.NormalLogCoefficient

/-!
# Exact next-fresh derivatives of the complete normalized logarithm

Supports `shields-2026-skew-corner-descent.tex` (`prop:normal-interface`).
The full logarithmic substitution retains its quadratic self-term at order two.
At the next fresh order, the entire first normal coefficient supplies the
logarithmic correction; it is not replaced by an onsite or frozen-unit value.
Sorry-free.
-/

namespace SkewCornerDescent.Matrix

variable {F M : Type*} [Field F] [Algebra ℚ F]
  [AddCommGroup M] [Module F M] [Module ℚ M]

/-- The complete logarithm at the next fresh order has exactly its original fresh
coefficient and the correction from the entire first coefficient. -/
theorem coeff_deriv_log_next (D : Derivation ℚ F M) (f : PowerSeries F) (n : ℕ)
    (hn : 2 ≤ n) (hf : PowerSeries.constantCoeff f = 1)
    (hprev : ∀ k, k < n - 1 → D (PowerSeries.coeff k f) = 0) :
    D (PowerSeries.coeff n (PowerSeries.logOf f)) =
      D (PowerSeries.coeff n f) -
        PowerSeries.coeff 1 f • D (PowerSeries.coeff (n - 1) f) := by
  classical
  let : CharZero F := Algebra.charZero_of_charZero (R := ℚ) (A := F)
  have h0 : PowerSeries.constantCoeff (f - 1) = 0 := by simp [hf]
  have hb := PowerSeries.HasSubst.of_constantCoeff_zero' h0
  have hp : ∀ k, k < n - 1 → D (PowerSeries.coeff k (f - 1)) = 0 := by
    intro k hk
    simp only [map_sub, PowerSeries.coeff_one]
    split_ifs <;> simp [hprev k hk]
  rw [PowerSeries.logOf_eq, PowerSeries.coeff_subst' hb]
  change D.toLinearMap.toAddMonoidHom
    (∑ᶠ a, PowerSeries.coeff a (PowerSeries.log F) •
      PowerSeries.coeff n ((f - 1) ^ a)) = _
  rw [D.toLinearMap.toAddMonoidHom.map_finsum
    (PowerSeries.coeff_subst_finite' hb (PowerSeries.log F) n)]
  change (∑ᶠ a, D (PowerSeries.coeff a (PowerSeries.log F) •
    PowerSeries.coeff n ((f - 1) ^ a))) = _
  have hterm (a : ℕ) :
      D (PowerSeries.coeff a (PowerSeries.log F) • PowerSeries.coeff n ((f - 1) ^ a)) =
        if a = 1 then D (PowerSeries.coeff n f)
        else if a = 2 then -(PowerSeries.coeff 1 f • D (PowerSeries.coeff (n - 1) f))
        else 0 := by
    rw [smul_eq_mul, Derivation.leibniz]
    have hc : D (PowerSeries.coeff a (PowerSeries.log F)) = 0 := by
      rw [PowerSeries.coeff_log]
      split_ifs
      · exact map_zero D
      · exact D.map_algebraMap _
    rw [hc, smul_zero, add_zero, coeff_deriv_pow_next D _ n hn h0 hp]
    by_cases ha : a = 1
    · subst a
      simp [PowerSeries.coeff_log, PowerSeries.coeff_one, show n ≠ 0 by omega]
    · by_cases ha2 : a = 2
      · subst a
        norm_num [PowerSeries.coeff_log, PowerSeries.coeff_one,
          show n - 1 ≠ 0 by omega, smul_smul]
        rw [← mul_assoc, div_mul_cancel₀ _ (by norm_num : (2 : F) ≠ 0), one_mul]
      · simp [ha, ha2]
  simp_rw [hterm]
  have hs : Function.support (fun a : ℕ =>
      if a = 1 then D (PowerSeries.coeff n f)
      else if a = 2 then -(PowerSeries.coeff 1 f • D (PowerSeries.coeff (n - 1) f))
      else 0) ⊆ ({1, 2} : Finset ℕ) := by
    intro a ha
    by_cases h1 : a = 1
    · simp [h1]
    · by_cases h2 : a = 2
      · simp [h2]
      · simp [Function.mem_support, h1, h2] at ha
  rw [finsum_eq_sum_of_support_subset _ hs]
  simp [sub_eq_add_neg]

/-- Normalization by the actual nonzero constant retains the complete first-coefficient
correction at the next fresh order. This includes all original inverse jets. -/
theorem coeff_deriv_normalized_log_next (D : Derivation ℚ F M) (p : PowerSeries F)
    (n : ℕ) (hn : 2 ≤ n) (hunit : PowerSeries.constantCoeff p ≠ 0)
    (hprev : ∀ k, k < n - 1 → D (PowerSeries.coeff k p) = 0) :
    D (PowerSeries.coeff n
      (PowerSeries.logOf (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p))) =
      (PowerSeries.constantCoeff p)⁻¹ • D (PowerSeries.coeff n p) -
        ((PowerSeries.constantCoeff p)⁻¹ ^ 2 * PowerSeries.coeff 1 p) •
          D (PowerSeries.coeff (n - 1) p) := by
  have h0 : D (PowerSeries.constantCoeff p) = 0 := by
    simpa only [PowerSeries.coeff_zero_eq_constantCoeff_apply] using hprev 0 (by omega)
  have hi : D (PowerSeries.constantCoeff p)⁻¹ = 0 := by
    rw [Derivation.leibniz_inv, h0, smul_zero]
  have hf : PowerSeries.constantCoeff (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p) = 1 := by
    simp [hunit]
  have hd (k : ℕ) : D (PowerSeries.coeff k
      (PowerSeries.C (PowerSeries.constantCoeff p)⁻¹ * p)) =
      (PowerSeries.constantCoeff p)⁻¹ • D (PowerSeries.coeff k p) := by
    rw [PowerSeries.coeff_C_mul, Derivation.leibniz, hi, smul_zero, add_zero]
  rw [coeff_deriv_log_next D _ n hn hf
      (fun k hk => by rw [hd k, hprev k hk, smul_zero]),
    hd n, hd (n - 1), PowerSeries.coeff_C_mul, smul_smul]
  rw [show (PowerSeries.constantCoeff p)⁻¹ * PowerSeries.coeff 1 p *
      (PowerSeries.constantCoeff p)⁻¹ =
      (PowerSeries.constantCoeff p)⁻¹ ^ 2 * PowerSeries.coeff 1 p by ring]

end SkewCornerDescent.Matrix
