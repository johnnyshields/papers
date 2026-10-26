/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.DerivSeries

/-!
# Differentiating the first variation in a letter

For a polynomial `Q` over the raw field, `dPoly L Q` is the coefficientwise derivative
`∂/∂H_L` of `Q`.  Differentiating a row equation `[HQ]_x = 0`, with `H = ∑ H_k z^k`, gives
`[H · dPoly L Q]_x = ∂_L [HQ]_x - Q_{x-L}`: the derivative of the letters contributes exactly the
coefficient `Q_{x-L}`, which the zero range removes.  Sorry-free.
-/

namespace SkewCoframeRigidity.UnitRestoration

open SkewCoframeRigidity.Coframe Polynomial PowerSeries

/-- The coefficientwise derivative `∂/∂H_L` of a polynomial over the raw field. -/
noncomputable def dPoly (L : ℕ) (Q : CohField[X]) : CohField[X] :=
  ∑ i ∈ Finset.range (Q.natDegree + 1), Polynomial.C (dRaw L (Q.coeff i)) * Polynomial.X ^ i

theorem coeff_dPoly (L : ℕ) (Q : CohField[X]) (i : ℕ) :
    (dPoly L Q).coeff i = dRaw L (Q.coeff i) := by
  unfold dPoly
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases h : i < Q.natDegree + 1
  · rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Ne.symm hj]
    · intro hi; exact absurd (Finset.mem_range.mpr h) hi
  · rw [Finset.sum_eq_zero]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), dRaw_zero]
    · intro j hj
      have : i ≠ j := by have := Finset.mem_range.mp hj; omega
      simp [this]

theorem coe_dPoly (L : ℕ) (Q : CohField[X]) :
    ((dPoly L Q : CohField[X]) : PowerSeries CohField) = dS L (Q : PowerSeries CohField) := by
  ext i
  rw [Polynomial.coeff_coe, coeff_dPoly, coeff_dS, Polynomial.coeff_coe]

/-- **Differentiating a row equation.**  `[H · ∂_L Q]_x = ∂_L [HQ]_x - Q_{x-L}`. -/
theorem coeff_letterSeries_mul_dPoly (L : ℕ) (Q : CohField[X]) (x : ℕ) :
    PowerSeries.coeff x (letterSeries * (dPoly L Q : PowerSeries CohField)) =
      dRaw L (PowerSeries.coeff x (letterSeries * (Q : PowerSeries CohField))) -
        (if L ≤ x then Q.coeff (x - L) else 0) := by
  have h := dS_mul L letterSeries (Q : PowerSeries CohField)
  have hls : dS L letterSeries = PowerSeries.X ^ L := dS_mk_letters L
  have h' := congrArg (PowerSeries.coeff x) h
  rw [hls, coeff_dS, map_add, ← coe_dPoly, PowerSeries.coeff_X_pow_mul',
    Polynomial.coeff_coe] at h'
  split_ifs at h' ⊢ <;> linear_combination -h'

end SkewCoframeRigidity.UnitRestoration
