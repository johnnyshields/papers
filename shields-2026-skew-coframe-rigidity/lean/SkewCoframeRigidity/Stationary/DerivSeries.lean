/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.Deriv
import SkewCoframeRigidity.ClippedOperator

/-!
# The derivative of power series and of the clipped operator

The coefficientwise extension `dS m` of `dRaw m` to power series is a derivation of
`CohField⟦X⟧`.  It commutes with truncation, and the derivative of the clipped operator follows
from the Leibniz rule.  Formalizes the derivative computations of
`shields-2026-skew-coframe-rigidity.tex`, `sc:top-matching`, `sc:positive-power`.
-/

namespace SkewCoframeRigidity.Coframe

open SkewCofactorIndependence PowerSeries

/-- The coefficientwise derivative of a power series over the raw field. -/
noncomputable def dS (m : ℕ) (φ : PowerSeries CohField) : PowerSeries CohField :=
  PowerSeries.mk fun i => dRaw m (PowerSeries.coeff i φ)

theorem coeff_dS (m : ℕ) (φ : PowerSeries CohField) (i : ℕ) :
    PowerSeries.coeff i (dS m φ) = dRaw m (PowerSeries.coeff i φ) := by
  simp [dS]

theorem dS_add (m : ℕ) (φ ψ : PowerSeries CohField) : dS m (φ + ψ) = dS m φ + dS m ψ := by
  ext i; simp [coeff_dS, dRaw_add]

theorem dS_sub (m : ℕ) (φ ψ : PowerSeries CohField) : dS m (φ - ψ) = dS m φ - dS m ψ := by
  ext i; simp [coeff_dS, dRaw_sub]

theorem dS_mul (m : ℕ) (φ ψ : PowerSeries CohField) :
    dS m (φ * ψ) = dS m φ * ψ + φ * dS m ψ := by
  ext i
  rw [coeff_dS, map_add, coeff_mul, coeff_mul, coeff_mul, dRaw_sum]
  simp only [dRaw_mul, coeff_dS, Finset.sum_add_distrib]

theorem dS_zero (m : ℕ) : dS m 0 = 0 := by ext i; simp [coeff_dS, dRaw_zero]

theorem dS_one (m : ℕ) : dS m 1 = 0 := by
  ext i; rw [coeff_dS, coeff_one]; split_ifs <;> simp [dRaw_one, dRaw_zero]

theorem dS_pow (m : ℕ) (φ : PowerSeries CohField) (k : ℕ) :
    dS m (φ ^ k) = k • (φ ^ (k - 1) * dS m φ) := by
  induction k with
  | zero => simp [dS_one]
  | succ k ih =>
    rw [pow_succ, dS_mul, ih]
    rcases k with _ | k
    · simp [dS_one]
    · simp only [Nat.add_sub_cancel, pow_succ, smul_mul_assoc, mul_smul_comm, succ_nsmul]
      ring_nf

theorem dS_pow' (m : ℕ) (φ : PowerSeries CohField) (k : ℕ) :
    dS m (φ ^ k) = PowerSeries.C (k : CohField) * (φ ^ (k - 1) * dS m φ) := by
  rw [dS_pow, nsmul_eq_mul]
  simp

theorem dS_mk_letters (m : ℕ) :
    dS m (PowerSeries.mk cohLetters) = PowerSeries.X ^ m := by
  ext i
  rw [coeff_dS, coeff_mk, dRaw_letter, coeff_X_pow]

theorem dS_trunc (m M : ℕ) (φ : PowerSeries CohField) :
    dS m (PowerSeries.trunc M φ : PowerSeries CohField) = (PowerSeries.trunc M (dS m φ) : _) := by
  ext i
  rw [coeff_dS, Polynomial.coeff_coe, Polynomial.coeff_coe, coeff_trunc, coeff_trunc]
  split_ifs
  · exact (coeff_dS m φ i).symm
  · exact dRaw_zero m

end SkewCoframeRigidity.Coframe
