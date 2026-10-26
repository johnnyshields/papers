/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import SkewCoframeRigidity.Stationary.MatchedDeriv
import SkewCoframeRigidity.Stationary.Ratio

/-!
# Low coefficients of powers of a series

The coefficients of degrees `0`, `1`, `2` of `φ^q`, and the resulting expansion of
`(p-1)φ^p - p φ_0 φ^{p-1} + φ_0^p`, used in the second pole jet of the cell case of
`sc:positive-power` (`sc:cell-second-jet`).
-/

namespace SkewCoframeRigidity.Coframe

open PowerSeries

theorem coeff_zero_pow' {R : Type*} [CommRing R] (φ : PowerSeries R) (q : ℕ) :
    coeff 0 (φ ^ q) = coeff 0 φ ^ q := by
  rw [coeff_zero_eq_constantCoeff_apply, map_pow, ← coeff_zero_eq_constantCoeff_apply]

theorem coeff_two_mul {R : Type*} [CommRing R] (φ ψ : PowerSeries R) :
    coeff 2 (φ * ψ) = coeff 0 φ * coeff 2 ψ + coeff 1 φ * coeff 1 ψ + coeff 2 φ * coeff 0 ψ := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_one_mul' {R : Type*} [CommRing R] (φ ψ : PowerSeries R) :
    coeff 1 (φ * ψ) = coeff 0 φ * coeff 1 ψ + coeff 1 φ * coeff 0 ψ := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [Finset.sum_range_succ]

theorem coeff_one_pow'' {R : Type*} [CommRing R] (φ : PowerSeries R) (q : ℕ) :
    coeff 1 (φ ^ q) = q * coeff 0 φ ^ (q - 1) * coeff 1 φ := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, coeff_one_mul', ih, coeff_zero_pow']
    rcases q with _ | q
    · simp
    · simp only [Nat.add_sub_cancel]; push_cast; ring

theorem coeff_two_pow {R : Type*} [CommRing R] (φ : PowerSeries R) (q : ℕ) :
    coeff 2 (φ ^ q) = q * coeff 0 φ ^ (q - 1) * coeff 2 φ +
      (q.choose 2 : R) * coeff 0 φ ^ (q - 2) * coeff 1 φ ^ 2 := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ, coeff_two_mul, ih, coeff_zero_pow', coeff_one_pow'']
    rcases q with _ | _ | q
    · simp
    · simp; ring
    · have hc : (((q + 1 + 1 + 1).choose 2 : ℕ) : R) = ((q + 1 + 1).choose 2 : ℕ) + (q + 2) := by
        rw [Nat.choose_succ_succ (q + 1 + 1) 1]; simp; ring
      have e1 : q + 1 + 1 + 1 - 1 = q + 1 + 1 := rfl
      have e2 : q + 1 + 1 + 1 - 2 = q + 1 := rfl
      have e3 : q + 1 + 1 - 1 = q + 1 := rfl
      have e4 : q + 1 + 1 - 2 = q := rfl
      rw [e1, e2, e3, e4, hc]
      push_cast
      ring

/-- `F = φ_0^p + (p-1) φ^p - p φ_0 φ^{p-1}` has order two with leading coefficient
`C(p,2) φ_0^{p-2} φ_1^2`. -/
noncomputable def cellF {R : Type*} [CommRing R] (φ : PowerSeries R) (p : ℕ) : PowerSeries R :=
  PowerSeries.C (coeff 0 φ ^ p) + PowerSeries.C ((p : R) - 1) * φ ^ p -
    PowerSeries.C ((p : R) * coeff 0 φ) * φ ^ (p - 1)

theorem cellF_coeff_eq {R : Type*} [CommRing R] (φ : PowerSeries R) (p n : ℕ) :
    coeff n (cellF φ p) = (if n = 0 then coeff 0 φ ^ p else 0) +
      ((p : R) - 1) * coeff n (φ ^ p) - ((p : R) * coeff 0 φ) * coeff n (φ ^ (p - 1)) := by
  unfold cellF
  rw [map_sub, map_add, coeff_C, coeff_C_mul, coeff_C_mul]

theorem cellF_coeff {R : Type*} [CommRing R] (φ : PowerSeries R) (q : ℕ) :
    coeff 0 (cellF φ (q + 2)) = 0 ∧ coeff 1 (cellF φ (q + 2)) = 0 ∧
      coeff 2 (cellF φ (q + 2)) =
        ((q + 2).choose 2 : R) * coeff 0 φ ^ q * coeff 1 φ ^ 2 := by
  have e1 : q + 2 - 1 = q + 1 := rfl
  refine ⟨?_, ?_, ?_⟩
  · rw [cellF_coeff_eq, e1, coeff_zero_pow', coeff_zero_pow']
    simp only [if_true]; push_cast; ring
  · rw [cellF_coeff_eq, e1, coeff_one_pow'', coeff_one_pow'']
    simp only [show (1 : ℕ) ≠ 0 by omega, if_false, zero_add]
    simp only [show q + 2 - 1 = q + 1 from rfl, show q + 1 - 1 = q from rfl]
    push_cast; ring
  · rw [cellF_coeff_eq, e1, coeff_two_pow, coeff_two_pow]
    simp only [show (2 : ℕ) ≠ 0 by omega, if_false, zero_add]
    rcases q with _ | q
    · simp; ring
    · have hc : (((q + 1 + 2).choose 2 : ℕ) : R) = ((q + 1 + 1).choose 2 : ℕ) + (q + 2) := by
        rw [show q + 1 + 2 = (q + 1 + 1) + 1 from rfl, Nat.choose_succ_succ (q + 1 + 1) 1]
        simp; ring
      simp only [show q + 1 + 2 - 1 = q + 1 + 1 from rfl, show q + 1 + 2 - 2 = q + 1 from rfl,
        show q + 1 + 1 - 1 = q + 1 from rfl, show q + 1 + 1 - 2 = q from rfl,
        show q + 1 + 1 + 1 - 1 = q + 1 + 1 from rfl, show q + 1 + 1 + 1 - 2 = q + 1 from rfl,
        show q + 1 - 1 = q from rfl]
      have hc2 : 2 * (((q + 1 + 1).choose 2 : ℕ) : R) = ((q : R) + 2) * ((q : R) + 1) := by
        have h : 2 * (q + 1 + 1).choose 2 = (q + 1 + 1) * (q + 1) := by
          rw [Nat.choose_two_right]
          exact Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd
        exact_mod_cast congrArg (fun x : ℕ => (x : R)) h |>.trans (by push_cast; ring)
      rw [hc]
      push_cast
      linear_combination (-(coeff 0 φ * coeff 0 φ ^ q * coeff 1 φ ^ 2)) * hc2

end SkewCoframeRigidity.Coframe
