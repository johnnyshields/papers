/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Scalar Taylor coefficients of an analytic function

The `m`-th Taylor coefficient of `F` at the origin, `(m!)^{-1}F^{(m)}(0)`, as a scalar rather than
through a `FormalMultilinearSeries`.  This is the form in which coefficients are compared,
multiplied and read off contour integrals.

Three facts carry the API: the coefficients depend only on the germ; they obey the Cauchy product
`c_n(FG) = \sum_{i+j=n} c_i(F)c_j(G)`; and, for `F` analytic on a closed disc, they are given by
Cauchy's formula `c_m = (2\pi i)^{-1}\oint F(z)z^{-m-1}\,dz`.

## Main results

* `Shields.taylorCoeff`, `Shields.taylorCoeff_zero`, `Shields.taylorCoeff_one`
* `Shields.taylorCoeff_congr` — only the germ matters
* `Shields.taylorCoeff_mul` — **the Cauchy product**
* `Shields.taylorCoeff_eq_coeff_of_mul_eq_one` — coefficients of a multiplicative inverse
* `Shields.taylorCoeff_eq_circleIntegral` — **Cauchy's coefficient formula**

## Implementation notes

The coefficient is defined by `iteratedDeriv` rather than by a power series, so that it is
available for any function and analyticity appears only where it is used.  A private helper for
`2πi ≠ 0` is not needed here: Mathlib's `Complex.two_pi_I_ne_zero` is used directly.

## Tags

taylor coefficient, cauchy product, cauchy integral formula, analytic
-/

open scoped Real
open Complex Filter Metric Nat Set Topology

namespace Shields

/-! ### Iterated derivatives of an entire function -/

/-- **Every derivative of an entire function is entire.**  Complex differentiability upgrades to
`ContDiff` of every order, and `ContDiff.differentiable_iteratedDeriv` does the rest. -/
theorem differentiable_iteratedDeriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (m : ℕ) :
    Differentiable ℂ (iteratedDeriv m f) :=
  (hf.contDiff (n := ⊤)).differentiable_iteratedDeriv m (by simp)

/-! ### The Taylor coefficient -/

/-- The `m`-th Taylor coefficient of `F` at the origin. -/
noncomputable def taylorCoeff (F : ℂ → ℂ) (m : ℕ) : ℂ :=
  ((m ! : ℕ) : ℂ)⁻¹ * iteratedDeriv m F 0

@[simp] theorem taylorCoeff_zero (F : ℂ → ℂ) : taylorCoeff F 0 = F 0 := by
  simp [taylorCoeff, iteratedDeriv_zero]

/-- Taylor coefficients depend only on the germ at the origin. -/
theorem taylorCoeff_congr {F G : ℂ → ℂ} (h : F =ᶠ[𝓝 0] G) (m : ℕ) :
    taylorCoeff F m = taylorCoeff G m := by
  rw [taylorCoeff, taylorCoeff, h.iteratedDeriv_eq m]

@[simp] theorem taylorCoeff_one (m : ℕ) :
    taylorCoeff (fun _ : ℂ => (1 : ℂ)) m = if m = 0 then 1 else 0 := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · simp [taylorCoeff, iteratedDeriv_const, hm.ne']

/-- **The Cauchy product.**  The Leibniz rule for iterated derivatives, divided by `m!`. -/
theorem taylorCoeff_mul {F G : ℂ → ℂ} (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) (m : ℕ) :
    taylorCoeff (fun z => F z * G z) m
      = ∑ i ∈ Finset.range (m + 1), taylorCoeff F i * taylorCoeff G (m - i) := by
  rw [taylorCoeff, iteratedDeriv_fun_mul hF.contDiffAt hG.contDiffAt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hle : i ≤ m := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  have h1 : ((m ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  have h2 : ((i ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
  have h3 : (((m - i)! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero (m - i))
  rw [taylorCoeff, taylorCoeff, Nat.cast_choose (K := ℂ) hle]
  field_simp

/-- The coefficients of `1 - c·H`, in the form the pencil denominator takes. -/
theorem taylorCoeff_one_sub_const_mul (c : ℂ) (H : ℂ → ℂ) (m : ℕ) :
    taylorCoeff (fun z => 1 - c * H z) m
      = if m = 0 then 1 - c * H 0 else -(c * taylorCoeff H m) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simp
  · rw [if_neg hm.ne', taylorCoeff, iteratedDeriv_const_sub (f := fun z => c * H z) hm 1,
      iteratedDeriv_neg, iteratedDeriv_const_mul_field, taylorCoeff]
    ring

/-! ### The formal inverse is computed by the analytic one -/

/-- **A triangular system with unit diagonal has one solution.**  If `F·D = 1` near the origin,
if the Taylor coefficients of `D` are those of a power series `S` with unit constant term, and if
`T·S = 1` formally, then the Taylor coefficients of `F` are those of `T`.

Nothing here asserts that the formal series converges to the analytic function.  Both coefficient
sequences solve `∑_{i≤m} c_i s_{m-i} = δ_{m0}`, which determines them: the Taylor side by the
Leibniz rule, the formal side by the definition of the product. -/
theorem taylorCoeff_eq_coeff_of_mul_eq_one {F D : ℂ → ℂ} {S T : PowerSeries ℂ}
    (hF : AnalyticAt ℂ F 0) (hD : AnalyticAt ℂ D 0)
    (heq : (fun z => F z * D z) =ᶠ[𝓝 0] fun _ => (1 : ℂ))
    (hS : ∀ j, taylorCoeff D j = PowerSeries.coeff j S)
    (hS0 : PowerSeries.coeff 0 S = 1) (hT : T * S = 1) (m : ℕ) :
    taylorCoeff F m = PowerSeries.coeff m T := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have hA : (∑ i ∈ Finset.range m, taylorCoeff F i * taylorCoeff D (m - i)) + taylorCoeff F m
        = if m = 0 then 1 else 0 := by
      have hmul := taylorCoeff_mul hF hD m
      rw [taylorCoeff_congr heq m, taylorCoeff_one, Finset.sum_range_succ] at hmul
      rw [Nat.sub_self, hS 0, hS0, mul_one] at hmul
      exact hmul.symm
    have hB : (∑ i ∈ Finset.range m,
          PowerSeries.coeff i T * PowerSeries.coeff (m - i) S) + PowerSeries.coeff m T
        = if m = 0 then 1 else 0 := by
      have hco := congrArg (PowerSeries.coeff (R := ℂ) m) hT
      rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
        Finset.sum_range_succ, Nat.sub_self, hS0, mul_one, PowerSeries.coeff_one] at hco
      exact hco
    have hsum : (∑ i ∈ Finset.range m, taylorCoeff F i * taylorCoeff D (m - i))
        = ∑ i ∈ Finset.range m, PowerSeries.coeff i T * PowerSeries.coeff (m - i) S :=
      Finset.sum_congr rfl fun i hi => by rw [ih i (Finset.mem_range.mp hi), hS]
    linear_combination hA - hB - hsum

/-! ### The contour side -/


/-- **Cauchy's formula for derivatives**, in the coefficient form `ClusterResidue` consumes. -/
theorem taylorCoeff_eq_circleIntegral {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall 0 R)) (m : ℕ) :
    (2 * Real.pi * I)⁻¹ * (∮ z in C(0, R), F z * z ^ (-(m : ℤ) - 1)) = taylorCoeff F m := by
  have hcong : (∮ z in C(0, R), F z * z ^ (-(m : ℤ) - 1))
      = ∮ z in C(0, R), (1 / (z - 0) ^ (m + 1)) • F z := by
    refine circleIntegral.integral_congr hR.le fun z hz => ?_
    have hz0 : z ≠ 0 := by
      intro h0
      have hzn : ‖z‖ = R := by simpa [Complex.dist_eq] using Metric.mem_sphere.mp hz
      rw [h0, norm_zero] at hzn
      exact absurd hzn.symm hR.ne'
    rw [sub_zero, smul_eq_mul, one_div,
      show (-(m : ℤ) - 1) = -((m + 1 : ℕ) : ℤ) by push_cast; ring, zpow_neg, zpow_natCast]
    ring
  rw [hcong, hF.circleIntegral_one_div_sub_center_pow_smul hR m, smul_eq_mul, taylorCoeff]
  have hfac : ((m ! : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero m)
  field_simp

/-- **The paper's convention `B_m = 0` for `m < 0` is Cauchy's theorem.**  At a negative index the
weight `z^{-m-1}` is a nonnegative power, so the integrand is regular on the whole disk. -/
theorem circleIntegral_mul_zpow_eq_zero_of_neg {F : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (Metric.closedBall 0 R)) {m : ℤ} (hm : m < 0) :
    (∮ z in C(0, R), F z * z ^ (-m - 1)) = 0 := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, -m - 1 = (j : ℤ) :=
    ⟨(-m - 1).toNat, (Int.toNat_of_nonneg (by omega)).symm⟩
  have hcong : (∮ z in C(0, R), F z * z ^ (-m - 1)) = ∮ z in C(0, R), F z * z ^ j :=
    circleIntegral.integral_congr hR.le fun z _ => by rw [hj, zpow_natCast]
  rw [hcong]
  refine Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
    Set.countable_empty ?_ ?_
  · exact hF.continuousOn.mul (continuousOn_id.pow j)
  · intro z hz
    exact (hF.differentiableAt (Metric.closedBall_mem_nhds_of_mem hz.1)).mul
      (differentiableAt_id.pow j)


/-! ### Axiom footprint -/

/-- info: 'Shields.taylorCoeff_eq_coeff_of_mul_eq_one' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms taylorCoeff_eq_coeff_of_mul_eq_one

/-- info: 'Shields.taylorCoeff_eq_circleIntegral' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms taylorCoeff_eq_circleIntegral

end Shields
