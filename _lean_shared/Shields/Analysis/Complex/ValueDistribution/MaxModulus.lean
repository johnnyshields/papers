/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.Harmonic.Poisson
import Shields.Analysis.Complex.ValueDistribution.Order

/-!
# From the characteristic to the maximum modulus

The Nevanlinna characteristic controls a circle *average* of `log⁺‖F‖`, while the Hadamard
rigidity theorems consume a *pointwise* bound on `\Re g` for `F = e^g`.  The Poisson formula
converts one into the other: the Poisson kernel of the disc of radius `R` is bounded by
`(R + r)/(R - r)` on the circle of radius `R`, so

  `\Re g(w) ≤ (R + r)/(R - r) · m(R, e^g)`  for `‖w‖ ≤ r < R`.

Taking `R = 2S` and `r = S` gives the factor `3` in the last result.

## Main results

* `Shields.poissonKernel_le` and `Shields.poissonKernel_mul_le` — the kernel bound on the
  circle, and the form the circle average consumes.
* `Shields.re_le_circleAverage_posPart` — the Poisson bound on the real part.
* `Shields.proximity_exp_eq_circleAverage` — `m(r, e^g)` is the circle average of `(\Re g)⁺`.
* `Shields.re_le_characteristic` — `\Re g ≤ 3 T(2S, e^g)` on the ball of radius `S`.

## Tags

Poisson kernel, maximum modulus, Nevanlinna characteristic, value distribution
-/

open Asymptotics Complex Filter Metric Real Set ValueDistribution
open scoped Topology

namespace Shields

/-! ### The Poisson kernel on a circle -/

/-- The Poisson kernel of the disc `‖z‖ < R` is nonnegative on the circle `‖z‖ = R`. -/
theorem poissonKernel_nonneg {R : ℝ} {w z : ℂ} (hw : ‖w‖ ≤ R) (hz : ‖z‖ = R) :
    0 ≤ poissonKernel 0 w z := by
  rw [poissonKernel_def]
  simp only [sub_zero, hz]
  exact div_nonneg (by nlinarith [norm_nonneg w]) (by positivity)

/-- The Poisson kernel of the disc `‖z‖ < R`, at a point of modulus at most `r < R`, is at most
`(R + r)/(R - r)` on the circle `‖z‖ = R`. -/
theorem poissonKernel_le {r R : ℝ} (hrR : r < R) {w z : ℂ} (hw : ‖w‖ ≤ r) (hz : ‖z‖ = R) :
    poissonKernel 0 w z ≤ (R + r) / (R - r) := by
  have hwR : ‖w‖ < R := lt_of_le_of_lt hw hrR
  have hker := re_herglotzRieszKernel_le (c := 0) (w := w)
    (mem_sphere_zero_iff_norm.2 hz) (mem_ball_zero_iff.2 hwR)
  simp only [sub_zero] at hker
  have hmono : (R + ‖w‖) / (R - ‖w‖) ≤ (R + r) / (R - r) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [norm_nonneg w]
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  simpa [herglotzRieszKernel] using hker.trans hmono

/-- **The kernel bound in the form the circle average consumes.**  The kernel's sign replaces the
value by its positive part, and the kernel's size then comes out of the product. -/
theorem poissonKernel_mul_le {r R : ℝ} (hrR : r < R) {w z : ℂ} (hw : ‖w‖ ≤ r) (hz : ‖z‖ = R)
    (x : ℝ) : poissonKernel 0 w z * x ≤ (R + r) / (R - r) * max 0 x :=
  calc poissonKernel 0 w z * x ≤ poissonKernel 0 w z * max 0 x :=
        mul_le_mul_of_nonneg_left (le_max_right _ _)
          (poissonKernel_nonneg (hw.trans hrR.le) hz)
    _ ≤ (R + r) / (R - r) * max 0 x :=
        mul_le_mul_of_nonneg_right (poissonKernel_le hrR hw hz) (le_max_left _ _)

/-! ### The Poisson bound on the real part -/

variable {g : ℂ → ℂ}

/-- **The Poisson bound.**  The real part of an entire function at a point of modulus at most `r`
is at most `(R + r)/(R - r)` times the circle average of its positive part over the circle of
radius `R > r`. -/
theorem re_le_circleAverage_posPart (hg : Differentiable ℂ g) {r R : ℝ} (hrR : r < R) {w : ℂ}
    (hw : ‖w‖ ≤ r) :
    (g w).re ≤ (R + r) / (R - r) * circleAverage (fun z ↦ max 0 (g z).re) 0 R := by
  have hr0 : 0 ≤ r := (norm_nonneg w).trans hw
  have hRpos : 0 < R := lt_of_le_of_lt hr0 hrR
  have hRabs : |R| = R := abs_of_pos hRpos
  have hwball : w ∈ ball (0 : ℂ) R := mem_ball_zero_iff.2 (lt_of_le_of_lt hw hrR)
  -- the kernel is continuous on the circle
  have hker : ContinuousOn (poissonKernel 0 w) (sphere (0 : ℂ) |R|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hwball)
  -- the Poisson formula for the harmonic function `\Re g`
  have hpoisson : circleAverage (fun z ↦ poissonKernel 0 w z * (g z).re) 0 R = (g w).re :=
    InnerProductSpace.HarmonicOnNhd.circleAverage_poissonKernel_smul
      (f := fun z ↦ (g z).re) (fun x _ ↦ (hg.analyticAt x).harmonicAt_re) hwball
  -- the integrand is dominated by the constant multiple of the positive part
  have hCI₁ : CircleIntegrable (fun z ↦ poissonKernel 0 w z * (g z).re) 0 R :=
    ContinuousOn.circleIntegrable'
      (hker.mul (Complex.continuous_re.comp_continuousOn hg.continuous.continuousOn))
  have hCI₂ : CircleIntegrable
      (fun z ↦ (R + r) / (R - r) * max 0 (g z).re) 0 R :=
    ContinuousOn.circleIntegrable'
      (continuousOn_const.mul
        ((continuous_const.max (Complex.continuous_re.comp hg.continuous)).continuousOn))
  have hmono : ∀ z ∈ sphere (0 : ℂ) |R|, poissonKernel 0 w z * (g z).re
      ≤ (R + r) / (R - r) * max 0 (g z).re := fun z hz ↦
    poissonKernel_mul_le hrR hw (by rwa [mem_sphere_zero_iff_norm, hRabs] at hz) _
  have hle := circleAverage_mono hCI₁ hCI₂ hmono
  rw [hpoisson] at hle
  have hconst : circleAverage (fun z ↦ ((R + r) / (R - r)) • max 0 (g z).re) 0 R
      = ((R + r) / (R - r)) • circleAverage (fun z ↦ max 0 (g z).re) 0 R :=
    circleAverage_fun_smul (E := ℝ) (𝕜 := ℝ) (a := (R + r) / (R - r))
      (f := fun z ↦ max 0 (g z).re) (c := 0) (R := R)
  simp only [smul_eq_mul] at hconst
  rwa [hconst] at hle

/-! ### The proximity function of an exponential -/

/-- The proximity function of `e^g` is the circle average of the positive part of `\Re g`. -/
theorem proximity_exp_eq_circleAverage (g : ℂ → ℂ) (R : ℝ) :
    proximity (fun z ↦ Complex.exp (g z)) ⊤ R = circleAverage (fun z ↦ max 0 (g z).re) 0 R := by
  rw [proximity_top]
  congr 1
  funext z
  simp [Real.posLog, Complex.norm_exp]

/-- `e^g` has no poles, so its logarithmic counting function at `⊤` vanishes. -/
theorem logCounting_exp_top (hg : Differentiable ℂ g) :
    logCounting (fun z ↦ Complex.exp (g z)) ⊤ = 0 := by
  have hana : AnalyticOnNhd ℂ (fun z ↦ Complex.exp (g z)) univ :=
    fun z _ ↦ (hg.analyticAt z).cexp'
  rw [logCounting_top,
    show (MeromorphicOn.divisor (fun z ↦ Complex.exp (g z)) univ)⁻ = 0 from
      negPart_eq_zero.2 (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hana), map_zero]

/-- The characteristic of `e^g` is its proximity function. -/
theorem characteristic_exp_eq_proximity (hg : Differentiable ℂ g) :
    characteristic (fun z ↦ Complex.exp (g z)) ⊤ = proximity (fun z ↦ Complex.exp (g z)) ⊤ := by
  unfold characteristic
  rw [logCounting_exp_top hg, add_zero]

/-- **The growth transfer.**  On the ball of radius `S`, the real part of `g` is at most three
times the characteristic of `e^g` at radius `2S`. -/
theorem re_le_characteristic (hg : Differentiable ℂ g) {S : ℝ} (hS : 0 < S) {z : ℂ}
    (hz : z ∈ ball (0 : ℂ) S) :
    (g z).re ≤ 3 * characteristic (fun w ↦ Complex.exp (g w)) ⊤ (2 * S) := by
  have hzS : ‖z‖ ≤ S := (mem_ball_zero_iff.1 hz).le
  have h := re_le_circleAverage_posPart hg (r := S) (R := 2 * S) (by linarith) hzS
  rw [characteristic_exp_eq_proximity hg, proximity_exp_eq_circleAverage]
  have hcoef : (2 * S + S) / (2 * S - S) = 3 := by
    field
  rwa [hcoef] at h


/-! ### Axiom footprint -/

/-- info: 'Shields.re_le_characteristic' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms re_le_characteristic

end Shields
