/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# A power series representing an entire function near the origin represents it everywhere

The disc of convergence of the Taylor series of an analytic function reaches the nearest
singularity, so a series known to converge only on a small ball around the origin converges on the
whole plane as soon as the function it represents there is entire.  This is the step that turns a
*formal* reciprocal --- a power series produced by inverting a convolution, whose convergence is
known only from a coefficient bound --- into a genuine expansion of the reciprocal function.

`Shields.hasSum_of_entire_of_hasSum_ball` is that statement.  Mathlib has each ingredient
(`FormalMultilinearSeries.ofScalars`, `FormalMultilinearSeries.hasFPowerSeriesOnBall`,
`DifferentiableOn.hasFPowerSeriesOnBall`, `HasFPowerSeriesAt.eq_formalMultilinearSeries`) but not
the scalar-series conclusion assembled from them.

## Main results

* `Shields.le_radius_ofScalars` -- a coefficient bound `‖a n‖ r^n ≤ C` is a radius bound.  This
  is the only use the argument makes of the hypothesis.
* `Shields.hasFPowerSeriesAt_ofScalars` -- a scalar series summing to `F` on that ball is a power
  series for `F` at the origin.  Nothing about `F` off the ball is used, which is what makes it
  the right half to state separately.
* `Shields.hasSum_of_entire_of_hasSum_ball` -- the conclusion: with `F` entire, its Cauchy series
  on any larger ball is also a power series for `F` at the origin, uniqueness identifies the two,
  and the sum is valid at every point.

Sorry-free.
-/

open Filter Metric Set
open scoped Topology NNReal ENNReal

namespace Shields

/-- Membership in an extended-radius ball from an `ℝ≥0` bound: the bridge between `‖y‖₊ < s`
and `‖y‖ₑ < ρ` when `s ≤ ρ`. -/
theorem mem_eball_zero_of_nnnorm_lt {y : ℂ} {s : ℝ≥0} {ρ : ℝ≥0∞}
    (hy : ‖y‖₊ < s) (hs : (s : ℝ≥0∞) ≤ ρ) : y ∈ Metric.eball (0 : ℂ) ρ := by
  rw [mem_eball_zero_iff]
  calc ‖y‖ₑ = ((‖y‖₊ : ℝ≥0) : ℝ≥0∞) := rfl
    _ < ((s : ℝ≥0) : ℝ≥0∞) := by exact_mod_cast hy
    _ ≤ ρ := hs

/-- Evaluating `FormalMultilinearSeries.ofScalars` on the diagonal returns the scalar monomial. -/
theorem ofScalars_apply_diag (a : ℕ → ℂ) (y : ℂ) (n : ℕ) :
    (FormalMultilinearSeries.ofScalars ℂ a) n (fun _ => y) = a n * y ^ n := by
  rw [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

/-- **A coefficient bound is a radius bound.**  If `‖a n‖ r^n ≤ C` for every `n`, the scalar
series `∑ a n z^n` converges on the open ball of radius `r`.  This is the only use made of the
bound, and it is typically the geometric estimate a recursion already supplies. -/
theorem le_radius_ofScalars {a : ℕ → ℂ} {r : ℝ≥0} {C : ℝ}
    (hbd : ∀ n, ‖a n‖ * (r : ℝ) ^ n ≤ C) :
    (r : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ a).radius := by
  refine FormalMultilinearSeries.le_radius_of_bound _ C fun n => ?_
  rw [FormalMultilinearSeries.ofScalars_norm]
  exact hbd n

/-- **A scalar series summing to `F` on a ball is a power series for `F` at the origin.**  The
series and `F` agree on a neighborhood of `0`, so the series' own sum -- which is a power series
there by `le_radius_ofScalars` -- may be transported to `F`.  Nothing about `F` off the ball is
used. -/
theorem hasFPowerSeriesAt_ofScalars {a : ℕ → ℂ} {F : ℂ → ℂ} {r : ℝ≥0} (hr : 0 < r)
    {C : ℝ} (hbd : ∀ n, ‖a n‖ * (r : ℝ) ^ n ≤ C)
    (ha : ∀ z : ℂ, ‖z‖ < (r : ℝ) → HasSum (fun n => a n * z ^ n) (F z)) :
    HasFPowerSeriesAt F (FormalMultilinearSeries.ofScalars ℂ a) 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ a with hp
  have hrad : (r : ℝ≥0∞) ≤ p.radius := le_radius_ofScalars hbd
  have hball : HasFPowerSeriesOnBall p.sum p 0 p.radius :=
    p.hasFPowerSeriesOnBall (lt_of_lt_of_le (by exact_mod_cast hr) hrad)
  refine hball.hasFPowerSeriesAt.congr ?_
  filter_upwards [ball_mem_nhds (0 : ℂ) (show (0 : ℝ) < r by exact_mod_cast hr)] with y hy
  have hy' : ‖y‖ < (r : ℝ) := by simpa [mem_ball_zero_iff] using hy
  have hsum_p : HasSum (fun n => p n fun _ => y) (p.sum (0 + y)) :=
    hball.hasSum (mem_eball_zero_of_nnnorm_lt (by exact_mod_cast hy' : ‖y‖₊ < r) hrad)
  rw [zero_add] at hsum_p
  exact hsum_p.unique (by simpa only [hp, ofScalars_apply_diag] using ha y hy')

/-- **A scalar power series converging to an entire function near the origin converges to it
everywhere.**

The series is a power series for `F` at the origin (`Shields.hasFPowerSeriesAt_ofScalars`), and
so is the Cauchy series of `F` on the ball of radius `‖z‖ + 1`, which exists because `F` is
entire.  Uniqueness of the power series at a point identifies the two, and the Cauchy series
converges at `z` because `z` lies in that ball. -/
theorem hasSum_of_entire_of_hasSum_ball {a : ℕ → ℂ} {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {r : ℝ≥0} (hr : 0 < r) {C : ℝ} (hbd : ∀ n, ‖a n‖ * (r : ℝ) ^ n ≤ C)
    (ha : ∀ z : ℂ, ‖z‖ < (r : ℝ) → HasSum (fun n => a n * z ^ n) (F z))
    (z : ℂ) : HasSum (fun n => a n * z ^ n) (F z) := by
  set R : ℝ≥0 := ⟨‖z‖ + 1, by positivity⟩ with hR
  have hRcoe : ((R : ℝ≥0) : ℝ) = ‖z‖ + 1 := rfl
  have hR0 : 0 < R := by rw [← NNReal.coe_pos, hRcoe]; positivity
  have hcauchy : HasFPowerSeriesOnBall F (cauchyPowerSeries F 0 R) 0 R :=
    hF.differentiableOn.hasFPowerSeriesOnBall hR0
  rw [hcauchy.hasFPowerSeriesAt.eq_formalMultilinearSeries
    (hasFPowerSeriesAt_ofScalars hr hbd ha)] at hcauchy
  have hzR : ‖z‖₊ < R := by rw [← NNReal.coe_lt_coe, hRcoe, coe_nnnorm]; linarith
  simpa only [ofScalars_apply_diag, zero_add] using
    hcauchy.hasSum (mem_eball_zero_of_nnnorm_lt hzR le_rfl)

end Shields
