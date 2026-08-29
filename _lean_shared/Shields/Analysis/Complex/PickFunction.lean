/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed

/-!
# The residue of a Pick function at a real point

A *Pick* (or *Herglotz*, or *Nevanlinna*) function maps the open upper half-plane into its
closure.  Mathlib carries no such class: its `Nevanlinna` files are value-distribution theory,
a different subject.  This supplies the one local fact about them that needs no representation
theorem.

## Main statements

* `Shields.residue_im_eq_zero_and_re_nonpos`: a function with nonnegative imaginary part on the
  open upper half-plane has a **real and nonpositive** residue at a real point.  The usual
  reference for this is Donoghue, *Monotone Matrix Functions and Analytic Continuation*, Ch. II,
  p. 26, where it is read off the canonical representation; the proof here is local and uses no
  representation theorem, only the half-plane bound and the existence of the limit.
* `Shields.residue_ray_ineq`: the one inequality that hypothesis yields, one direction at a time
  -- `0 ≤ Im c · cos θ - Re c · sin θ` for `θ ∈ (0, π)`.  Everything after it is real analysis on
  a closed condition, with no complex function in sight.
* `Shields.tendsto_ray_nhdsWithin_ne` and `Shields.im_ray`: the ray `r ↦ x₀ + r e^{iθ}` stays in
  the open upper half-plane and reaches `x₀` from off it.

## Implementation notes

The hypothesis is stated as a limit of `(z - x₀) · R z` along `𝓝[≠] x₀` rather than as a pole
of a meromorphic function, so nothing about analyticity, order, or a local factorization is
assumed.

## Tags

Pick function, Herglotz, Nevanlinna, residue, upper half-plane
-/

open Filter Topology Set

namespace Shields

/-- The imaginary part of a point on the ray of direction `θ` through the real point `x₀`. -/
theorem im_ray (x₀ θ r : ℝ) :
    (((x₀ : ℝ) : ℂ) + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im = r * Real.sin θ := by
  simp [Complex.add_im, Complex.mul_im]

/-- **The ray reaches `x₀` from inside the upper half-plane.**  For a direction
`θ ∈ (0, π)` the points `x₀ + r e^{iθ}` have positive imaginary part at every `r > 0`, so
they are where the Pick hypothesis applies, and they converge to `x₀` without ever equaling
it. -/
theorem tendsto_ray_nhdsWithin_ne {x₀ θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    Tendsto (fun r : ℝ => ((x₀ : ℝ) : ℂ) + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))
      (𝓝[>] (0 : ℝ)) (𝓝[≠] ((x₀ : ℝ) : ℂ)) := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
  · have hcts : Continuous
        (fun r : ℝ => ((x₀ : ℝ) : ℂ) + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) :=
      continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
    simpa using (hcts.tendsto 0).mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ)))
  · filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpos : (0 : ℝ) < r := hr
    simp only [mem_compl_iff, mem_singleton_iff]
    intro hreal
    have hzero : (((x₀ : ℝ) : ℂ) + (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im = 0 := by
      rw [hreal, Complex.ofReal_im]
    rw [im_ray] at hzero
    have := mul_pos hrpos hsin
    linarith

/-- **The directional inequality behind the residue sign.**  Approaching `x₀` along the ray of
direction `θ ∈ (0, π)`, the Pick bound `0 ≤ Im R` survives the limit as

\[
  0 \le \operatorname{Im} c \cdot \cos\theta - \operatorname{Re} c \cdot \sin\theta ,
\]

because `r · R(x₀ + r e^{iθ})` has nonnegative imaginary part at every `r > 0` and converges to
`c / e^{iθ}`.  This is the whole use made of the half-plane hypothesis; the sign of the residue is
then a statement about which `c` satisfy this for every `θ`. -/
theorem residue_ray_ineq {R : ℂ → ℂ} {x₀ : ℝ} {c : ℂ}
    (hpick : ∀ w : ℂ, 0 < w.im → 0 ≤ (R w).im)
    (hc : Tendsto (fun w => (w - ((x₀ : ℝ) : ℂ)) * R w) (𝓝[≠] ((x₀ : ℝ) : ℂ)) (𝓝 c))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    0 ≤ c.im * Real.cos θ - c.re * Real.sin θ := by
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  set u : ℂ := Complex.exp ((θ : ℂ) * Complex.I) with hu
  have hunorm : Complex.normSq u = 1 := by
    rw [Complex.normSq_eq_norm_sq, hu, Complex.norm_exp_ofReal_mul_I, one_pow]
  have hune : u ≠ 0 := Complex.exp_ne_zero _
  -- along the ray, `r · R` has nonnegative imaginary part
  have hnonneg : ∀ᶠ r : ℝ in 𝓝[>] (0 : ℝ),
      0 ≤ ((r : ℂ) * R (((x₀ : ℝ) : ℂ) + (r : ℂ) * u)).im := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    have hrpos : (0 : ℝ) < r := hr
    have hupper : 0 < (((x₀ : ℝ) : ℂ) + (r : ℂ) * u).im := by
      rw [hu, im_ray]; exact mul_pos hrpos hsin
    have hsplit : ((r : ℂ) * R (((x₀ : ℝ) : ℂ) + (r : ℂ) * u)).im
        = r * (R (((x₀ : ℝ) : ℂ) + (r : ℂ) * u)).im := by
      simp [Complex.mul_im]
    rw [hsplit]
    exact mul_nonneg hrpos.le (hpick _ hupper)
  -- and converges to `c / u`, since `(x₀ + r u) - x₀ = r u`
  have hlimit : Tendsto (fun r : ℝ => (r : ℂ) * R (((x₀ : ℝ) : ℂ) + (r : ℂ) * u))
      (𝓝[>] (0 : ℝ)) (𝓝 (c / u)) := by
    refine Filter.Tendsto.congr (fun r => ?_)
      ((hc.comp (hu ▸ tendsto_ray_nhdsWithin_ne (x₀ := x₀) hθ)).div_const u)
    simp only [Function.comp_apply, add_sub_cancel_left]
    field_simp
  have him : (0 : ℝ) ≤ (c / u).im :=
    ge_of_tendsto ((Complex.continuous_im.tendsto _).comp hlimit) hnonneg
  rw [Complex.div_im, hu, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    ← hu, hunorm] at him
  simpa using him

/-- **The sign of the residue of a Pick function at a real point.**  A function with
nonnegative imaginary part on the open upper half-plane has a real and nonpositive residue at
a real point: if `(z - x₀) R(z) → c` as `z → x₀` off `x₀`, then `Im c = 0` and `Re c ≤ 0`.

`Shields.residue_ray_ineq` supplies `0 ≤ Im c · cos θ - Re c · sin θ` on the open interval
`(0, π)`; the inequality is closed, so it extends to the endpoints, and `θ = 0` and `θ = π`
bracket `Im c` between `0` and `0` while `θ = π/2` gives `Re c ≤ 0`.

No analyticity is assumed -- only the half-plane bound and the existence of the limit -- so
this applies to any function with a simple pole at a real point, meromorphic or not. -/
theorem residue_im_eq_zero_and_re_nonpos {R : ℂ → ℂ} {x₀ : ℝ} {c : ℂ}
    (hpick : ∀ w : ℂ, 0 < w.im → 0 ≤ (R w).im)
    (hc : Tendsto (fun w => (w - ((x₀ : ℝ) : ℂ)) * R w) (𝓝[≠] ((x₀ : ℝ) : ℂ)) (𝓝 c)) :
    c.im = 0 ∧ c.re ≤ 0 := by
  have hclosed : IsClosed {θ : ℝ | 0 ≤ c.im * Real.cos θ - c.re * Real.sin θ} :=
    isClosed_le continuous_const
      ((continuous_const.mul Real.continuous_cos).sub (continuous_const.mul Real.continuous_sin))
  have hIcc : Icc (0 : ℝ) Real.pi ⊆ {θ : ℝ | 0 ≤ c.im * Real.cos θ - c.re * Real.sin θ} := by
    rw [← closure_Ioo (Ne.symm Real.pi_ne_zero)]
    exact closure_minimal (fun θ hθ => residue_ray_ineq hpick hc hθ) hclosed
  have hzero : 0 ≤ c.im * Real.cos 0 - c.re * Real.sin 0 :=
    hIcc (left_mem_Icc.mpr Real.pi_pos.le)
  have hpi : 0 ≤ c.im * Real.cos Real.pi - c.re * Real.sin Real.pi :=
    hIcc (right_mem_Icc.mpr Real.pi_pos.le)
  have hhalf : 0 ≤ c.im * Real.cos (Real.pi / 2) - c.re * Real.sin (Real.pi / 2) :=
    residue_ray_ineq hpick hc ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
  rw [Real.cos_zero, Real.sin_zero] at hzero
  rw [Real.cos_pi, Real.sin_pi] at hpi
  rw [Real.cos_pi_div_two, Real.sin_pi_div_two] at hhalf
  exact ⟨by linarith, by linarith⟩


/-! ### Axiom footprint -/

/-- info: 'Shields.residue_im_eq_zero_and_re_nonpos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms residue_im_eq_zero_and_re_nonpos

end Shields
