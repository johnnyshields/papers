/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Order.Compact

/-!
# Holomorphy of a contour integral in a level parameter

A contour integral whose dependence on a parameter `c` is through a resolvent `1/(f(t) - c)`
alone is complex differentiable in `c` wherever `f - c` stays off zero on the contour, and the
derivative is the same integral against `(f - c)^{-2}`.

## Main results

* `Shields.resolvent_remainder_eq`: the pointwise identity the whole argument rests on.
* `Shields.norm_div_mul_sq_le`: the pointwise estimate that turns it into `O(|c - c₀|)`.
* `Shields.circleIntegral_resolvent_sub_eq`: the difference quotient as a contour integral.
* `Shields.hasDerivAt_of_norm_slope_sub_le`: a candidate derivative confirmed by a linear bound
  on the slope.
* `Shields.hasDerivAt_circleIntegral_inv_sub`: the derivative in the level.
* `Shields.differentiableAt_circleIntegral_inv_sub`: holomorphy in the level.
* `Shields.hasDerivAt_circleIntegral_powerSum`: the specialization with the weight `g^\ell f'`,
  which by the argument principle is the `\ell`-th power sum of the solutions of `f(t) = c`
  enclosed by the contour.

## Implementation notes

**No differentiation under the integral sign is used.**  The level enters only through the
resolvent, and

\[ \frac{1}{f(t)-c} - \frac{1}{f(t)-c_0} = \frac{c-c_0}{(f(t)-c)(f(t)-c_0)}, \]

so the difference quotient is itself a contour integral.  Subtracting the candidate derivative
leaves one more factor of `c - c_0`, and the contour is compact, so the remainder is
`O(|c - c_0|)` by the elementary length-times-supremum bound.  The estimate is explicit: with
`\delta = \min_{\partial}|f - c_0|` and `\|K\| \le M` on the contour, the error at
`|c - c_0| < \delta/2` is at most `|c-c_0| \cdot 2\pi R \cdot 2M/\delta^3`.

Consequently the hypotheses ask only for continuity of `f` and of the weight on the contour;
neither is required to be analytic, or even defined, anywhere else.

## Tags

contour integral, circle integral, resolvent, holomorphic parameter, level set, power sum
-/

open Complex Filter Metric Set Topology

open scoped Real

namespace Shields

/-! ### The two pointwise facts

The whole level derivative rests on an algebraic identity and an estimate, both at a single point
of the contour.  Neither mentions an integral. -/

/-- **The resolvent's first-order remainder carries a square.**  Subtracting from the resolvent
difference the candidate derivative `(c - c₀)/(f - c₀)^2` leaves `(c - c₀)^2` over the product of
the three denominators.  That extra factor is why no differentiation under the integral sign is
needed: the remainder is `O(|c - c₀|^2)` before any integration. -/
theorem resolvent_remainder_eq {w c c₀ K : ℂ} (h : w - c ≠ 0) (h₀ : w - c₀ ≠ 0) :
    K * (w - c)⁻¹ - K * (w - c₀)⁻¹ - (c - c₀) * (K * ((w - c₀) ^ 2)⁻¹)
      = (c - c₀) * ((c - c₀) * (K * ((w - c) * (w - c₀) ^ 2)⁻¹)) := by
  field

/-- **The remainder's integrand against the contour's floor and ceiling.**  With `δ` a lower bound
for `‖v‖` and `δ/2` one for `‖u‖`, and `M` an upper bound for `‖K‖`, the quotient is at most
`2M/δ^3` -- the constant that appears in the final estimate. -/
theorem norm_div_mul_sq_le {δ M : ℝ} (hδ : 0 < δ) {K u v : ℂ}
    (hu : δ / 2 ≤ ‖u‖) (hv : δ ≤ ‖v‖) (hK : ‖K‖ ≤ M) :
    ‖K‖ / (‖u‖ * ‖v‖ ^ 2) ≤ 2 * M / δ ^ 3 := by
  have hd1 : 0 < ‖u‖ := by linarith
  have hd2 : 0 < ‖v‖ := by linarith
  have hM0 : 0 ≤ M := le_trans (norm_nonneg K) hK
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hsq : δ ^ 2 ≤ ‖v‖ ^ 2 := pow_le_pow_left₀ hδ.le hv 2
  have hprod : δ / 2 * δ ^ 2 ≤ ‖u‖ * ‖v‖ ^ 2 :=
    mul_le_mul hu hsq (by positivity) hd1.le
  have hscale : 2 * M * (δ / 2 * δ ^ 2) ≤ 2 * M * (‖u‖ * ‖v‖ ^ 2) :=
    mul_le_mul_of_nonneg_left hprod (by linarith)
  have hgap : 0 ≤ (M - ‖K‖) * δ ^ 3 := mul_nonneg (sub_nonneg.mpr hK) (by positivity)
  nlinarith [hscale, hgap]

/-! ### The level derivative -/

/-- **A candidate derivative confirmed by a linear bound on the slope.**  Where the difference
quotient of `Φ` at `c₀` stays within `‖c - c₀‖ B` of `A`, the slope tends to `A` and `A` is the
derivative.  Nothing here is special to a contour integral; it is the endgame of the estimate
below. -/
theorem hasDerivAt_of_norm_slope_sub_le {Φ : ℂ → ℂ} {A c₀ : ℂ} {B r : ℝ} (hr : 0 < r)
    (h : ∀ c, c ≠ c₀ → ‖c - c₀‖ < r → ‖slope Φ c₀ c - A‖ ≤ ‖c - c₀‖ * B) :
    HasDerivAt Φ A c₀ := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hzero : Tendsto (fun c : ℂ => slope Φ c₀ c - A) (𝓝[≠] c₀) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun c : ℂ => ‖c - c₀‖ * B) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds c₀ hr)] with c hc1 hc2
      exact h c hc1 (by rw [← Complex.dist_eq]; exact Metric.mem_ball.mp hc2)
    · simpa using
        ((tendsto_norm_sub_self_nhdsNE c₀).mono_right nhdsWithin_le_nhds).mul_const B
  simpa using hzero.add_const A

/-- **The difference quotient is itself a contour integral.**  Subtracting the candidate
derivative from the difference of the two resolvent integrals leaves `(c - c₀)^2` times the
integral of the three-denominator integrand, by `resolvent_remainder_eq` under the integral. -/
theorem circleIntegral_resolvent_sub_eq {z₀ c₀ c : ℂ} {R : ℝ} (hR : 0 ≤ R) {f K : ℂ → ℂ}
    (hI : CircleIntegrable (fun t => K t * (f t - c)⁻¹) z₀ R)
    (hI₀ : CircleIntegrable (fun t => K t * (f t - c₀)⁻¹) z₀ R)
    (hI₂ : CircleIntegrable (fun t => K t * ((f t - c₀) ^ 2)⁻¹) z₀ R)
    (hc : ∀ t ∈ sphere z₀ R, f t - c ≠ 0) (hc₀ : ∀ t ∈ sphere z₀ R, f t - c₀ ≠ 0) :
    (∮ t in C(z₀, R), K t * (f t - c)⁻¹) - (∮ t in C(z₀, R), K t * (f t - c₀)⁻¹)
        - (c - c₀) * ∮ t in C(z₀, R), K t * ((f t - c₀) ^ 2)⁻¹
      = ∮ t in C(z₀, R), (c - c₀) * ((c - c₀) * (K t * ((f t - c) * (f t - c₀) ^ 2)⁻¹)) := by
  have hIs : CircleIntegrable (fun t => (c - c₀) * (K t * ((f t - c₀) ^ 2)⁻¹)) z₀ R := by
    simpa [smul_eq_mul] using hI₂.const_fun_smul (a := c - c₀)
  rw [← circleIntegral.integral_const_mul, ← circleIntegral.integral_sub hI hI₀,
    ← circleIntegral.integral_sub (hI.fun_sub hI₀) hIs]
  exact circleIntegral.integral_congr hR fun t ht =>
    resolvent_remainder_eq (hc t ht) (hc₀ t ht)

/-- **Holomorphy in the level, with its derivative.**  A contour integral whose dependence on the
level `c` is through `1/(f(t)-c)` alone is complex differentiable in `c` wherever `f - c` stays
off zero on the contour, with derivative the same integral against `(f-c)^{-2}`. -/
theorem hasDerivAt_circleIntegral_inv_sub {z₀ c₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (f K : ℂ → ℂ) (hf : ContinuousOn f (sphere z₀ R)) (hK : ContinuousOn K (sphere z₀ R))
    (hne : ∀ t ∈ sphere z₀ R, f t - c₀ ≠ 0) :
    HasDerivAt (fun c => ∮ t in C(z₀, R), K t * (f t - c)⁻¹)
      (∮ t in C(z₀, R), K t * ((f t - c₀) ^ 2)⁻¹) c₀ := by
  -- a positive floor for `|f - c₀|` and a ceiling for `‖K‖` on the contour
  obtain ⟨δ, hδpos, hδle⟩ : ∃ δ > 0, ∀ t ∈ sphere z₀ R, δ ≤ ‖f t - c₀‖ :=
    (isCompact_sphere z₀ R).exists_forall_le' ((hf.sub continuousOn_const).norm)
      fun t ht => norm_pos_iff.mpr (hne t ht)
  obtain ⟨M, hMle⟩ := (isCompact_sphere z₀ R).exists_bound_of_continuousOn hK
  -- on the ball of radius `δ/2` the shifted denominator is still bounded away from zero
  have hden : ∀ c : ℂ, ‖c - c₀‖ < δ / 2 → ∀ t ∈ sphere z₀ R, δ / 2 ≤ ‖f t - c‖ := by
    intro c hc t ht
    have h1 : ‖f t - c₀‖ - ‖c - c₀‖ ≤ ‖(f t - c₀) - (c - c₀)‖ := norm_sub_norm_le _ _
    rw [show (f t - c₀) - (c - c₀) = f t - c from by ring] at h1
    linarith [hδle t ht]
  have hdenne : ∀ c : ℂ, ‖c - c₀‖ < δ / 2 → ∀ t ∈ sphere z₀ R, f t - c ≠ 0 := fun c hc t ht =>
    norm_pos_iff.mp (lt_of_lt_of_le (by linarith) (hden c hc t ht))
  -- integrability of every integrand that appears
  have hint : ∀ c : ℂ, ‖c - c₀‖ < δ / 2 →
      CircleIntegrable (fun t => K t * (f t - c)⁻¹) z₀ R := fun c hc =>
    ContinuousOn.circleIntegrable hR.le
      (hK.mul ((hf.sub continuousOn_const).inv₀ (hdenne c hc)))
  have hint₂ : CircleIntegrable (fun t => K t * ((f t - c₀) ^ 2)⁻¹) z₀ R :=
    ContinuousOn.circleIntegrable hR.le
      (hK.mul (((hf.sub continuousOn_const).pow 2).inv₀ fun t ht => pow_ne_zero 2 (hne t ht)))
  have hc₀ : ‖c₀ - c₀‖ < δ / 2 := by simpa using hδpos
  -- the slope, minus the answer, is `(c - c₀)` times a bounded contour integral
  refine hasDerivAt_of_norm_slope_sub_le (r := δ / 2) (B := 2 * π * R * (2 * M / δ ^ 3))
    (by linarith) fun c hcne hc => ?_
  have hsub : c - c₀ ≠ 0 := sub_ne_zero.mpr hcne
  have hpt : ∀ t ∈ sphere z₀ R,
      ‖(c - c₀) * ((c - c₀) * (K t * ((f t - c) * (f t - c₀) ^ 2)⁻¹))‖
        ≤ ‖c - c₀‖ * (‖c - c₀‖ * (2 * M / δ ^ 3)) := by
    intro t ht
    have hquot : ‖K t‖ / (‖f t - c‖ * ‖f t - c₀‖ ^ 2) ≤ 2 * M / δ ^ 3 :=
      norm_div_mul_sq_le hδpos (hden c hc t ht) (hδle t ht) (hMle t ht)
    rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_mul, norm_pow, ← div_eq_mul_inv]
    gcongr
  have hnorm := circleIntegral.norm_integral_le_of_norm_le_const hR.le hpt
  have hslope : slope (fun c => ∮ t in C(z₀, R), K t * (f t - c)⁻¹) c₀ c
      - (∮ t in C(z₀, R), K t * ((f t - c₀) ^ 2)⁻¹)
      = (c - c₀)⁻¹ * ∮ t in C(z₀, R),
          (c - c₀) * ((c - c₀) * (K t * ((f t - c) * (f t - c₀) ^ 2)⁻¹)) := by
    rw [← circleIntegral_resolvent_sub_eq hR.le (hint c hc) (hint c₀ hc₀) hint₂ (hdenne c hc) hne,
      slope_def_field]
    field_simp
  rw [hslope, norm_mul, norm_inv, inv_mul_le_iff₀ (norm_pos_iff.mpr hsub)]
  exact hnorm.trans_eq (by ring)

/-- **Holomorphy in the level.** -/
theorem differentiableAt_circleIntegral_inv_sub {z₀ c₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (f K : ℂ → ℂ) (hf : ContinuousOn f (sphere z₀ R)) (hK : ContinuousOn K (sphere z₀ R))
    (hne : ∀ t ∈ sphere z₀ R, f t - c₀ ≠ 0) :
    DifferentiableAt ℂ (fun c => ∮ t in C(z₀, R), K t * (f t - c)⁻¹) c₀ :=
  (hasDerivAt_circleIntegral_inv_sub hR f K hf hK hne).differentiableAt

/-- **The power sums of a level set are holomorphic in the level.**  With the weight
`K = g^ℓ f'` the integral is, by the argument principle, `∑ g(t)^ℓ` over the solutions of
`f(t) = c` enclosed by the contour.  It is therefore holomorphic in `c` wherever `f - c` stays
off zero on the contour — no hypothesis on how the solutions themselves move, which is the
point: individually they are only Hölder-`1/2` where two of them collide. -/
theorem hasDerivAt_circleIntegral_powerSum {z₀ c₀ : ℂ} {R : ℝ} (hR : 0 < R) (ℓ : ℕ)
    (f g : ℂ → ℂ) (hf : ContinuousOn f (sphere z₀ R))
    (hf' : ContinuousOn (deriv f) (sphere z₀ R)) (hg : ContinuousOn g (sphere z₀ R))
    (hne : ∀ t ∈ sphere z₀ R, f t - c₀ ≠ 0) :
    HasDerivAt (fun c => ∮ t in C(z₀, R), (g t ^ ℓ * deriv f t) * (f t - c)⁻¹)
      (∮ t in C(z₀, R), (g t ^ ℓ * deriv f t) * ((f t - c₀) ^ 2)⁻¹) c₀ :=
  hasDerivAt_circleIntegral_inv_sub hR f _ hf ((hg.pow ℓ).mul hf') hne


/-! ### Axiom footprint -/

/-- info: 'Shields.differentiableAt_circleIntegral_inv_sub' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms differentiableAt_circleIntegral_inv_sub

/-- info: 'Shields.hasDerivAt_circleIntegral_powerSum' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms hasDerivAt_circleIntegral_powerSum

end Shields
