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

/-- **Holomorphy in the level, with its derivative.**  A contour integral whose dependence on the
level `c` is through `1/(f(t)-c)` alone is complex differentiable in `c` wherever `f - c` stays
off zero on the contour, with derivative the same integral against `(f-c)^{-2}`. -/
theorem hasDerivAt_circleIntegral_inv_sub {z₀ c₀ : ℂ} {R : ℝ} (hR : 0 < R)
    (f K : ℂ → ℂ) (hf : ContinuousOn f (sphere z₀ R)) (hK : ContinuousOn K (sphere z₀ R))
    (hne : ∀ t ∈ sphere z₀ R, f t - c₀ ≠ 0) :
    HasDerivAt (fun c => ∮ t in C(z₀, R), K t * (f t - c)⁻¹)
      (∮ t in C(z₀, R), K t * ((f t - c₀) ^ 2)⁻¹) c₀ := by
  -- a positive floor for `|f - c₀|` and a ceiling for `‖K‖` on the contour
  have hcpt : IsCompact (sphere z₀ R) := isCompact_sphere z₀ R
  have hnem : (sphere z₀ R).Nonempty := ⟨z₀ + (R : ℂ), by
    rw [mem_sphere_iff_norm, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hR]⟩
  obtain ⟨t₁, ht₁, hmin⟩ := hcpt.exists_isMinOn hnem
    ((hf.sub continuousOn_const).norm)
  set δ := ‖f t₁ - c₀‖ with hδdef
  have hδpos : 0 < δ := norm_pos_iff.mpr (hne t₁ ht₁)
  have hδle : ∀ t ∈ sphere z₀ R, δ ≤ ‖f t - c₀‖ := fun t ht => isMinOn_iff.mp hmin t ht
  obtain ⟨t₂, ht₂, hmax⟩ := hcpt.exists_isMaxOn hnem hK.norm
  set M := ‖K t₂‖ with hMdef
  have hM0 : 0 ≤ M := norm_nonneg _
  have hMle : ∀ t ∈ sphere z₀ R, ‖K t‖ ≤ M := fun t ht => isMaxOn_iff.mp hmax t ht
  -- on the ball of radius `δ/2` the shifted denominator is still bounded away from zero
  have hden : ∀ c : ℂ, ‖c - c₀‖ < δ / 2 → ∀ t ∈ sphere z₀ R, δ / 2 ≤ ‖f t - c‖ := by
    intro c hc t ht
    have h1 : ‖f t - c₀‖ - ‖c - c₀‖ ≤ ‖(f t - c₀) - (c - c₀)‖ := norm_sub_norm_le _ _
    have h2 : (f t - c₀) - (c - c₀) = f t - c := by ring
    rw [h2] at h1
    linarith [hδle t ht]
  have hdenne : ∀ c : ℂ, ‖c - c₀‖ < δ / 2 → ∀ t ∈ sphere z₀ R, f t - c ≠ 0 := by
    intro c hc t ht h0
    have := hden c hc t ht
    rw [h0, norm_zero] at this
    linarith
  -- integrability of every integrand that appears
  have hint : ∀ c : ℂ, ‖c - c₀‖ < δ / 2 →
      CircleIntegrable (fun t => K t * (f t - c)⁻¹) z₀ R := by
    intro c hc
    refine ContinuousOn.circleIntegrable hR.le (hK.mul ?_)
    exact (hf.sub continuousOn_const).inv₀ (hdenne c hc)
  have hint₂ : CircleIntegrable (fun t => K t * ((f t - c₀) ^ 2)⁻¹) z₀ R := by
    refine ContinuousOn.circleIntegrable hR.le (hK.mul ?_)
    exact ((hf.sub continuousOn_const).pow 2).inv₀ fun t ht => pow_ne_zero 2 (hne t ht)
  -- the slope, minus the answer, is `(c - c₀)` times a bounded integral
  set Φ : ℂ → ℂ := fun c => ∮ t in C(z₀, R), K t * (f t - c)⁻¹ with hΦ
  set A : ℂ := ∮ t in C(z₀, R), K t * ((f t - c₀) ^ 2)⁻¹ with hA
  set B : ℝ := 2 * π * R * (2 * M / δ ^ 3) with hB
  have hc₀ : ‖c₀ - c₀‖ < δ / 2 := by simpa using hδpos
  have hcomb : ∀ c : ℂ, c ≠ c₀ → ‖c - c₀‖ < δ / 2 →
      Φ c - Φ c₀ - (c - c₀) * A
        = ∮ t in C(z₀, R), ((c - c₀) * ((c - c₀) * (K t * ((f t - c) * (f t - c₀) ^ 2)⁻¹))) := by
    intro c hcne hc
    have hI1 := hint c hc
    have hI0 := hint c₀ hc₀
    have hIs : CircleIntegrable (fun t => (c - c₀) * (K t * ((f t - c₀) ^ 2)⁻¹)) z₀ R := by
      simpa [smul_eq_mul] using hint₂.const_fun_smul (a := c - c₀)
    calc Φ c - Φ c₀ - (c - c₀) * A
        = (∮ t in C(z₀, R), (K t * (f t - c)⁻¹ - K t * (f t - c₀)⁻¹))
            - ∮ t in C(z₀, R), (c - c₀) * (K t * ((f t - c₀) ^ 2)⁻¹) := by
          rw [circleIntegral.integral_sub hI1 hI0, circleIntegral.integral_const_mul, hΦ, hA]
      _ = ∮ t in C(z₀, R), ((K t * (f t - c)⁻¹ - K t * (f t - c₀)⁻¹)
            - (c - c₀) * (K t * ((f t - c₀) ^ 2)⁻¹)) :=
          (circleIntegral.integral_sub (hI1.fun_sub hI0) hIs).symm
      _ = ∮ t in C(z₀, R), ((c - c₀) * ((c - c₀) * (K t * ((f t - c) * (f t - c₀) ^ 2)⁻¹))) := by
          exact circleIntegral.integral_congr hR.le fun t ht =>
            resolvent_remainder_eq (hdenne c hc t ht) (hne t ht)
  have hbound : ∀ c : ℂ, c ≠ c₀ → ‖c - c₀‖ < δ / 2 →
      ‖slope Φ c₀ c - A‖ ≤ ‖c - c₀‖ * B := by
    intro c hcne hc
    have hsub : c - c₀ ≠ 0 := sub_ne_zero.mpr hcne
    have hpt : ∀ t ∈ sphere z₀ R,
        ‖(c - c₀) * ((c - c₀) * (K t * ((f t - c) * (f t - c₀) ^ 2)⁻¹))‖
          ≤ ‖c - c₀‖ * (‖c - c₀‖ * (2 * M / δ ^ 3)) := by
      intro t ht
      have h1 : δ / 2 ≤ ‖f t - c‖ := hden c hc t ht
      have h2 : δ ≤ ‖f t - c₀‖ := hδle t ht
      have h3 : ‖K t‖ ≤ M := hMle t ht
      have hquot : ‖K t‖ / (‖f t - c‖ * ‖f t - c₀‖ ^ 2) ≤ 2 * M / δ ^ 3 :=
        norm_div_mul_sq_le hδpos h1 h2 h3
      rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_mul, norm_pow]
      rw [show ‖K t‖ * (‖f t - c‖ * ‖f t - c₀‖ ^ 2)⁻¹
          = ‖K t‖ / (‖f t - c‖ * ‖f t - c₀‖ ^ 2) from (div_eq_mul_inv _ _).symm]
      gcongr
    have hnorm := circleIntegral.norm_integral_le_of_norm_le_const hR.le hpt
    have hslope : slope Φ c₀ c - A = (c - c₀)⁻¹ * (Φ c - Φ c₀ - (c - c₀) * A) := by
      rw [slope_def_field]
      field_simp
    rw [hslope, hcomb c hcne hc, norm_mul, norm_inv, hB]
    rw [inv_mul_le_iff₀ (by positivity)]
    calc ‖∮ t in C(z₀, R), ((c - c₀) * ((c - c₀) * (K t * ((f t - c) * (f t - c₀) ^ 2)⁻¹)))‖
        ≤ 2 * π * R * (‖c - c₀‖ * (‖c - c₀‖ * (2 * M / δ ^ 3))) := hnorm
      _ = ‖c - c₀‖ * (‖c - c₀‖ * (2 * π * R * (2 * M / δ ^ 3))) := by ring
  rw [hasDerivAt_iff_tendsto_slope]
  have hzero : Tendsto (fun c : ℂ => slope Φ c₀ c - A) (𝓝[≠] c₀) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun c : ℂ => ‖c - c₀‖ * B) ?_ ?_
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Metric.ball_mem_nhds c₀ (show (0 : ℝ) < δ / 2 by linarith))]
        with c hc1 hc2
      refine hbound c hc1 ?_
      rw [← Complex.dist_eq]
      exact Metric.mem_ball.mp hc2
    · have hcont : Continuous fun c : ℂ => ‖c - c₀‖ := by fun_prop
      have h1 : Tendsto (fun c : ℂ => ‖c - c₀‖) (𝓝[≠] c₀) (𝓝 0) := by
        have h2 := (hcont.tendsto c₀).mono_left (nhdsWithin_le_nhds (s := ({c₀}ᶜ : Set ℂ)))
        simpa using h2
      simpa using h1.mul_const B
  have := hzero.add_const A
  simpa using this

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

end Shields
