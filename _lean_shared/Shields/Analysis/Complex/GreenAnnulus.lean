/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.PolarLaplacian
import Mathlib.MeasureTheory.Integral.CircleAverage
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Green's identity on an annulus

Mathlib's divergence theorem is stated on a **box**, so the flux form of Green's identity on an
annulus is not available from it.
This module builds that identity instead from `PolarLaplacian`, where polar coordinates make the
annulus a rectangle without any change of variables having to be performed.

Three steps.

* **The angular second derivative integrates to zero** over a full turn.  The first angular
  derivative returns to its value, so the fundamental theorem of calculus leaves nothing.  What
  that says, once the second angular derivative is expanded, is
  `∫Du[e^{iθ}]dθ = r∫D²u[ie^{iθ},ie^{iθ}]dθ` — the cancellation the polar Laplacian's `r^{-1}∂_r`
  term performs, in integrated form.
* **The flux differentiates to the Laplacian's circle integral.**  Differentiation under the
  integral sign gives the circle integral a radial derivative, twice; the product rule on
  `r ↦ r∫Du[e^{iθ}]dθ` then contributes the radial average plus `r` times the second radial
  average, and by the previous step the first is `r` times the *angular* average.  The two second
  differentials add to the Laplacian, `{e^{iθ}, ie^{iθ}}` being orthonormal.
* **The fundamental theorem of calculus** turns that into the identity itself.

The flux is `2πr` times the radial derivative of the circle average, which is the form
`RieszPotential.circleFlux_rootPotential` computes for the root potential, and the form the
`(2π)^{-1}` of the Riesz identity comes from.

The hypothesis `0 < ε` is what keeps the origin — the one point where polar coordinates degenerate
— out of the region.  `u` is an arbitrary `C²` function on the plane.

## Main results

* `circleMap_eq_circleDir`, `circleDir_periodic` — the bridge to Mathlib's `circleMap`, and the
  turn.
* `integral_angular_second`, `integral_radial_eq_angular` — the angular part contributes nothing,
  and what that identity says about the two averages.
* `hasDerivAt_circleIntegral`, `hasDerivAt_radialIntegral` — differentiation under the integral
  sign, at both orders.
* `circleFlux`, `hasDerivAt_circleFlux` — the flux, and **its derivative is the Laplacian's circle
  integral**.
* `green_annulus` — **Green's identity on an annulus**, in flux form.
* `circleFlux_eq_deriv_circleAverage` — the flux is `2πr` times the circle average's radial
  derivative.
* `green_annulus_log` — **the same identity tested against `log r`**, which is the shape the Riesz
  identity consumes: integration by parts against the flux, where `log' r = 1/r` cancels the
  radius the flux carries and leaves the circle average's own derivative.

## Tags

green identity, annulus, flux, circle average, laplacian
-/

open scoped Real
open InnerProductSpace Complex Laplacian intervalIntegral Real

namespace Shields

variable {u : ℂ → ℝ}

/-! ### The bridge to `circleMap`, and periodicity -/

theorem circleMap_eq_circleDir (c : ℂ) (r θ : ℝ) :
    circleMap c r θ = c + (r : ℂ) * circleDir θ := rfl

theorem circleDir_periodic (θ : ℝ) : circleDir (2 * π + θ) = circleDir θ := by
  rw [circleDir, circleDir, Complex.ofReal_add, add_mul, Complex.exp_add,
    show ((2 * π : ℝ) : ℂ) * Complex.I = 2 * (π : ℂ) * Complex.I from by push_cast; ring,
    Complex.exp_two_pi_mul_I, one_mul]

/-! ### Regularity extracted from `C²` -/

theorem contDiff_two_differentiable (hu : ContDiff ℝ 2 u) : Differentiable ℝ u :=
  hu.differentiable (by norm_num)

theorem contDiff_two_differentiable_fderiv (hu : ContDiff ℝ 2 u) :
    Differentiable ℝ (fderiv ℝ u) :=
  (hu.fderiv_right (m := 1) le_rfl).differentiable (by norm_num)

theorem contDiff_two_continuous_fderiv (hu : ContDiff ℝ 2 u) : Continuous (fderiv ℝ u) :=
  (hu.fderiv_right (m := 1) le_rfl).continuous

theorem contDiff_two_continuous_fderiv2 (hu : ContDiff ℝ 2 u) :
    Continuous (fderiv ℝ (fderiv ℝ u)) :=
  ((hu.fderiv_right (m := 1) le_rfl).fderiv_right (m := 0) le_rfl).continuous

/-! ### The angular second derivative integrates to zero -/

/-- The first angular derivative, as a function of the angle. -/
noncomputable def angularDeriv (u : ℂ → ℝ) (c : ℂ) (r : ℝ) (θ : ℝ) : ℝ :=
  fderiv ℝ u (circleMap c r θ) ((r : ℂ) * (circleDir θ * Complex.I))

/-- The second angular derivative, as a function of the angle. -/
noncomputable def angularDeriv2 (u : ℂ → ℝ) (c : ℂ) (r : ℝ) (θ : ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ u) (circleMap c r θ) ((r : ℂ) * (circleDir θ * Complex.I))
      ((r : ℂ) * (circleDir θ * Complex.I))
    + fderiv ℝ u (circleMap c r θ) (-((r : ℂ) * circleDir θ))

theorem hasDerivAt_angularDeriv (hu : ContDiff ℝ 2 u) (c : ℂ) (r θ : ℝ) :
    HasDerivAt (angularDeriv u c r) (angularDeriv2 u c r θ) θ :=
  hasDerivAt_angular_fderiv (contDiff_two_differentiable_fderiv hu) c r θ

theorem continuous_angularDeriv2 (hu : ContDiff ℝ 2 u) (c : ℂ) (r : ℝ) :
    Continuous (angularDeriv2 u c r) := by
  have hpt : Continuous fun θ : ℝ => circleMap c r θ := continuous_circleMap c r
  have hdir : Continuous fun θ : ℝ => ((r : ℂ) * (circleDir θ * Complex.I)) := by
    refine continuous_const.mul (Continuous.mul ?_ continuous_const)
    exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  have hrad : Continuous fun θ : ℝ => (-((r : ℂ) * circleDir θ)) := by
    refine (continuous_const.mul ?_).neg
    exact Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
  refine Continuous.add ?_ ?_
  · exact ((contDiff_two_continuous_fderiv2 hu).comp hpt).clm_apply hdir |>.clm_apply hdir
  · exact ((contDiff_two_continuous_fderiv hu).comp hpt).clm_apply hrad

/-- **The angular second derivative integrates to zero over a full turn.**  The first angular
derivative returns to its value, so the fundamental theorem of calculus leaves nothing. -/
theorem integral_angular_second (hu : ContDiff ℝ 2 u) (c : ℂ) (r : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), angularDeriv2 u c r θ = 0 := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun θ _ => hasDerivAt_angularDeriv hu c r θ)
    ((continuous_angularDeriv2 hu c r).intervalIntegrable _ _)]
  have hper : angularDeriv u c r (2 * π) = angularDeriv u c r 0 := by
    rw [angularDeriv, angularDeriv, circleMap_eq_circleDir, circleMap_eq_circleDir,
      show (2 * π : ℝ) = 2 * π + 0 from by ring, circleDir_periodic]
  rw [hper, sub_self]

/-- The identity the previous result carries: the average of the radial differential is `r` times
the average of the angular second differential. -/
theorem integral_radial_eq_angular (hu : ContDiff ℝ 2 u) (c : ℂ) (r : ℝ) :
    ∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u (circleMap c r θ) (circleDir θ) * r
      = r ^ 2 * ∫ θ in (0 : ℝ)..(2 * π),
          fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ * Complex.I)
            (circleDir θ * Complex.I) := by
  have hsmul : ∀ z : ℂ, (r : ℂ) * z = (r : ℝ) • z := fun z => Complex.real_smul.symm
  have hpoint : ∀ θ : ℝ, angularDeriv2 u c r θ
      = r ^ 2 * fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ * Complex.I)
          (circleDir θ * Complex.I)
        - fderiv ℝ u (circleMap c r θ) (circleDir θ) * r := by
    intro θ
    rw [angularDeriv2]
    simp only [hsmul, ← smul_neg, map_smul, smul_apply, smul_eq_mul, map_neg]
    ring
  have hzero := integral_angular_second hu c r
  rw [intervalIntegral.integral_congr (g := fun θ => r ^ 2 *
      fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ * Complex.I)
        (circleDir θ * Complex.I)
      - fderiv ℝ u (circleMap c r θ) (circleDir θ) * r)
    (fun θ _ => hpoint θ)] at hzero
  have hint1 : IntervalIntegrable (fun θ : ℝ => r ^ 2 *
      fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ * Complex.I)
        (circleDir θ * Complex.I)) MeasureTheory.volume 0 (2 * π) := by
    refine Continuous.intervalIntegrable ?_ _ _
    have hdir : Continuous fun θ : ℝ => (circleDir θ * Complex.I) :=
      (Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)).mul
        continuous_const
    exact continuous_const.mul
      ((((contDiff_two_continuous_fderiv2 hu).comp (continuous_circleMap c r)).clm_apply
        hdir).clm_apply hdir)
  have hint2 : IntervalIntegrable
      (fun θ : ℝ => fderiv ℝ u (circleMap c r θ) (circleDir θ) * r)
      MeasureTheory.volume 0 (2 * π) := by
    refine Continuous.intervalIntegrable ?_ _ _
    have hdir : Continuous fun θ : ℝ => circleDir θ :=
      Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)
    exact (((contDiff_two_continuous_fderiv hu).comp
      (continuous_circleMap c r)).clm_apply hdir).mul continuous_const
  rw [intervalIntegral.integral_sub hint1 hint2, sub_eq_zero,
    intervalIntegral.integral_const_mul] at hzero
  exact hzero.symm

/-! ### Differentiating the circle average in the radius -/

theorem continuous_circleDir : Continuous circleDir :=
  Complex.continuous_exp.comp (Complex.continuous_ofReal.mul continuous_const)

theorem norm_circleMap_sub_center (c : ℂ) (x θ : ℝ) : ‖circleMap c x θ - c‖ = |x| := by
  rw [circleMap_eq_circleDir]
  simp [norm_circleDir]

theorem circleMap_mem_closedBall_of_mem_ball {c : ℂ} {r x : ℝ} (hx : x ∈ Metric.ball r 1) (θ : ℝ) :
    circleMap c x θ ∈ Metric.closedBall c (|r| + 1) := by
  rw [Metric.mem_closedBall, Complex.dist_eq, norm_circleMap_sub_center]
  have h1 : |x - r| < 1 := by simpa [Real.dist_eq] using hx
  obtain ⟨h2, h3⟩ := abs_lt.mp h1
  rw [abs_le]
  exact ⟨by linarith [neg_abs_le r], by linarith [le_abs_self r]⟩

/-- **The circle integral is differentiable in the radius, with the radial differential as
derivative.**  Differentiation under the integral sign: the parameter enters only through the
point, the derivative in the parameter is the differential along the ray, and it is bounded
uniformly by the supremum of `‖Du‖` on a compact disk. -/
theorem hasDerivAt_circleIntegral (hu : ContDiff ℝ 2 u) (c : ℂ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ θ in (0 : ℝ)..(2 * π), u (circleMap c s θ))
      (∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u (circleMap c r θ) (circleDir θ)) r := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c (|r| + 1)).exists_bound_of_continuousOn
    (contDiff_two_continuous_fderiv hu).continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun s θ => fderiv ℝ u (circleMap c s θ) (circleDir θ)) (bound := fun _ => C)
    (Metric.ball_mem_nhds r one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with x
    exact ((contDiff_two_differentiable hu).continuous.comp
      (continuous_circleMap c x)).aestronglyMeasurable
  · exact (((contDiff_two_differentiable hu).continuous.comp
      (continuous_circleMap c r)).intervalIntegrable _ _)
  · exact ((((contDiff_two_continuous_fderiv hu).comp
      (continuous_circleMap c r)).clm_apply continuous_circleDir)).aestronglyMeasurable
  · filter_upwards with θ _ x hx
    calc ‖fderiv ℝ u (circleMap c x θ) (circleDir θ)‖
        ≤ ‖fderiv ℝ u (circleMap c x θ)‖ * ‖circleDir θ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ u (circleMap c x θ)‖ := by rw [norm_circleDir, mul_one]
      _ ≤ C := hC _ (circleMap_mem_closedBall_of_mem_ball hx θ)
  · exact intervalIntegrable_const
  · filter_upwards with θ _ x _
    exact hasDerivAt_radial (contDiff_two_differentiable hu) c (circleDir θ) x

/-- The same, one order up: the radial differential's own integral differentiates to the second
radial differential. -/
theorem hasDerivAt_radialIntegral (hu : ContDiff ℝ 2 u) (c : ℂ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => ∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u (circleMap c s θ) (circleDir θ))
      (∫ θ in (0 : ℝ)..(2 * π),
        fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ) (circleDir θ)) r := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall c (|r| + 1)).exists_bound_of_continuousOn
    (f := fderiv ℝ (fderiv ℝ u)) (contDiff_two_continuous_fderiv2 hu).continuousOn
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F' := fun s θ => fderiv ℝ (fderiv ℝ u) (circleMap c s θ) (circleDir θ) (circleDir θ))
    (bound := fun _ => C) (Metric.ball_mem_nhds r one_pos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · filter_upwards with x
    exact (((contDiff_two_continuous_fderiv hu).comp
      (continuous_circleMap c x)).clm_apply continuous_circleDir).aestronglyMeasurable
  · exact ((((contDiff_two_continuous_fderiv hu).comp
      (continuous_circleMap c r)).clm_apply continuous_circleDir).intervalIntegrable _ _)
  · exact ((((contDiff_two_continuous_fderiv2 hu).comp
      (continuous_circleMap c r)).clm_apply continuous_circleDir).clm_apply
        continuous_circleDir).aestronglyMeasurable
  · filter_upwards with θ _ x hx
    calc ‖fderiv ℝ (fderiv ℝ u) (circleMap c x θ) (circleDir θ) (circleDir θ)‖
        ≤ ‖fderiv ℝ (fderiv ℝ u) (circleMap c x θ) (circleDir θ)‖ * ‖circleDir θ‖ :=
          ContinuousLinearMap.le_opNorm _ _
      _ ≤ (‖fderiv ℝ (fderiv ℝ u) (circleMap c x θ)‖ * ‖circleDir θ‖) * ‖circleDir θ‖ := by
          gcongr
          exact ContinuousLinearMap.le_opNorm _ _
      _ = ‖fderiv ℝ (fderiv ℝ u) (circleMap c x θ)‖ := by rw [norm_circleDir]; ring
      _ ≤ C := hC _ (circleMap_mem_closedBall_of_mem_ball hx θ)
  · exact intervalIntegrable_const
  · filter_upwards with θ _ x _
    exact hasDerivAt_radial_fderiv (contDiff_two_differentiable_fderiv hu) c (circleDir θ) x

/-! ### The flux, and Green's identity on an annulus -/

/-- The outward flux of `∇u` through the circle of radius `r`: `2π r` times the radial derivative
of the circle average. -/
noncomputable def circleFlux (u : ℂ → ℝ) (c : ℂ) (r : ℝ) : ℝ :=
  r * ∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u (circleMap c r θ) (circleDir θ)

/-- **The flux differentiates to the Laplacian's circle integral.**  The product rule contributes
the radial average plus `r` times the second radial average; the first is `r` times the angular
average by `integral_radial_eq_angular`, and the two second differentials add to the Laplacian. -/
theorem hasDerivAt_circleFlux (hu : ContDiff ℝ 2 u) (c : ℂ) {r : ℝ} (hr : r ≠ 0) :
    HasDerivAt (circleFlux u c) (r * ∫ θ in (0 : ℝ)..(2 * π), Δ u (circleMap c r θ)) r := by
  have hprod : HasDerivAt (circleFlux u c)
      ((∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u (circleMap c r θ) (circleDir θ))
        + r * ∫ θ in (0 : ℝ)..(2 * π),
            fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ) (circleDir θ)) r := by
    have h := (hasDerivAt_id r).mul (hasDerivAt_radialIntegral hu c r)
    simp only [id_eq, one_mul] at h
    exact h
  -- The angular average, recovered from `integral_radial_eq_angular` by canceling one `r`.
  have hang : (∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u (circleMap c r θ) (circleDir θ))
      = r * ∫ θ in (0 : ℝ)..(2 * π),
          fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ * Complex.I)
            (circleDir θ * Complex.I) := by
    have h := integral_radial_eq_angular hu c r
    rw [intervalIntegral.integral_mul_const] at h
    refine mul_right_cancel₀ hr ?_
    rw [h]
    ring
  -- The two second differentials add to the Laplacian, pointwise inside the integral.
  have hlap : (∫ θ in (0 : ℝ)..(2 * π), Δ u (circleMap c r θ))
      = (∫ θ in (0 : ℝ)..(2 * π),
          fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ) (circleDir θ))
        + ∫ θ in (0 : ℝ)..(2 * π),
            fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ * Complex.I)
              (circleDir θ * Complex.I) := by
    rw [← intervalIntegral.integral_add]
    · exact intervalIntegral.integral_congr fun θ _ => laplacian_apply_rotated u θ _
    · refine Continuous.intervalIntegrable ?_ _ _
      exact (((contDiff_two_continuous_fderiv2 hu).comp
        (continuous_circleMap c r)).clm_apply continuous_circleDir).clm_apply continuous_circleDir
    · refine Continuous.intervalIntegrable ?_ _ _
      have hdir : Continuous fun θ : ℝ => circleDir θ * Complex.I :=
        continuous_circleDir.mul continuous_const
      exact (((contDiff_two_continuous_fderiv2 hu).comp
        (continuous_circleMap c r)).clm_apply hdir).clm_apply hdir
  have heq : (∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u (circleMap c r θ) (circleDir θ))
      + r * (∫ θ in (0 : ℝ)..(2 * π),
          fderiv ℝ (fderiv ℝ u) (circleMap c r θ) (circleDir θ) (circleDir θ))
      = r * ∫ θ in (0 : ℝ)..(2 * π), Δ u (circleMap c r θ) := by
    rw [hang, hlap]
    ring
  rw [← heq]
  exact hprod

/-! ### Green's identity on an annulus -/

theorem continuous_laplacian (hu : ContDiff ℝ 2 u) : Continuous (Δ u) := by
  have h : Δ u = fun p => fderiv ℝ (fderiv ℝ u) p (circleDir 0) (circleDir 0)
      + fderiv ℝ (fderiv ℝ u) p (circleDir 0 * Complex.I) (circleDir 0 * Complex.I) :=
    funext fun p => laplacian_apply_rotated u 0 p
  rw [h]
  exact (((contDiff_two_continuous_fderiv2 hu).clm_apply continuous_const).clm_apply
    continuous_const).add
      (((contDiff_two_continuous_fderiv2 hu).clm_apply continuous_const).clm_apply
        continuous_const)

theorem continuous_circleMap_uncurry (c : ℂ) :
    Continuous fun p : ℝ × ℝ => circleMap c p.1 p.2 := by
  simp only [circleMap_eq_circleDir]
  exact continuous_const.add ((Complex.continuous_ofReal.comp continuous_fst).mul
    (continuous_circleDir.comp continuous_snd))

theorem continuous_laplacianIntegral (hu : ContDiff ℝ 2 u) (c : ℂ) :
    Continuous fun s : ℝ => ∫ θ in (0 : ℝ)..(2 * π), Δ u (circleMap c s θ) := by
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun s θ => Δ u (circleMap c s θ)) ?_ 0 (2 * π)
  exact (continuous_laplacian hu).comp (continuous_circleMap_uncurry c)

/-- **Green's identity on an annulus.**  The integral of the Laplacian over the annulus
`ε ≤ ‖z-c‖ ≤ R`, taken in polar form, is the net outward flux through its two boundary circles.

Mathlib's divergence theorem is stated on a box, so this is proved instead from the polar
Laplacian: the flux differentiates to the Laplacian's circle integral
(`hasDerivAt_circleFlux`), and the fundamental theorem of calculus does the rest.  The hypothesis
`0 < ε` is what keeps the origin — where polar coordinates degenerate — out of the region. -/
theorem green_annulus (hu : ContDiff ℝ 2 u) (c : ℂ) {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ s in ε..R, s * ∫ θ in (0 : ℝ)..(2 * π), Δ u (circleMap c s θ))
      = circleFlux u c R - circleFlux u c ε := by
  refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s hs => ?_) ?_
  · rw [Set.uIcc_of_le hεR] at hs
    exact hasDerivAt_circleFlux hu c (ne_of_gt (lt_of_lt_of_le hε hs.1))
  · exact (continuous_id.mul (continuous_laplacianIntegral hu c)).intervalIntegrable _ _

/-! ### The flux is the circle average's radial derivative -/

theorem hasDerivAt_circleAverage (hu : ContDiff ℝ 2 u) (c : ℂ) (r : ℝ) :
    HasDerivAt (fun s : ℝ => circleAverage u c s)
      ((2 * π)⁻¹ • ∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u (circleMap c r θ) (circleDir θ)) r :=
  (hasDerivAt_circleIntegral hu c r).const_smul ((2 * π)⁻¹ : ℝ)

/-- **The flux is `2πr` times the radial derivative of the circle average**, which is the form
`RieszPotential.circleFlux_rootPotential` computes for the root potential and the form the
`(2π)^{-1}` of the Riesz identity comes from. -/
theorem circleFlux_eq_deriv_circleAverage (hu : ContDiff ℝ 2 u) (c : ℂ) (r : ℝ) :
    circleFlux u c r = 2 * π * r * deriv (fun s : ℝ => circleAverage u c s) r := by
  rw [(hasDerivAt_circleAverage hu c r).deriv, circleFlux, smul_eq_mul]
  field_simp

/-! ### Green's identity against `log r` -/

theorem continuous_radialIntegral (hu : ContDiff ℝ 2 u) (c : ℂ) :
    Continuous fun s : ℝ => ∫ θ in (0 : ℝ)..(2 * π),
      fderiv ℝ u (circleMap c s θ) (circleDir θ) := by
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun s θ => fderiv ℝ u (circleMap c s θ) (circleDir θ)) ?_ 0 (2 * π)
  exact ((contDiff_two_continuous_fderiv hu).comp (continuous_circleMap_uncurry c)).clm_apply
    (continuous_circleDir.comp continuous_snd)

/-- The flux divided by the radius is `2π` times the circle average's derivative. -/
theorem radialIntegral_eq (hu : ContDiff ℝ 2 u) (c : ℂ) (r : ℝ) :
    (∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ u (circleMap c r θ) (circleDir θ))
      = 2 * π * deriv (fun s : ℝ => circleAverage u c s) r := by
  rw [(hasDerivAt_circleAverage hu c r).deriv, smul_eq_mul]
  field_simp

/-- **Green's identity on an annulus, tested against `log r`.**  This is the shape the Riesz
identity consumes: integrating the Laplacian against the logarithmic kernel over an annulus leaves
the flux's boundary terms weighted by `log`, minus `2π` times the change in the circle average.

The proof is integration by parts against the flux, whose derivative is the Laplacian's circle
integral; `log' r = 1/r` cancels the radius the flux carries, leaving the circle average's own
derivative, which the fundamental theorem of calculus integrates. -/
theorem green_annulus_log (hu : ContDiff ℝ 2 u) (c : ℂ) {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ s in ε..R, Real.log s * (s * ∫ θ in (0 : ℝ)..(2 * π), Δ u (circleMap c s θ)))
      = Real.log R * circleFlux u c R - Real.log ε * circleFlux u c ε
        - 2 * π * (circleAverage u c R - circleAverage u c ε) := by
  have hpos : ∀ s ∈ Set.uIcc ε R, 0 < s := by
    rw [Set.uIcc_of_le hεR]
    exact fun s hs => lt_of_lt_of_le hε hs.1
  have hopen : ∀ s ∈ Set.Ioo (min ε R) (max ε R), 0 < s := by
    rw [min_eq_left hεR, max_eq_right hεR]
    exact fun s hs => lt_trans hε hs.1
  have hfluxcont : ContinuousOn (circleFlux u c) (Set.uIcc ε R) := by
    have : Continuous (circleFlux u c) := by
      unfold circleFlux
      exact continuous_id.mul (continuous_radialIntegral hu c)
    exact this.continuousOn
  have hlogcont : ContinuousOn Real.log (Set.uIcc ε R) :=
    Real.continuousOn_log.mono fun s hs => ne_of_gt (hpos s hs)
  -- Integration by parts against the flux.
  have hparts : (∫ s in ε..R, Real.log s * (s * ∫ θ in (0 : ℝ)..(2 * π),
        Δ u (circleMap c s θ)))
      = Real.log R * circleFlux u c R - Real.log ε * circleFlux u c ε
        - ∫ s in ε..R, s⁻¹ * circleFlux u c s :=
    intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt hlogcont hfluxcont
      (fun s hs => Real.hasDerivAt_log (ne_of_gt (hopen s hs)))
      (fun s hs => hasDerivAt_circleFlux hu c (ne_of_gt (hopen s hs)))
      (ContinuousOn.intervalIntegrable
        (continuousOn_inv₀.mono fun s hs => ne_of_gt (hpos s hs)))
      ((continuous_id.mul (continuous_laplacianIntegral hu c)).intervalIntegrable _ _)
  -- The remaining integral is the circle average's total change.
  have hderiv : (deriv fun t : ℝ => circleAverage u c t)
      = fun s : ℝ => (2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π),
          fderiv ℝ u (circleMap c s θ) (circleDir θ) := by
    funext s
    rw [(hasDerivAt_circleAverage hu c s).deriv, smul_eq_mul]
  have hftc : (∫ s in ε..R, deriv (fun t : ℝ => circleAverage u c t) s)
      = circleAverage u c R - circleAverage u c ε := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => ?_) ?_
    · rw [(hasDerivAt_circleAverage hu c s).deriv]
      exact hasDerivAt_circleAverage hu c s
    · rw [hderiv]
      exact (continuous_const.mul (continuous_radialIntegral hu c)).intervalIntegrable _ _
  have hpt : ∀ s ∈ Set.uIcc ε R,
      s⁻¹ * circleFlux u c s = 2 * π * deriv (fun t : ℝ => circleAverage u c t) s := by
    intro s hs
    rw [circleFlux, ← radialIntegral_eq hu c s, ← mul_assoc,
      inv_mul_cancel₀ (ne_of_gt (hpos s hs)), one_mul]
  have hrest : (∫ s in ε..R, s⁻¹ * circleFlux u c s)
      = 2 * π * (circleAverage u c R - circleAverage u c ε) := by
    rw [intervalIntegral.integral_congr hpt, intervalIntegral.integral_const_mul, hftc]
  rw [hparts, hrest]

end Shields
