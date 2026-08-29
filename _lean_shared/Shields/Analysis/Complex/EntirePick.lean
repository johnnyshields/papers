/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Normed.Group.Tannery
import Shields.Analysis.Complex.DenseNonReal
import Shields.Analysis.SpecialFunctions.Trigonometric.MultipleAngleBound
import Shields.Analysis.SpecificLimits.ConstDivBound

/-!
# An entire function with a sign-definite imaginary part is affine

A *Pick* (or *Herglotz*, or *Nevanlinna*) function maps the open upper half-plane into its
closure.  The classical fact that an **entire** Pick function is affine with nonnegative slope
is normally read off the Herglotz--Nevanlinna representation together with Stieltjes inversion.
Mathlib carries the Poisson and Herglotz--Riesz kernels on the *disk* only, and no half-plane
representation; the proof here needs neither.

## The argument

Write `v = Im E`.  Reality on the axis (`hconj`) makes `v` odd, so `v(z) · Im z ≥ 0` on the whole
plane once `v ≥ 0` on the upper half-plane -- and that single sign condition is all that is used.
On the circle of radius `ρ` the Fourier coefficients of `v` are the Taylor coefficients of `E`,

  `∫₀^{2π} v(ρe^{iθ}) sin (nθ) dθ = π aₙ ρⁿ`,

by Cauchy's theorem for the positive frequencies and Cauchy's formula for the negative ones.
The elementary inequality `|sin nθ| ≤ n |sin θ|` then compares the `n`-th coefficient with the
first against the *nonnegative* density `v(ρe^{iθ}) sin θ`, giving

  `|aₙ| ρⁿ ≤ n a₁ ρ`.

Letting `ρ → ∞` kills every `aₙ` with `n ≥ 2`, and `a₁ ≥ 0` because the density is nonnegative.
The scaling in `ρ` is what does the work: on a single circle a sine series can perfectly well be
nonnegative with higher harmonics present, and only their simultaneous nonnegativity at every
radius forces them out.

## Main statements

* `Shields.eq_affine_of_neg_le_im_mul_im`: the theorem, in the form used by a *meromorphic* Pick
  function with finitely many real poles.  Subtracting the principal parts of such a function
  leaves an entire `E` whose sign condition is only violated by a bounded defect `κ`, because
  each pole term `cᵢ/(λᵢ - z)` contributes `cᵢ (Im z)² / |λᵢ - z|² ≤ cᵢ` -- a real pole always
  satisfies `|λᵢ - z| ≥ |Im z|`.  Carrying the defect through costs one term in the estimate and
  removes any need for Donoghue's reflection lemma.
* `Shields.eq_affine_of_im_nonneg`: the classical statement, `κ = 0`.

## Implementation notes

The canonical representation is proved here rather than assumed.  A development that reduces a
spectral image to a Herglotz representation, or that reads a Pick function off an Edrei symbol,
would otherwise have to carry it as a hypothesis.

## Tags

Pick function, Herglotz, Nevanlinna, entire function, Liouville, Fourier coefficient
-/

open Real Set Filter Topology intervalIntegral

namespace Shields

/-! ### Fourier coefficients on a circle -/

section Fourier

variable {f : ℂ → ℂ}

open Complex in
private theorem circleMap_pow (ρ : ℝ) (k : ℕ) (θ : ℝ) :
    (circleMap 0 ρ θ) ^ k = (ρ : ℂ) ^ k * Complex.exp ((k : ℂ) * (θ : ℂ) * I) := by
  rw [circleMap_zero, mul_pow, ← Complex.exp_nat_mul]
  congr 2
  ring

open Complex in
/-- Continuity of the integrands below. -/
private theorem continuous_circle (hf : Differentiable ℂ f) (ρ : ℝ) :
    Continuous fun θ : ℝ => f (circleMap 0 ρ θ) :=
  hf.continuous.comp (continuous_circleMap 0 ρ)

open Complex in
/-- Continuity of the sine transform's integrand. -/
private theorem continuous_sin_mul_circle (hf : Differentiable ℂ f) (a ρ : ℝ) :
    Continuous fun θ : ℝ => (Real.sin (a * θ) : ℂ) * f (circleMap 0 ρ θ) :=
  (Complex.continuous_ofReal.comp (Real.continuous_sin.comp (by fun_prop))).mul
    (continuous_circle hf ρ)

open Complex in
/-- **Positive frequencies vanish**: Cauchy's theorem applied to `z ↦ zᵐ f z`. -/
private theorem integral_exp_pos_mul (hf : Differentiable ℂ f) (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ θ in (0 : ℝ)..(2 * π),
        Complex.exp (((m : ℂ) + 1) * (θ : ℂ) * I) * f (circleMap 0 ρ θ) = 0 := by
  have hzero : (∮ z in C(0, ρ), z ^ m * f z) = 0 :=
    DiffContOnCl.circleIntegral_eq_zero hρ.le
      (Differentiable.diffContOnCl (((differentiable_pow m).mul hf)))
  rw [circleIntegral] at hzero
  have hint : ∀ θ : ℝ,
      deriv (circleMap 0 ρ) θ • ((circleMap 0 ρ θ) ^ m * f (circleMap 0 ρ θ))
        = (I * (ρ : ℂ) ^ (m + 1)) *
            (Complex.exp (((m : ℂ) + 1) * (θ : ℂ) * I) * f (circleMap 0 ρ θ)) := by
    intro θ
    rw [deriv_circleMap, smul_eq_mul]
    have hp : (circleMap 0 ρ θ) * (circleMap 0 ρ θ) ^ m = (circleMap 0 ρ θ) ^ (m + 1) := by ring
    have hpow := circleMap_pow ρ (m + 1) θ
    push_cast at hpow
    calc circleMap 0 ρ θ * I * ((circleMap 0 ρ θ) ^ m * f (circleMap 0 ρ θ))
        = I * ((circleMap 0 ρ θ) * (circleMap 0 ρ θ) ^ m) * f (circleMap 0 ρ θ) := by ring
      _ = I * ((ρ : ℂ) ^ (m + 1) * Complex.exp (((m : ℂ) + 1) * (θ : ℂ) * I))
            * f (circleMap 0 ρ θ) := by rw [hp, hpow]
      _ = _ := by ring
  rw [intervalIntegral.integral_congr (g := fun θ =>
    (I * (ρ : ℂ) ^ (m + 1)) *
      (Complex.exp (((m : ℂ) + 1) * (θ : ℂ) * I) * f (circleMap 0 ρ θ)))
    (fun θ _ => hint θ), intervalIntegral.integral_const_mul] at hzero
  have hne : (I * (ρ : ℂ) ^ (m + 1)) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (pow_ne_zero _ (Complex.ofReal_ne_zero.2 hρ.ne'))
  exact (mul_eq_zero.mp hzero).resolve_left hne

open Complex in
/-- **Negative frequencies are the Taylor coefficients**: Cauchy's formula. -/
private theorem integral_exp_neg_mul (hf : Differentiable ℂ f) (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ θ in (0 : ℝ)..(2 * π),
        Complex.exp (-((n : ℂ) * (θ : ℂ)) * I) * f (circleMap 0 ρ θ)
      = 2 * π * (ρ : ℂ) ^ n * (cauchyPowerSeries f 0 1).coeff n := by
  -- the Cauchy series does not depend on the radius
  have hser : cauchyPowerSeries f 0 ρ = cauchyPowerSeries f 0 1 := by
    have h1 : HasFPowerSeriesAt f (cauchyPowerSeries f 0 ρ) 0 := by
      have := hf.hasFPowerSeriesOnBall (R := ρ.toNNReal) 0
        (by simpa using Real.toNNReal_pos.2 hρ)
      rw [Real.coe_toNNReal ρ hρ.le] at this
      exact this.hasFPowerSeriesAt
    have h2 : HasFPowerSeriesAt f (cauchyPowerSeries f 0 1) 0 :=
      (hf.hasFPowerSeriesOnBall (R := 1) 0 one_pos).hasFPowerSeriesAt
    exact h1.eq_formalMultilinearSeries h2
  have hne2 : (2 * (π : ℂ) * I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.2 Real.pi_ne_zero))
      Complex.I_ne_zero
  have hcoeff : (∮ z in C(0, ρ), (1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z)
      = 2 * π * I * (cauchyPowerSeries f 0 1).coeff n := by
    have h := cauchyPowerSeries_apply f 0 ρ n 1
    have hc : (cauchyPowerSeries f 0 1).coeff n = (cauchyPowerSeries f 0 ρ n fun _ => (1 : ℂ)) := by
      rw [hser]; rfl
    rw [hc, h, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hne2, one_mul]
  rw [circleIntegral] at hcoeff
  have hint : ∀ θ : ℝ,
      deriv (circleMap 0 ρ) θ •
          ((1 / (circleMap 0 ρ θ - 0)) ^ n • (circleMap 0 ρ θ - 0)⁻¹ • f (circleMap 0 ρ θ))
        = (I * ((ρ : ℂ) ^ n)⁻¹) *
            (Complex.exp (-((n : ℂ) * (θ : ℂ)) * I) * f (circleMap 0 ρ θ)) := by
    intro θ
    have hz : circleMap 0 ρ θ ≠ 0 := circleMap_ne_center hρ.ne'
    have hpow := circleMap_pow ρ n θ
    have hexp : (Complex.exp ((n : ℂ) * (θ : ℂ) * I))⁻¹
        = Complex.exp (-((n : ℂ) * (θ : ℂ)) * I) := by
      rw [← Complex.exp_neg]
      congr 1
      ring
    simp only [deriv_circleMap, smul_eq_mul, sub_zero, one_div, inv_pow]
    rw [hpow, mul_inv, hexp]
    field_simp
  rw [intervalIntegral.integral_congr (g := fun θ =>
    (I * ((ρ : ℂ) ^ n)⁻¹) *
      (Complex.exp (-((n : ℂ) * (θ : ℂ)) * I) * f (circleMap 0 ρ θ)))
    (fun θ _ => hint θ), intervalIntegral.integral_const_mul] at hcoeff
  have hIne : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  have hρne : ((ρ : ℂ) ^ n) ≠ 0 := pow_ne_zero _ (Complex.ofReal_ne_zero.2 hρ.ne')
  refine mul_left_cancel₀ (show (I * ((ρ : ℂ) ^ n)⁻¹) ≠ 0 from
    mul_ne_zero hIne (inv_ne_zero hρne)) ?_
  rw [hcoeff]
  field_simp

open Complex in
/-- **The sine transform of `f` on the circle of radius `ρ`.**  Subtracting the vanishing positive
frequency from the coefficient-carrying negative one. -/
private theorem sineIntegral (hf : Differentiable ℂ f) (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∫ θ in (0 : ℝ)..(2 * π),
        (Real.sin (((m + 1 : ℕ) : ℝ) * θ) : ℂ) * f (circleMap 0 ρ θ)
      = I * π * (ρ : ℂ) ^ (m + 1) * (cauchyPowerSeries f 0 1).coeff (m + 1) := by
  have hA := integral_exp_neg_mul hf (m + 1) hρ
  have hB := integral_exp_pos_mul hf m hρ
  have hcast : ((m : ℂ) + 1) = ((m + 1 : ℕ) : ℂ) := by push_cast; ring
  rw [hcast] at hB
  have hcont : Continuous fun θ : ℝ => f (circleMap 0 ρ θ) := continuous_circle hf ρ
  have hi : ∀ e : ℝ → ℂ, Continuous e → IntervalIntegrable
      (fun θ : ℝ => (I / 2) * (e θ * f (circleMap 0 ρ θ))) MeasureTheory.volume 0 (2 * π) :=
    fun _ he => (continuous_const.mul (he.mul hcont)).intervalIntegrable _ _
  have hi1 := hi (fun θ => Complex.exp (-(((m + 1 : ℕ) : ℂ) * (θ : ℂ)) * I))
    (Complex.continuous_exp.comp (by fun_prop))
  have hi2 := hi (fun θ => Complex.exp (((m + 1 : ℕ) : ℂ) * (θ : ℂ) * I))
    (Complex.continuous_exp.comp (by fun_prop))
  have hpt : ∀ θ : ℝ, (Real.sin (((m + 1 : ℕ) : ℝ) * θ) : ℂ) * f (circleMap 0 ρ θ)
      = (I / 2) * (Complex.exp (-(((m + 1 : ℕ) : ℂ) * (θ : ℂ)) * I) * f (circleMap 0 ρ θ))
        - (I / 2) * (Complex.exp (((m + 1 : ℕ) : ℂ) * (θ : ℂ) * I) * f (circleMap 0 ρ θ)) := by
    intro θ
    have hs : ((Real.sin (((m + 1 : ℕ) : ℝ) * θ) : ℝ) : ℂ)
        = Complex.sin (((m + 1 : ℕ) : ℂ) * (θ : ℂ)) := by
      rw [Complex.ofReal_sin]; push_cast; ring_nf
    have h1 : Complex.exp (-(((m + 1 : ℕ) : ℂ) * (θ : ℂ)) * I)
        = Complex.cos (((m + 1 : ℕ) : ℂ) * (θ : ℂ))
          - Complex.sin (((m + 1 : ℕ) : ℂ) * (θ : ℂ)) * I := by
      rw [show -(((m + 1 : ℕ) : ℂ) * (θ : ℂ)) * I = (-(((m + 1 : ℕ) : ℂ) * (θ : ℂ))) * I by ring,
        Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
      ring
    have h2 : Complex.exp (((m + 1 : ℕ) : ℂ) * (θ : ℂ) * I)
        = Complex.cos (((m + 1 : ℕ) : ℂ) * (θ : ℂ))
          + Complex.sin (((m + 1 : ℕ) : ℂ) * (θ : ℂ)) * I := Complex.exp_mul_I _
    rw [hs, h1, h2]
    have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
    linear_combination (f (circleMap 0 ρ θ) * Complex.sin (((m + 1 : ℕ) : ℂ) * (θ : ℂ))) * hI
  rw [intervalIntegral.integral_congr (g := fun θ =>
      (I / 2) * (Complex.exp (-(((m + 1 : ℕ) : ℂ) * (θ : ℂ)) * I) * f (circleMap 0 ρ θ))
        - (I / 2) * (Complex.exp (((m + 1 : ℕ) : ℂ) * (θ : ℂ) * I) * f (circleMap 0 ρ θ)))
      (fun θ _ => hpt θ),
    intervalIntegral.integral_sub hi1 hi2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hA, hB]
  ring

open Complex in
/-- **The Taylor coefficients are real**, because `f` is real on the axis.  The sine transform is
odd under the reflection `θ ↦ 2π - θ`, hence purely imaginary. -/
private theorem coeff_im_eq_zero (hf : Differentiable ℂ f)
    (hconj : ∀ u : ℂ, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u)) (m : ℕ) :
    ((cauchyPowerSeries f 0 1).coeff (m + 1)).im = 0 := by
  let G : ℝ → ℂ := fun t => (Real.sin (((m + 1 : ℕ) : ℝ) * t) : ℂ) * f (circleMap 0 1 t)
  have hGdef : ∀ t, G t
      = (Real.sin (((m + 1 : ℕ) : ℝ) * t) : ℂ) * f (circleMap 0 1 t) := fun _ => rfl
  have hcontG : Continuous G := continuous_sin_mul_circle hf (((m + 1 : ℕ) : ℝ)) 1
  have hcm : ∀ θ : ℝ, (starRingEnd ℂ) (circleMap 0 1 θ) = circleMap 0 1 (-θ) := fun θ => by
    rw [circleMap_zero, circleMap_zero, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring
  have hper : ∀ θ : ℝ, circleMap 0 1 (2 * π - θ) = circleMap 0 1 (-θ) := fun θ => by
    rw [show 2 * π - θ = -θ + 2 * π by ring]; exact periodic_circleMap 0 1 (-θ)
  have hsin : ∀ θ : ℝ, Real.sin (((m + 1 : ℕ) : ℝ) * (2 * π - θ))
      = -Real.sin (((m + 1 : ℕ) : ℝ) * θ) := fun θ => by
    rw [show ((m + 1 : ℕ) : ℝ) * (2 * π - θ)
        = -(((m + 1 : ℕ) : ℝ) * θ) + (m + 1 : ℕ) * (2 * π) by push_cast; ring,
      Real.sin_add_nat_mul_two_pi, Real.sin_neg]
  have hrefl : ∀ θ : ℝ, (starRingEnd ℂ) (G θ) = -G (2 * π - θ) := fun θ => by
    have hL : (starRingEnd ℂ) (G θ)
        = (Real.sin (((m + 1 : ℕ) : ℝ) * θ) : ℂ) * f (circleMap 0 1 (-θ)) := by
      rw [hGdef, map_mul, Complex.conj_ofReal, ← hconj (circleMap 0 1 θ), hcm]
    rw [hL, hGdef, hsin, hper]
    push_cast; ring
  have hconjS : (starRingEnd ℂ) (∫ θ in (0 : ℝ)..(2 * π), G θ)
      = -(∫ θ in (0 : ℝ)..(2 * π), G θ) := by
    rw [← intervalIntegral.intervalIntegral_conj,
      intervalIntegral.integral_congr (g := fun θ => -G (2 * π - θ)) (fun θ _ => hrefl θ),
      intervalIntegral.integral_neg]
    congr 1
    simp
  have hS := sineIntegral hf m (ρ := 1) one_pos
  simp only [Complex.ofReal_one, one_pow, mul_one] at hS
  have hSG : (∫ θ in (0 : ℝ)..(2 * π), G θ)
      = I * π * (cauchyPowerSeries f 0 1).coeff (m + 1) := hS
  rw [hSG] at hconjS
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal] at hconjS
  have hIpi : (-I * (π : ℂ)) ≠ 0 :=
    mul_ne_zero (neg_ne_zero.2 Complex.I_ne_zero) (Complex.ofReal_ne_zero.2 Real.pi_ne_zero)
  have hcc : (starRingEnd ℂ) ((cauchyPowerSeries f 0 1).coeff (m + 1))
      = (cauchyPowerSeries f 0 1).coeff (m + 1) := by
    refine mul_left_cancel₀ hIpi ?_
    linear_combination hconjS
  simp only [Complex.conj_eq_iff_im] at hcc
  exact hcc

open Complex in
/-- The real form of the sine transform: the `n`-th Fourier coefficient of `Im f` on the circle of
radius `ρ` is `π aₙ ρⁿ`. -/
private theorem sineIntegral_im (hf : Differentiable ℂ f) (m : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ θ in (0 : ℝ)..(2 * π),
        Real.sin (((m + 1 : ℕ) : ℝ) * θ) * (f (circleMap 0 ρ θ)).im)
      = π * ρ ^ (m + 1) * ((cauchyPowerSeries f 0 1).coeff (m + 1)).re := by
  have hS := sineIntegral hf m hρ
  have hcont : Continuous fun θ : ℝ =>
      (Real.sin (((m + 1 : ℕ) : ℝ) * θ) : ℂ) * f (circleMap 0 ρ θ) :=
    continuous_sin_mul_circle hf (((m + 1 : ℕ) : ℝ)) ρ
  have hIm := (intervalIntegral_im (μ := MeasureTheory.volume)
    (hcont.intervalIntegrable 0 (2 * π))).symm
  rw [hS] at hIm
  simp only [RCLike.im_eq_complex_im, Complex.im_ofReal_mul] at hIm
  rw [← hIm]
  have him0 : ((ρ : ℂ) ^ (m + 1)).im = 0 := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_im _
  have hre0 : ((ρ : ℂ) ^ (m + 1)).re = ρ ^ (m + 1) := by
    rw [← Complex.ofReal_pow]; exact Complex.ofReal_re _
  simp [Complex.mul_im, Complex.mul_re, him0, hre0]

/-- Integrability of every integrand below. -/
private theorem sineIntegral_im_one (hf : Differentiable ℂ f) {ρ : ℝ} (hρ : 0 < ρ) :
    (∫ θ in (0 : ℝ)..(2 * π), Real.sin θ * (f (circleMap 0 ρ θ)).im)
      = π * ρ * ((cauchyPowerSeries f 0 1).coeff 1).re := by
  have h := sineIntegral_im hf 0 hρ
  norm_num at h
  exact h

private theorem intervalIntegrable_sinMul (hf : Differentiable ℂ f) (r ρ : ℝ) :
    IntervalIntegrable (fun θ : ℝ => Real.sin (r * θ) * (f (circleMap 0 ρ θ)).im)
      MeasureTheory.volume 0 (2 * π) := by
  apply Continuous.intervalIntegrable
  exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).mul
    (Complex.continuous_im.comp (continuous_circle hf ρ))

/-- `Im f` and `Im z` have the same sign on the circle, up to a defect that is allowed to grow
quadratically.  On the circle of radius `ρ` the slack per unit of `sin θ` is `(A + Bρ²)/ρ`. -/
private theorem neg_le_sin_mul_im {A B : ℝ}
    (hsign : ∀ z : ℂ, -(A + B * ‖z‖ ^ 2) ≤ (f z).im * z.im)
    {ρ : ℝ} (hρ : 0 < ρ) (θ : ℝ) :
    -((A + B * ρ ^ 2) / ρ) ≤ Real.sin θ * (f (circleMap 0 ρ θ)).im := by
  have him : (circleMap 0 ρ θ).im = ρ * Real.sin θ := by
    rw [circleMap_zero]
    simp [Complex.mul_im, Complex.exp_ofReal_mul_I_im, Complex.exp_ofReal_mul_I_re]
  have hnorm : ‖circleMap 0 ρ θ‖ = ρ := by
    rw [circleMap_zero]
    simp [abs_of_pos hρ]
  have h := hsign (circleMap 0 ρ θ)
  rw [him, hnorm] at h
  rw [show -((A + B * ρ ^ 2) / ρ) = (-(A + B * ρ ^ 2)) / ρ by ring, div_le_iff₀ hρ,
    show Real.sin θ * (f (circleMap 0 ρ θ)).im * ρ
      = (f (circleMap 0 ρ θ)).im * (ρ * Real.sin θ) by ring]
  exact h

open Complex in
/-- **The comparison.**  `|sin nθ| ≤ n |sin θ|` against the density `Im f · sin θ`, which is
nonnegative up to `κ`. -/
private theorem coeff_re_estimate (hf : Differentiable ℂ f) {κ ρ : ℝ} (hρ : 0 < ρ)
    (hκ : 0 ≤ κ) (hlow : ∀ θ : ℝ, -κ ≤ Real.sin θ * (f (circleMap 0 ρ θ)).im) (m : ℕ) :
    π * ρ ^ (m + 1) * |((cauchyPowerSeries f 0 1).coeff (m + 1)).re|
      ≤ ((m + 1 : ℕ) : ℝ) * (π * ρ * ((cauchyPowerSeries f 0 1).coeff 1).re
          + 2 * κ * (2 * π)) := by
  have h2pi : (0 : ℝ) ≤ 2 * π := by positivity
  have hI1 := intervalIntegrable_sinMul hf (((m + 1 : ℕ) : ℝ)) ρ
  have hIsin' : IntervalIntegrable
      (fun θ : ℝ => Real.sin θ * (f (circleMap 0 ρ θ)).im) MeasureTheory.volume 0 (2 * π) := by
    simpa only [one_mul] using intervalIntegrable_sinMul hf 1 ρ
  have hI3 : IntervalIntegrable
      (fun θ : ℝ => ((m + 1 : ℕ) : ℝ) * (Real.sin θ * (f (circleMap 0 ρ θ)).im + 2 * κ))
      MeasureTheory.volume 0 (2 * π) :=
    (hIsin'.add intervalIntegrable_const).const_mul _
  have hpt : ∀ θ ∈ Set.Icc (0 : ℝ) (2 * π),
      |Real.sin (((m + 1 : ℕ) : ℝ) * θ) * (f (circleMap 0 ρ θ)).im|
        ≤ ((m + 1 : ℕ) : ℝ) * (Real.sin θ * (f (circleMap 0 ρ θ)).im + 2 * κ) := by
    intro θ _
    have h1 : |Real.sin (((m + 1 : ℕ) : ℝ) * θ) * (f (circleMap 0 ρ θ)).im|
        ≤ ((m + 1 : ℕ) : ℝ) * |Real.sin θ * (f (circleMap 0 ρ θ)).im| := by
      rw [abs_mul, abs_mul, ← mul_assoc]
      exact mul_le_mul_of_nonneg_right (abs_sin_natCast_mul_le (m + 1) θ) (abs_nonneg _)
    have h2 : |Real.sin θ * (f (circleMap 0 ρ θ)).im|
        ≤ Real.sin θ * (f (circleMap 0 ρ θ)).im + 2 * κ := by
      have hl := hlow θ
      have hk : 0 ≤ κ := hκ
      rcases abs_cases (Real.sin θ * (f (circleMap 0 ρ θ)).im) with h | h
      · linarith [h.1]
      · linarith [h.1]
    refine h1.trans ?_
    gcongr
  have hmono := intervalIntegral.integral_mono_on h2pi hI1.abs hI3 hpt
  have habs := intervalIntegral.abs_integral_le_integral_abs (μ := MeasureTheory.volume)
    (f := fun θ : ℝ => Real.sin (((m + 1 : ℕ) : ℝ) * θ) * (f (circleMap 0 ρ θ)).im) h2pi
  have hJn := sineIntegral_im hf m hρ
  have hJ1 := sineIntegral_im_one hf hρ
  have hRHS : (∫ θ in (0 : ℝ)..(2 * π),
        ((m + 1 : ℕ) : ℝ) * (Real.sin θ * (f (circleMap 0 ρ θ)).im + 2 * κ))
      = ((m + 1 : ℕ) : ℝ) * (π * ρ * ((cauchyPowerSeries f 0 1).coeff 1).re
          + 2 * κ * (2 * π)) := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add hIsin' intervalIntegrable_const, hJ1,
      intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    ring
  rw [hJn] at habs
  rw [hRHS] at hmono
  have hpos : |π * ρ ^ (m + 1) * ((cauchyPowerSeries f 0 1).coeff (m + 1)).re|
      = π * ρ ^ (m + 1) * |((cauchyPowerSeries f 0 1).coeff (m + 1)).re| := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < π * ρ ^ (m + 1))]
  rw [hpos] at habs
  linarith [habs, hmono]


/-- The first coefficient is bounded below by the slack alone: the density integrates to
`π ρ a₁`, and it is `≥ -κ` pointwise. -/
private theorem coeff_one_re_ge (hf : Differentiable ℂ f) {κ ρ : ℝ} (hρ : 0 < ρ)
    (hlow : ∀ θ : ℝ, -κ ≤ Real.sin θ * (f (circleMap 0 ρ θ)).im) :
    -(2 * κ / ρ) ≤ ((cauchyPowerSeries f 0 1).coeff 1).re := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hJ1 := sineIntegral_im_one hf hρ
  have hlowint : (∫ _θ in (0 : ℝ)..(2 * π), -κ)
      ≤ ∫ θ in (0 : ℝ)..(2 * π), Real.sin θ * (f (circleMap 0 ρ θ)).im := by
    refine intervalIntegral.integral_mono_on (by positivity) intervalIntegrable_const ?_ ?_
    · simpa only [one_mul] using intervalIntegrable_sinMul hf 1 ρ
    · intro θ _; exact hlow θ
  rw [hJ1, intervalIntegral.integral_const] at hlowint
  simp only [sub_zero, smul_eq_mul] at hlowint
  -- `2π(-κ) ≤ πρ a₁`, so `-2κ ≤ ρ a₁`
  have h2 : -(2 * κ) ≤ ρ * ((cauchyPowerSeries f 0 1).coeff 1).re := by
    refine le_of_mul_le_mul_left ?_ hπ
    calc π * -(2 * κ) = 2 * π * -κ := by ring
      _ ≤ π * ρ * ((cauchyPowerSeries f 0 1).coeff 1).re := hlowint
      _ = π * (ρ * ((cauchyPowerSeries f 0 1).coeff 1).re) := by ring
  rw [show -(2 * κ / ρ) = (-(2 * κ)) / ρ by ring, div_le_iff₀ hρ]
  linarith [h2]

end Fourier

/-! ### The theorem -/

open Complex in
/-- **Every Taylor coefficient beyond the first vanishes.**  The slack is allowed to grow
*quadratically* in `‖z‖`, and that is the whole point: a finite pole family gives a constant
defect, but an infinite one gives only a quadratic bound (`normSq_mul_sq_im_le`), and the
comparison tolerates it because `ρⁿ` beats `ρ` for `n ≥ 2` either way. -/
private theorem coeff_eq_zero_of_two_le {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ u : ℂ, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsign : ∀ z : ℂ, -(A + B * ‖z‖ ^ 2) ≤ (f z).im * z.im) :
    ∀ n : ℕ, 2 ≤ n → (cauchyPowerSeries f 0 1).coeff n = 0 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : 1 ≤ m := by omega
  have hre : ((cauchyPowerSeries f 0 1).coeff (m + 1)).re = 0 := by
    refine eq_zero_of_abs_le_const_div
      (C := ((m + 1 : ℕ) : ℝ)
        * (|((cauchyPowerSeries f 0 1).coeff 1).re| + 4 * A + 4 * B)) ?_
    intro ρ hρ1
    have hρ : (0 : ℝ) < ρ := lt_of_lt_of_le one_pos hρ1
    have hκ : 0 ≤ (A + B * ρ ^ 2) / ρ := by positivity
    have hest := coeff_re_estimate hf hρ hκ (neg_le_sin_mul_im hsign hρ) m
    have hpow : ρ ^ 2 ≤ ρ ^ (m + 1) := pow_le_pow_right₀ hρ1 (by omega)
    have hslack : (A + B * ρ ^ 2) / ρ ≤ (A + B) * ρ := by
      rw [div_le_iff₀ hρ]
      have h1 : (1 : ℝ) ≤ ρ ^ 2 := by nlinarith [hρ1]
      have h2 : A * 1 ≤ A * ρ ^ 2 := mul_le_mul_of_nonneg_left h1 hA
      nlinarith [h2]
    have step1 : π * ρ ^ 2 * |((cauchyPowerSeries f 0 1).coeff (m + 1)).re|
        ≤ π * ρ ^ (m + 1) * |((cauchyPowerSeries f 0 1).coeff (m + 1)).re| := by
      gcongr
    have step2 : ((m + 1 : ℕ) : ℝ) * (π * ρ * ((cauchyPowerSeries f 0 1).coeff 1).re
          + 2 * ((A + B * ρ ^ 2) / ρ) * (2 * π))
        ≤ π * ρ * (((m + 1 : ℕ) : ℝ)
            * (|((cauchyPowerSeries f 0 1).coeff 1).re| + 4 * A + 4 * B)) := by
      have t1 : ((m + 1 : ℕ) : ℝ) * (π * ρ) * ((cauchyPowerSeries f 0 1).coeff 1).re
          ≤ ((m + 1 : ℕ) : ℝ) * (π * ρ) * |((cauchyPowerSeries f 0 1).coeff 1).re| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
      have t2 : ((m + 1 : ℕ) : ℝ) * (4 * π) * ((A + B * ρ ^ 2) / ρ)
          ≤ ((m + 1 : ℕ) : ℝ) * (4 * π) * ((A + B) * ρ) :=
        mul_le_mul_of_nonneg_left hslack (by positivity)
      linarith [t1, t2]
    have hchain : π * ρ ^ 2 * |((cauchyPowerSeries f 0 1).coeff (m + 1)).re|
        ≤ π * ρ * (((m + 1 : ℕ) : ℝ)
            * (|((cauchyPowerSeries f 0 1).coeff 1).re| + 4 * A + 4 * B)) :=
      le_trans (le_trans step1 hest) step2
    rw [le_div_iff₀ hρ]
    refine le_of_mul_le_mul_left ?_ (by positivity : (0 : ℝ) < π * ρ)
    linarith [hchain]
  exact Complex.ext hre (coeff_im_eq_zero hf hconj m)

private theorem eq_ofReal_of_im_eq_zero' {z : ℂ} (h : z.im = 0) : z = (z.re : ℂ) :=
  (Complex.conj_eq_iff_re.mp (Complex.conj_eq_iff_im.mpr h)).symm

open Complex in
/-- Collapsing the power series once every coefficient beyond the first is gone.  Both survivors
are real, by `coeff_im_eq_zero` and by `f 0 = conj (f 0)`. -/
private theorem eq_affine_coeff {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ u : ℂ, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u))
    (hzero : ∀ n : ℕ, 2 ≤ n → (cauchyPowerSeries f 0 1).coeff n = 0) (u : ℂ) :
    f u = (((cauchyPowerSeries f 0 1).coeff 1).re : ℂ) * u
      + (((cauchyPowerSeries f 0 1).coeff 0).re : ℂ) := by
  have hp : HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 1) 0 ⊤ :=
    hf.hasFPowerSeriesOnBall (R := 1) 0 one_pos
  have hc0 : (cauchyPowerSeries f 0 1).coeff 0 = f 0 := hp.coeff_zero 1
  have hc0im : ((cauchyPowerSeries f 0 1).coeff 0).im = 0 := by
    rw [hc0]
    have h := hconj 0
    simp only [map_zero] at h
    exact Complex.conj_eq_iff_im.1 h.symm
  have hc1im : ((cauchyPowerSeries f 0 1).coeff 1).im = 0 := coeff_im_eq_zero hf hconj 0
  have hsum : HasSum (fun n => u ^ n • (cauchyPowerSeries f 0 1).coeff n) (f u) := by
    have h := hp.hasSum (y := u) (by simp)
    simpa [FormalMultilinearSeries.apply_eq_pow_smul_coeff] using h
  have hfin : HasSum (fun n => u ^ n • (cauchyPowerSeries f 0 1).coeff n)
      (∑ n ∈ ({0, 1} : Finset ℕ), u ^ n • (cauchyPowerSeries f 0 1).coeff n) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro n hn
    have h2 : 2 ≤ n := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      omega
    rw [hzero n h2, smul_zero]
  have huniq := hsum.unique hfin
  rw [huniq, Finset.sum_pair (by norm_num),
    eq_ofReal_of_im_eq_zero' hc0im, eq_ofReal_of_im_eq_zero' hc1im]
  simp only [pow_zero, pow_one, smul_eq_mul, one_mul, Complex.ofReal_re]
  ring

open Complex in
/-- **The quadratic-slack form.**  `Im f · Im z ≥ -(A + B‖z‖²)` already forces `f` affine.  The
slope is real but its **sign is not determined**: `B > 0` genuinely loses it, and `f u = γu + b`
with `γ < 0` can satisfy the hypothesis.  For the sign, use `eq_affine_of_neg_le_im_mul_im`
(constant slack) or read it off the Pick property directly. -/
theorem eq_affine_of_neg_quadratic_le_im_mul_im {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ u : ℂ, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u))
    {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hsign : ∀ z : ℂ, -(A + B * ‖z‖ ^ 2) ≤ (f z).im * z.im) :
    ∃ γ b : ℝ, ∀ u : ℂ, f u = γ * u + b :=
  ⟨_, _, eq_affine_coeff hf hconj (coeff_eq_zero_of_two_le hf hconj hA hB hsign)⟩

open Complex in
/-- **An entire function whose imaginary part is sign-definite off the real axis, up to a bounded
defect, is affine with nonnegative slope.**

`hsign` says `Im f(z) · Im z ≥ -κ`.  For a genuine Pick function real on the axis this holds with
`κ = 0`; the slack is what lets a *meromorphic* Pick function with finitely many poles be handled
after its principal parts are subtracted, since a pole at a real `λ` contributes
`c (Im z)²/|λ - z|² ≤ c`.

The slope `γ` is nonnegative and the intercept `b` real, both read off the Taylor coefficients. -/
theorem eq_affine_of_neg_le_im_mul_im {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ u : ℂ, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u))
    {κ : ℝ} (hsign : ∀ z : ℂ, -κ ≤ (f z).im * z.im) :
    ∃ γ b : ℝ, 0 ≤ γ ∧ ∀ u : ℂ, f u = γ * u + b := by
  have hκ : 0 ≤ κ := by
    have h := hsign 1
    simp at h
    linarith
  have hsign' : ∀ z : ℂ, -(κ + 0 * ‖z‖ ^ 2) ≤ (f z).im * z.im := by
    intro z; simpa using hsign z
  have hγ : 0 ≤ ((cauchyPowerSeries f 0 1).coeff 1).re := by
    refine nonneg_of_neg_const_div_le (C := 2 * κ) ?_
    intro ρ hρ1
    have hρ : (0 : ℝ) < ρ := lt_of_lt_of_le one_pos hρ1
    have hlow : ∀ θ : ℝ, -(κ / ρ) ≤ Real.sin θ * (f (circleMap 0 ρ θ)).im := by
      intro θ
      have h := neg_le_sin_mul_im hsign' hρ θ
      rw [show κ + 0 * ρ ^ 2 = κ by ring] at h
      exact h
    have h := coeff_one_re_ge hf hρ hlow
    have heq : 2 * (κ / ρ) / ρ = 2 * κ / ρ ^ 2 := by field_simp
    rw [heq] at h
    have hmono : 2 * κ / ρ ^ 2 ≤ 2 * κ / ρ := by
      rw [div_le_div_iff₀ (by positivity) hρ]
      have hd : (0 : ℝ) ≤ ρ ^ 2 - ρ := by nlinarith [hρ1]
      nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * κ) hd]
    linarith [h, hmono]
  exact ⟨_, _, hγ,
    eq_affine_coeff hf hconj (coeff_eq_zero_of_two_le hf hconj hκ le_rfl hsign')⟩

/-- The classical statement: an entire Pick function, real on the axis, is affine with nonnegative
slope.  No Herglotz--Nevanlinna representation and no Stieltjes inversion. -/
theorem eq_affine_of_im_nonneg {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ u : ℂ, f ((starRingEnd ℂ) u) = (starRingEnd ℂ) (f u))
    (hpick : ∀ z : ℂ, 0 < z.im → 0 ≤ (f z).im) :
    ∃ γ b : ℝ, 0 ≤ γ ∧ ∀ u : ℂ, f u = γ * u + b := by
  refine eq_affine_of_neg_le_im_mul_im hf hconj (κ := 0) ?_
  intro z
  simp only [neg_zero]
  rcases lt_trichotomy 0 z.im with h | h | h
  · exact mul_nonneg (hpick z h) h.le
  · rw [← h, mul_zero]
  · -- reflect: `Im f` is odd, so both factors flip sign
    have hz : 0 < ((starRingEnd ℂ) z).im := by simpa using h
    have hfz : 0 ≤ (f ((starRingEnd ℂ) z)).im := hpick _ hz
    rw [hconj z] at hfz
    simp only [Complex.conj_im] at hfz
    have hf0 : (f z).im ≤ 0 := by linarith
    nlinarith [hf0, h]

/-! ### The meromorphic case -/

section Meromorphic

/-- A real point is never a non-real one, so a real pole is no obstruction off the axis. -/
private theorem ofReal_ne_of_im_ne_zero {z : ℂ} (hz : z.im ≠ 0) (lam : ℝ) : (lam : ℂ) ≠ z :=
  fun h => hz (by rw [← h]; simp)

/-- **Real symmetry extends from the non-real points.**  A continuous `E` agreeing with its own
reflection off the real axis agrees with it everywhere, because the non-real points are dense.

This is what lets the pole representation, which says nothing at a pole, still pin `E` on the
axis: the representation is available exactly where `z.im ≠ 0`, and `dense_im_ne_zero` carries
the conclusion the rest of the way. -/
private theorem conj_symm_of_im_ne_zero {E : ℂ → ℂ} (hE : Continuous E)
    (h : ∀ u : ℂ, u.im ≠ 0 → E ((starRingEnd ℂ) u) = (starRingEnd ℂ) (E u)) (u : ℂ) :
    E ((starRingEnd ℂ) u) = (starRingEnd ℂ) (E u) :=
  congrFun (Continuous.ext_on dense_im_ne_zero (hE.comp Complex.continuous_conj)
    (Complex.continuous_conj.comp hE) fun w hw => h w hw) u

/-! ### An infinite pole family -/

/-- **The sharp pole defect.**  For a **real** `λ`,

  `λ² (Im z)² ≤ ‖z‖² |λ - z|²`,

because the difference is a square: `‖z‖²|λ - z|² - λ²(Im z)² = (λ · Re z - ‖z‖²)²`.

Realness of `λ` is essential, and the constant `1` is sharp -- equality holds exactly when
`λ · Re z = ‖z‖²`.  This is what makes an *infinite* pole family tractable: the crude bound
`(Im z)²/|λ - z|² ≤ 1` needs `Σ cᵢ < ∞`, which the Schoenberg--Edrei class does not give, whereas
this one needs only `Σ cᵢ/λᵢ² < ∞`, which is exactly the integrability condition the canonical
representation supplies.  The price is that the defect grows like `‖z‖²` instead of staying
bounded, and `coeff_eq_zero_of_two_le` is stated to absorb precisely that. -/
theorem sq_mul_sq_im_le (lam : ℝ) (z : ℂ) :
    lam ^ 2 * z.im ^ 2 ≤ ‖z‖ ^ 2 * Complex.normSq ((lam : ℂ) - z) := by
  rw [← Complex.normSq_eq_norm_sq]
  have key : Complex.normSq z * Complex.normSq ((lam : ℂ) - z) - lam ^ 2 * z.im ^ 2
      = (lam * z.re - Complex.normSq z) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    ring
  nlinarith [sq_nonneg (lam * z.re - Complex.normSq z), key]

theorem im_regularized (c lam : ℝ) (z : ℂ) :
    ((c : ℂ) * (1 / ((lam : ℂ) - z) - 1 / (lam : ℂ))).im
      = c * (z.im / Complex.normSq ((lam : ℂ) - z)) := by
  rw [Complex.im_ofReal_mul, Complex.sub_im, one_div, one_div, Complex.inv_im, Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg, neg_zero, zero_div, sub_zero]

/-- The regularized pole term's contribution to `Im · Im`, bounded by `c ‖z‖²/λ²`.  The
regularization `- 1/λ` is real, so it does not enter. -/
theorem im_regularized_mul_im_le {c lam : ℝ} (hc : 0 ≤ c) (hlam : lam ≠ 0) (z : ℂ) :
    ((c : ℂ) * (1 / ((lam : ℂ) - z) - 1 / (lam : ℂ))).im * z.im ≤ c / lam ^ 2 * ‖z‖ ^ 2 := by
  rw [im_regularized]
  have hlam2 : (0 : ℝ) < lam ^ 2 := by positivity
  rcases eq_or_lt_of_le (Complex.normSq_nonneg ((lam : ℂ) - z)) with h0 | hpos
  · rw [← h0, div_zero, mul_zero, zero_mul]
    positivity
  · have hkey := sq_mul_sq_im_le lam z
    rw [show c * (z.im / Complex.normSq ((lam : ℂ) - z)) * z.im
        = c * z.im ^ 2 / Complex.normSq ((lam : ℂ) - z) by field_simp,
      div_mul_eq_mul_div, div_le_div_iff₀ hpos hlam2]
    nlinarith [mul_le_mul_of_nonneg_left hkey hc]

/-- The imaginary part of a single principal part at a **real** pole.  The unregularized
counterpart of `im_regularized`; the two differ by the real constant `c/lam`, which contributes
nothing here. -/
theorem im_principalPart (c lam : ℝ) (z : ℂ) :
    ((c : ℂ) / ((lam : ℂ) - z)).im = c * (z.im / Complex.normSq ((lam : ℂ) - z)) := by
  rw [div_eq_mul_inv, Complex.im_ofReal_mul, Complex.inv_im]
  simp only [Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]

/-- **The bounded pole defect.**  A real pole contributes at most `c` to `Im · Im`, uniformly in
`z`, because `lam` real forces `|lam - z| ≥ |Im z|`.

This is what lets a *finite* pole family be handled without the Herglotz--Nevanlinna
representation: the entire part is never shown to be a Pick function, only to be one up to
`Σ cᵢ`, which is all `eq_affine_of_neg_le_im_mul_im` asks for.  An infinite family has no such
uniform bound and pays the quadratic price of `im_regularized_mul_im_le` instead. -/
theorem im_principalPart_mul_im_le {c lam : ℝ} (hc : 0 ≤ c) (z : ℂ) :
    ((c : ℂ) / ((lam : ℂ) - z)).im * z.im ≤ c := by
  rw [im_principalPart]
  rcases eq_or_lt_of_le (Complex.normSq_nonneg ((lam : ℂ) - z)) with h0 | hpos
  · rw [← h0, div_zero, mul_zero, zero_mul]
    exact hc
  · have hns : z.im ^ 2 ≤ Complex.normSq ((lam : ℂ) - z) := by
      have him := Complex.im_sq_le_normSq ((lam : ℂ) - z)
      simp only [Complex.sub_im, Complex.ofReal_im, zero_sub] at him
      nlinarith [him]
    rw [show c * (z.im / Complex.normSq ((lam : ℂ) - z)) * z.im
        = c * (z.im ^ 2 / Complex.normSq ((lam : ℂ) - z)) by ring]
    exact mul_le_of_le_one_right hc ((div_le_one hpos).2 hns)


/-- **A Pick function that is real on the axis has `Im R(z) · Im z ≥ 0` off it.**  Above the axis
this is the half-plane hypothesis itself.  Below it, the hypothesis says nothing directly, and the
reflection `R(conj z) = conj (R z)` is what carries it down: `Im R` changes sign with `Im z`, so
the product does not.

This is the whole use either representation theorem makes of the half-plane bound in the lower
half-plane, and it is where reality on the axis is spent. -/
theorem im_mul_im_nonneg_of_pick {R : ℂ → ℂ} {z : ℂ}
    (hpick : ∀ w : ℂ, 0 < w.im → 0 ≤ (R w).im)
    (hconj : R ((starRingEnd ℂ) z) = (starRingEnd ℂ) (R z)) (hz : z.im ≠ 0) :
    0 ≤ (R z).im * z.im := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have hzc : 0 < ((starRingEnd ℂ) z).im := by simpa using hneg
    have h1 := hpick _ hzc
    rw [hconj] at h1
    simp only [Complex.conj_im] at h1
    nlinarith [h1, hneg]
  · exact mul_nonneg (hpick z hpos) hpos.le

/-- **The entire part carries the sign condition up to the defect that was removed.**  If `R` is
Pick on the upper half-plane and real on the axis, and the removed part `R - E` contributes at
most `d` to `Im · Im z`, then `Im E · Im z ≥ -d`.  On the real axis the product is `0` and the
bound is free, which is the one point `im_mul_im_nonneg_of_pick` does not reach; off the axis the
two facts subtract.

This is all either representation theorem below asks of its pole part, and the `d` a pole family
costs is what separates them: a constant `Σ cᵢ` for finitely many poles, a quadratic `C‖z‖²` for a
summable infinite family. -/
theorem neg_le_im_mul_im_of_pick {R E : ℂ → ℂ} {d : ℝ} {z : ℂ}
    (hpick : ∀ w : ℂ, 0 < w.im → 0 ≤ (R w).im)
    (hconj : z.im ≠ 0 → R ((starRingEnd ℂ) z) = (starRingEnd ℂ) (R z)) (hd : 0 ≤ d)
    (hdefect : z.im ≠ 0 → (R z - E z).im * z.im ≤ d) :
    -d ≤ (E z).im * z.im := by
  rcases eq_or_ne z.im 0 with hz | hz
  · rw [hz, mul_zero]
    linarith
  · have hR0 : 0 ≤ (R z).im * z.im := im_mul_im_nonneg_of_pick hpick (hconj hz) hz
    have hEz : (E z).im * z.im = (R z).im * z.im - (R z - E z).im * z.im := by
      rw [Complex.sub_im]; ring
    rw [hEz]
    linarith [hdefect hz]

open Complex in
/-- **The entire part of a meromorphic Pick function with a summable real pole family is affine**,
the family allowed to be **infinite**.

The hypothesis `hsplit` is the paper's representation in its *regularized* form: off the poles,
`R - E` is the sum of `cᵢ(1/(λᵢ - u) - 1/λᵢ)`.  The regularization is what makes the series
converge when `Σ cᵢ` diverges and only `Σ cᵢ/λᵢ² < ∞` -- exactly the integrability condition
`∫ dσ(λ)/(λ²+1) < ∞` of the canonical representation, transported to the poles.  Being a real
constant, `- 1/λᵢ` disturbs no imaginary part, so the defect is still controlled, now by
`sq_mul_sq_im_le` rather than termwise by `cᵢ`.

The slope's **sign is not concluded**, because the defect is quadratic rather than constant.  For
the Schoenberg--Edrei application it is read off the Pick property on the imaginary axis instead,
which the finite case never needed. -/
theorem eq_affine_entirePart_of_pick {ι : Type*} {R E : ℂ → ℂ} {c lam : ι → ℝ} {C : ℝ}
    (hc : ∀ i, 0 ≤ c i) (hlam : ∀ i, lam i ≠ 0) (hE : Differentiable ℂ E)
    (hC : HasSum (fun i => c i / lam i ^ 2) C)
    (hsplit : ∀ u : ℂ, (∀ i, (lam i : ℂ) ≠ u) →
      HasSum (fun i => (c i : ℂ) * (1 / ((lam i : ℂ) - u) - 1 / (lam i : ℂ))) (R u - E u))
    (hconjR : ∀ u : ℂ, (∀ i, (lam i : ℂ) ≠ u) →
      R ((starRingEnd ℂ) u) = (starRingEnd ℂ) (R u))
    (hpick : ∀ z : ℂ, 0 < z.im → 0 ≤ (R z).im) :
    ∃ γ b : ℝ, ∀ u : ℂ, E u = γ * u + b := by
  have hpole : ∀ {z : ℂ}, z.im ≠ 0 → ∀ i, (lam i : ℂ) ≠ z :=
    fun hz i => ofReal_ne_of_im_ne_zero hz (lam i)
  have hC0 : 0 ≤ C := hC.nonneg fun i => div_nonneg (hc i) (sq_nonneg _)
  have hfam : ∀ (u : ℂ) (i : ι),
      (starRingEnd ℂ) ((c i : ℂ) * (1 / ((lam i : ℂ) - u) - 1 / (lam i : ℂ)))
        = (c i : ℂ) * (1 / ((lam i : ℂ) - (starRingEnd ℂ) u) - 1 / (lam i : ℂ)) := by
    intro u i
    simp only [map_mul, map_sub, map_div₀, map_one, Complex.conj_ofReal]
  -- the entire part is real on the axis, by density
  have hconjE : ∀ u : ℂ, E ((starRingEnd ℂ) u) = (starRingEnd ℂ) (E u) :=
    conj_symm_of_im_ne_zero hE.continuous fun u hu => by
      have huc : ((starRingEnd ℂ) u).im ≠ 0 := by simpa using hu
      have h1' : HasSum
          (fun i => (c i : ℂ) * (1 / ((lam i : ℂ) - (starRingEnd ℂ) u) - 1 / (lam i : ℂ)))
          ((starRingEnd ℂ) (R u - E u)) := by
        simpa only [RCLike.star_def, hfam u] using (hsplit u (hpole hu)).star
      have huq := (hsplit ((starRingEnd ℂ) u) (hpole huc)).unique h1'
      rw [map_sub, hconjR u (hpole hu)] at huq
      linear_combination -huq
  -- the sign condition, now with quadratic slack
  have hsign : ∀ z : ℂ, -(0 + C * ‖z‖ ^ 2) ≤ (E z).im * z.im := fun z =>
    neg_le_im_mul_im_of_pick hpick (fun hz => hconjR z (hpole hz))
      (by have := mul_nonneg hC0 (sq_nonneg ‖z‖); linarith) fun hz => by
        have him : HasSum
            (fun i => ((c i : ℂ) * (1 / ((lam i : ℂ) - z) - 1 / (lam i : ℂ))).im * z.im)
            ((R z - E z).im * z.im) := (Complex.hasSum_im (hsplit z (hpole hz))).mul_right _
        have hbound : HasSum (fun i => c i / lam i ^ 2 * ‖z‖ ^ 2) (C * ‖z‖ ^ 2) := hC.mul_right _
        have hsum_le : (R z - E z).im * z.im ≤ C * ‖z‖ ^ 2 :=
          hasSum_le (fun i => im_regularized_mul_im_le (hc i) (hlam i) z) him hbound
        linarith
  obtain ⟨gam, b, haff⟩ :=
    eq_affine_of_neg_quadratic_le_im_mul_im hE hconjE le_rfl hC0 hsign
  exact ⟨gam, b, haff⟩

/-- **The lost sign is genuinely lost.**  `f u = -u` is entire, real on the axis, and satisfies
the quadratic hypothesis with `A = 0`, `B = 1` -- with slope `-1`.  So
`eq_affine_of_neg_quadratic_le_im_mul_im` cannot be strengthened to give `0 ≤ γ`, and
`nonneg_slope_of_pick` is doing real work rather than repackaging it. -/
theorem neg_slope_witness (z : ℂ) : -(0 + 1 * ‖z‖ ^ 2) ≤ (-z).im * z.im := by
  simp only [Complex.neg_im, zero_add, one_mul]
  nlinarith [Complex.im_sq_le_normSq z, Complex.sq_norm z]

/-- The pole sum `S(t) = Σ cᵢ/(λᵢ² + t²)` converges, being dominated termwise by its value on
the axis. -/
private theorem summable_poleSum {ι : Type*} {c lam : ι → ℝ} {C : ℝ} (hc : ∀ i, 0 ≤ c i)
    (hlam : ∀ i, lam i ≠ 0) (hC : HasSum (fun i => c i / lam i ^ 2) C) (t : ℝ) :
    Summable fun i => c i / (lam i ^ 2 + t ^ 2) :=
  Summable.of_nonneg_of_le
    (fun i => div_nonneg (hc i) (by nlinarith [sq_nonneg t, sq_nonneg (lam i), hlam i]))
    (fun i => div_le_div_of_nonneg_left (hc i) (sq_pos_of_ne_zero (hlam i))
      (by nlinarith [sq_nonneg t]))
    hC.summable

/-- **The pole sum vanishes at infinity.**  `S(t) = Σ cᵢ/(λᵢ² + t²) → 0` as `t → ∞`: each term
tends to `0` and is dominated uniformly in `t` by the summable `cᵢ/λᵢ²`, which is Tannery's
theorem. -/
private theorem tendsto_tsum_poleSum {ι : Type*} {c lam : ι → ℝ} {C : ℝ} (hc : ∀ i, 0 ≤ c i)
    (hlam : ∀ i, lam i ≠ 0) (hC : HasSum (fun i => c i / lam i ^ 2) C) :
    Filter.Tendsto (fun t : ℝ => ∑' i, c i / (lam i ^ 2 + t ^ 2)) Filter.atTop (nhds 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := Filter.atTop)
    (f := fun (t : ℝ) (i : ι) => c i / (lam i ^ 2 + t ^ 2)) (g := fun _ : ι => (0 : ℝ))
    (bound := fun i => c i / lam i ^ 2) hC.summable ?_ ?_
  · simpa using h
  · intro i
    have hdiv : Filter.Tendsto (fun t : ℝ => lam i ^ 2 + t ^ 2) Filter.atTop Filter.atTop := by
      simpa using Filter.tendsto_atTop_add_const_left Filter.atTop (lam i ^ 2)
        (tendsto_pow_atTop two_ne_zero)
    simpa [div_eq_mul_inv] using hdiv.inv_tendsto_atTop.const_mul (c i)
  · filter_upwards with t i
    rw [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hc i)
        (by nlinarith [sq_nonneg t, sq_nonneg (lam i), hlam i]))]
    exact div_le_div_of_nonneg_left (hc i) (sq_pos_of_ne_zero (hlam i))
      (by nlinarith [sq_nonneg t])

open Complex in
/-- **The slope is nonnegative.**  With a finite pole family the constant defect already delivers
this (`eq_affine_of_neg_le_im_mul_im`); with an infinite one the defect is quadratic and the sign
is lost, so it is recovered from the Pick property on the imaginary axis.

On `z = it` every pole term contributes `cᵢ t/(λᵢ² + t²) ≥ 0`, so `0 ≤ Im R(it) = γt + t·S(t)`
with `S(t) = Σ cᵢ/(λᵢ² + t²)`.  Dividing by `t > 0` gives `γ ≥ -S(t)`, and `S(t) → 0` as `t → ∞`
by Tannery's theorem against the summable bound `cᵢ/λᵢ²`. -/
theorem nonneg_slope_of_pick {ι : Type*} {R E : ℂ → ℂ} {c lam : ι → ℝ} {C γ b : ℝ}
    (hc : ∀ i, 0 ≤ c i) (hlam : ∀ i, lam i ≠ 0)
    (hC : HasSum (fun i => c i / lam i ^ 2) C)
    (hsplit : ∀ u : ℂ, (∀ i, (lam i : ℂ) ≠ u) →
      HasSum (fun i => (c i : ℂ) * (1 / ((lam i : ℂ) - u) - 1 / (lam i : ℂ))) (R u - E u))
    (hpick : ∀ z : ℂ, 0 < z.im → 0 ≤ (R z).im)
    (haff : ∀ u : ℂ, E u = (γ : ℂ) * u + (b : ℂ)) :
    0 ≤ γ := by
  have hlim := tendsto_tsum_poleSum hc hlam hC
  -- the identity on the imaginary axis
  have hkey : ∀ t : ℝ, 0 < t → -(∑' i, c i / (lam i ^ 2 + t ^ 2)) ≤ γ := by
    intro t ht
    have hzim : ((t : ℂ) * Complex.I).im = t := by simp
    have hns : ∀ i : ι, Complex.normSq ((lam i : ℂ) - (t : ℂ) * Complex.I)
        = lam i ^ 2 + t ^ 2 := fun i => by
      rw [show ((lam i : ℂ) - (t : ℂ) * Complex.I)
            = (lam i : ℂ) + ((-t : ℝ) : ℂ) * Complex.I by push_cast; ring,
        Complex.normSq_add_mul_I]
      ring
    have hpoles : ∀ i, (lam i : ℂ) ≠ (t : ℂ) * Complex.I := by
      intro i h
      have h0 : ((t : ℂ) * Complex.I).im = 0 := by rw [← h]; simp
      rw [hzim] at h0
      exact ht.ne' h0
    have hterm : ∀ i : ι,
        ((c i : ℂ) * (1 / ((lam i : ℂ) - (t : ℂ) * Complex.I) - 1 / (lam i : ℂ))).im
          = t * (c i / (lam i ^ 2 + t ^ 2)) := by
      intro i
      rw [im_regularized, hns i, hzim]
      ring
    have him2 : HasSum (fun i => t * (c i / (lam i ^ 2 + t ^ 2)))
        ((R ((t : ℂ) * Complex.I) - E ((t : ℂ) * Complex.I)).im) := by
      have h := Complex.hasSum_im (hsplit ((t : ℂ) * Complex.I) hpoles)
      simpa only [hterm] using h
    have huq := him2.unique ((summable_poleSum hc hlam hC t).hasSum.mul_left t)
    have hEim : (E ((t : ℂ) * Complex.I)).im = γ * t := by
      rw [haff]; simp
    have hRim : (R ((t : ℂ) * Complex.I)).im
        = γ * t + t * ∑' i, c i / (lam i ^ 2 + t ^ 2) := by
      rw [Complex.sub_im, hEim] at huq
      linarith [huq]
    have hge := hpick ((t : ℂ) * Complex.I) (by rw [hzim]; exact ht)
    rw [hRim] at hge
    have h2 : 0 ≤ γ + ∑' i, c i / (lam i ^ 2 + t ^ 2) :=
      le_of_mul_le_mul_left (by linarith [hge]) ht
    linarith [h2]
  have hfinal : -γ ≤ 0 := ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨1, fun t ht => by
    have h := hkey t (lt_of_lt_of_le one_pos ht)
    linarith⟩)
  linarith

open Complex in
/-- **The canonical representation of a meromorphic Pick function, at an infinite pole family.**

The pole set may be infinite; what is assumed of it is `Σ cᵢ/λᵢ² < ∞`, which is the integrability
condition `∫ dσ(λ)/(λ²+1) < ∞` of the classical representation transported to the poles, and the
representation is taken in its **regularized** form because that is the only form that converges
there.

Neither the Herglotz--Nevanlinna representation nor Donoghue's reflection lemma is used.  Two
things replace them: `sq_mul_sq_im_le`, which turns `Σ cᵢ/λᵢ² < ∞` into quadratic control of the
defect where the finite case had a constant, and `nonneg_slope_of_pick`, which recovers the sign
of the slope from the Pick property on the imaginary axis once the quadratic slack has spent it. -/
theorem eq_affine_add_regularizedParts_of_pick {ι : Type*} {R E : ℂ → ℂ} {c lam : ι → ℝ} {C : ℝ}
    (hc : ∀ i, 0 ≤ c i) (hlam : ∀ i, lam i ≠ 0) (hE : Differentiable ℂ E)
    (hC : HasSum (fun i => c i / lam i ^ 2) C)
    (hsplit : ∀ u : ℂ, (∀ i, (lam i : ℂ) ≠ u) →
      HasSum (fun i => (c i : ℂ) * (1 / ((lam i : ℂ) - u) - 1 / (lam i : ℂ))) (R u - E u))
    (hconjR : ∀ u : ℂ, (∀ i, (lam i : ℂ) ≠ u) →
      R ((starRingEnd ℂ) u) = (starRingEnd ℂ) (R u))
    (hpick : ∀ z : ℂ, 0 < z.im → 0 ≤ (R z).im) :
    ∃ γ b : ℝ, 0 ≤ γ ∧ ∀ u : ℂ, E u = (γ : ℂ) * u + (b : ℂ) := by
  obtain ⟨gam, bb, haff⟩ := eq_affine_entirePart_of_pick hc hlam hE hC hsplit hconjR hpick
  exact ⟨gam, bb, nonneg_slope_of_pick hc hlam hC hsplit hpick haff, haff⟩

open Complex in
/-- **The canonical representation of a meromorphic Pick function with finitely many poles**,
proved rather than assumed.

`R` is meromorphic on `ℂ` with at worst simple poles at the **real** points `λᵢ` and residues
`-cᵢ ≤ 0` -- stated by exhibiting the entire remainder `E`, which assumes nothing about the
entire part -- it is real on the axis, and it has nonnegative imaginary part on the upper
half-plane.  Then

  `R(u) = γu + b + Σᵢ cᵢ/(λᵢ - u)`,  `γ ≥ 0`, `b` real.

The classical route is the Herglotz--Nevanlinna representation (Donoghue, *Monotone Matrix
Functions and Analytic Continuation*, Ch. II, Thm. I) followed by the reflection lemma
(Ch. II, Lem. 2), which makes the representing measure atomic on the pole set.  Neither is used
here and neither is in Mathlib.

Two things make the elementary route work.  `eq_affine_of_neg_le_im_mul_im` needs only a
**lower** bound on `Im E · Im z`, and a real pole supplies a bounded defect: `λᵢ` real forces
`|λᵢ - z| ≥ |Im z|`, hence `cᵢ (Im z)²/|λᵢ - z|² ≤ cᵢ` uniformly in `z`.  So the entire part is
never shown to be a Pick function, only to be one up to `Σ cᵢ` -- and the reflection lemma,
whose whole job is to supply exactly that, is not needed. -/
theorem eq_affine_add_principalParts_of_pick {ι : Type*} [Fintype ι] {R E : ℂ → ℂ}
    {c lam : ι → ℝ} (hc : ∀ i, 0 ≤ c i) (hE : Differentiable ℂ E)
    (hsplit : ∀ u : ℂ, (∀ i, (lam i : ℂ) ≠ u) →
      R u = E u + ∑ i, (c i : ℂ) / ((lam i : ℂ) - u))
    (hconjR : ∀ u : ℂ, (∀ i, (lam i : ℂ) ≠ u) →
      R ((starRingEnd ℂ) u) = (starRingEnd ℂ) (R u))
    (hpick : ∀ z : ℂ, 0 < z.im → 0 ≤ (R z).im) :
    ∃ γ : ℝ, 0 ≤ γ ∧ ∃ b : ℝ, ∀ u : ℂ, (∀ i, (lam i : ℂ) ≠ u) →
      R u = (γ : ℂ) * u + (b : ℂ) + ∑ i, (c i : ℂ) / ((lam i : ℂ) - u) := by
  -- a real point is a pole only of a real argument
  have hpole : ∀ {z : ℂ}, z.im ≠ 0 → ∀ i, (lam i : ℂ) ≠ z :=
    fun hz i => ofReal_ne_of_im_ne_zero hz (lam i)
  have hpp : ∀ w : ℂ, ∑ i, (c i : ℂ) / ((lam i : ℂ) - (starRingEnd ℂ) w)
      = (starRingEnd ℂ) (∑ i, (c i : ℂ) / ((lam i : ℂ) - w)) := by
    intro w
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_div₀, Complex.conj_ofReal, map_sub, Complex.conj_ofReal]
  -- the entire part is real on the axis, by density
  have hconjE : ∀ u : ℂ, E ((starRingEnd ℂ) u) = (starRingEnd ℂ) (E u) :=
    conj_symm_of_im_ne_zero hE.continuous fun u hu => by
      have huc : ((starRingEnd ℂ) u).im ≠ 0 := by simpa using hu
      rw [show E ((starRingEnd ℂ) u)
          = R ((starRingEnd ℂ) u) - ∑ i, (c i : ℂ) / ((lam i : ℂ) - (starRingEnd ℂ) u) by
        rw [hsplit ((starRingEnd ℂ) u) (hpole huc)]; ring,
        hconjR u (hpole hu), hpp u, hsplit u (hpole hu), map_add]
      ring
  -- the sign condition, with the bounded defect
  have hκ0 : 0 ≤ ∑ i, c i := Finset.sum_nonneg fun i _ => hc i
  have hsign : ∀ z : ℂ, -(∑ i, c i) ≤ (E z).im * z.im := fun z =>
    neg_le_im_mul_im_of_pick hpick (fun hz => hconjR z (hpole hz)) hκ0 fun hz => by
      have hRE : R z - E z = ∑ i, (c i : ℂ) / ((lam i : ℂ) - z) := by
        rw [hsplit z (hpole hz)]; ring
      rw [hRE, Complex.im_sum, Finset.sum_mul]
      exact Finset.sum_le_sum fun i _ => im_principalPart_mul_im_le (hc i) z
  obtain ⟨gam, b, hgam, haff⟩ := eq_affine_of_neg_le_im_mul_im hE hconjE hsign
  exact ⟨gam, hgam, b, fun u hu => by rw [hsplit u hu, haff u]⟩

end Meromorphic


/-! ### Axiom footprint -/

/-- info: 'Shields.eq_affine_of_im_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_affine_of_im_nonneg

end Shields
