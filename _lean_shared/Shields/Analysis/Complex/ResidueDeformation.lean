/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.CircleIntegral
import Shields.Analysis.Complex.ArgumentPrinciple.Polynomial

/-!
# Deforming a circle integral past finitely many simple poles

Let `g` be holomorphic on a closed annulus `\rho \le |z| \le R` apart from finitely many
**distinct simple poles** `a_i` lying strictly inside it, with residues `b_i`.  Then

\[
  \oint_{|z|=R}g-\oint_{|z|=\rho}g=2\pi i\sum_i b_i .
\]

The mechanism is the usual one and needs no winding numbers: subtract every principal part
`b_i/(z-a_i)`, fill in the removable singularities, and what is left is holomorphic on the
annulus, so Cauchy–Goursat moves it between the two circles for free.  Each principal part
contributes `2\pi i b_i` on the outer circle and nothing on the inner one.

Two forms are given.  The first takes the regular part as a hypothesis, which is what a caller
who already has the decomposition wants.  The second **builds** it — `regularPart` subtracts the
principal parts and patches the punctures — so that the hypotheses are only that the poles are
distinct, simple, and interior, with the residues presented as
`b_i = \lim_{z\to a_i}(z-a_i)g(z)`.

## Main results

* `Shields.circleIntegral_sub_inv_of_gt` — the integral of `(z-w)^{-1}` over a circle enclosing
  the pole.  The complementary case, the pole outside, is
  `Shields.circleIntegral_sub_inv_of_lt`, already available at an arbitrary center.
* `Shields.circleIntegral_deform_simple_poles` — the deformation, with the regular part given.
* `Shields.regularPart`, `Shields.differentiableAt_regularPart` — the regular part, built.
* `Shields.circleIntegral_deform_of_simplePoles` — **the deformation**, with the regular part
  built rather than assumed.
* `Shields.eq_principalPart_two` — the order-two Laurent split of `F z / (z - ζ)^2`.
* `Shields.circleIntegral_deform_double_pole_of_quotient` — **the deformation past a pole of order
  at most two**, presented as such a quotient.  A simple pole is the case `F ζ = 0`, so this covers
  both orders without a case split.

## Implementation notes

`regularPart` uses `Function.update` at each pole to install the removable value, so it is
definitionally `g` away from the poles and needs `DecidableEq` on the index type.  Residues enter
as limits rather than as `Complex.residue`, since that is the shape a caller with an explicit
factorization has on hand.

## References

* L. V. Ahlfors, *Complex analysis*, 3rd ed., McGraw–Hill, 1979, Ch. 4 §5.

## Tags

residue theorem, contour deformation, simple pole, annulus, cauchy goursat
-/

open scoped Real
open Complex Metric Set
open Filter Topology

namespace Shields

/-- A pole strictly inside contributes `2πi` times its residue. -/
theorem circleIntegral_sub_inv_of_gt {w : ℂ} {r : ℝ} (hw : ‖w‖ < r) :
    (∮ z in C(0, r), (z - w)⁻¹) = 2 * π * I := by
  refine circleIntegral.integral_sub_inv_of_mem_ball ?_
  simpa [mem_ball, dist_zero_right] using hw

theorem circleIntegral_finset_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ → ℂ) (c : ℂ) (r : ℝ)
    (hf : ∀ i ∈ S, CircleIntegrable (f i) c r) :
    (∮ z in C(c, r), ∑ i ∈ S, f i z) = ∑ i ∈ S, ∮ z in C(c, r), f i z :=
  circleIntegral.integral_fun_sum hf

/-- **Deforming past a cluster of simple poles**, with the regular part given.  On each of the two
circles the integrand `g` is presented as a regular part `h` plus the principal
parts `b_i/(z - a_i)` of finitely many simple poles lying strictly inside the
annulus.  Cauchy--Goursat for the annulus moves `h` between the circles for
free, the outer circle picks up `2πi b_i` at each pole and the inner circle
picks up nothing, so the difference of the two integrals is exactly `2πi` times
the sum of the residues. -/
theorem circleIntegral_deform_simple_poles {ι : Type*}
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) {g h : ℂ → ℂ}
    (S : Finset ι) (a : ι → ℂ) (b : ι → ℂ)
    (hin : ∀ i ∈ S, ρ < ‖a i‖ ∧ ‖a i‖ < R)
    (hcont : ContinuousOn h (closedBall 0 R \ ball 0 ρ))
    (hdiff : ∀ z ∈ ball (0 : ℂ) R \ closedBall 0 ρ, DifferentiableAt ℂ h z)
    (hgR : EqOn g (fun z => h z + ∑ i ∈ S, b i / (z - a i)) (sphere 0 R))
    (hgρ : EqOn g (fun z => h z + ∑ i ∈ S, b i / (z - a i)) (sphere 0 ρ)) :
    (∮ z in C(0, R), g z) = (∮ z in C(0, ρ), g z) + 2 * π * I * ∑ i ∈ S, b i := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le hρ hρR
  -- Each sphere sits in the closed annulus, and misses every pole.
  have hsphereR : sphere (0 : ℂ) R ⊆ closedBall 0 R \ ball 0 ρ := by
    intro z hz
    rw [mem_sphere, dist_zero_right] at hz
    exact ⟨by simp [mem_closedBall, dist_zero_right, hz],
      by simp [mem_ball, dist_zero_right, hz, not_lt.mpr hρR]⟩
  have hsphereρ : sphere (0 : ℂ) ρ ⊆ closedBall 0 R \ ball 0 ρ := by
    intro z hz
    rw [mem_sphere, dist_zero_right] at hz
    exact ⟨by simp [mem_closedBall, dist_zero_right, hz, hρR],
      by simp [mem_ball, dist_zero_right, hz]⟩
  -- One circle at a time: split the integral into its regular and polar parts.
  have split : ∀ r : ℝ, 0 < r → sphere (0 : ℂ) r ⊆ closedBall 0 R \ ball 0 ρ →
      (∀ i ∈ S, ‖a i‖ ≠ r) →
      EqOn g (fun z => h z + ∑ i ∈ S, b i / (z - a i)) (sphere 0 r) →
      (∮ z in C(0, r), g z)
        = (∮ z in C(0, r), h z) + ∑ i ∈ S, b i * ∮ z in C(0, r), (z - a i)⁻¹ := by
    intro r hr hsub hmiss heq
    have hpole : ∀ i ∈ S, CircleIntegrable (fun z => b i / (z - a i)) 0 r := by
      intro i hi
      refine ContinuousOn.circleIntegrable hr.le ?_
      refine continuousOn_const.div (continuousOn_id.sub continuousOn_const) ?_
      intro z hz hzw
      rw [sub_eq_zero] at hzw
      rw [mem_sphere, dist_zero_right] at hz
      exact hmiss i hi (hzw ▸ hz)
    have hreg : CircleIntegrable h 0 r :=
      ContinuousOn.circleIntegrable hr.le (hcont.mono hsub)
    have hsum : CircleIntegrable (fun z : ℂ => ∑ i ∈ S, b i / (z - a i)) 0 r := by
      have hs := CircleIntegrable.sum S hpole
      rwa [show (∑ i ∈ S, fun z : ℂ => b i / (z - a i))
          = fun z : ℂ => ∑ i ∈ S, b i / (z - a i) from
        funext fun z => Finset.sum_apply z S _] at hs
    rw [circleIntegral.integral_congr hr.le heq,
      circleIntegral.integral_add hreg hsum,
      circleIntegral_finset_sum S _ 0 r hpole]
    refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
    rw [show (fun z : ℂ => b i / (z - a i)) = fun z : ℂ => b i • (z - a i)⁻¹ from
      funext fun z => by rw [smul_eq_mul, div_eq_mul_inv], circleIntegral.integral_smul,
      smul_eq_mul]
  rw [split R hR0 hsphereR (fun i hi => ne_of_lt (hin i hi).2) hgR,
    split ρ hρ hsphereρ (fun i hi => ne_of_gt (hin i hi).1) hgρ,
    Complex.circleIntegral_eq_of_differentiable_on_annulus_off_countable hρ hρR
      Set.countable_empty hcont (fun z hz => hdiff z hz.1)]
  have houter : ∀ i ∈ S, b i * (∮ z in C(0, R), (z - a i)⁻¹) = b i * (2 * π * I) :=
    fun i hi => by rw [circleIntegral_sub_inv_of_gt (hin i hi).2]
  have hinner : ∀ i ∈ S, b i * (∮ z in C(0, ρ), (z - a i)⁻¹) = 0 :=
    fun i hi => by
      rw [circleIntegral_sub_inv_of_lt hρ.le (by simpa using (hin i hi).1), mul_zero]
  rw [Finset.sum_congr rfl houter, Finset.sum_congr rfl hinner, Finset.sum_const_zero,
    ← Finset.sum_mul]
  ring

/-! ### Poles of order two

A merged pair of nodes is a **double** pole, and the deformation formula survives it unchanged: the
`(z - a)^{-2}` part of a principal part integrates to zero around every circle, so only the residue
— the `(z - a)^{-1}` coefficient — is visible to the contour.  This is what lets a collision be
handled without splitting into cases on whether the nodes coincide.
-/

/-- The `(z - a)^{-2}` term is invisible to a circle integral, wherever the pole sits. -/
theorem circleIntegral_sub_sq_inv (a c : ℂ) (r : ℝ) :
    (∮ z in C(c, r), ((z - a) ^ 2)⁻¹) = 0 := by
  have hfun : (fun z : ℂ => ((z - a) ^ 2)⁻¹) = fun z : ℂ => (z - a) ^ (-2 : ℤ) := by
    funext z
    rw [zpow_neg, zpow_two, pow_two]
  calc (∮ z in C(c, r), ((z - a) ^ 2)⁻¹)
      = ∮ z in C(c, r), (z - a) ^ (-2 : ℤ) := by rw [hfun]
    _ = 0 := circleIntegral.integral_sub_zpow_of_ne (by decide) c a r

/-- **The order-two Laurent decomposition.**  If `F` is holomorphic on a neighborhood `s` of `ζ`,
then away from `ζ` the quotient `F z / (z - ζ)^2` splits as

  `F ζ / (z - ζ)^2  +  F' ζ / (z - ζ)  +  G z`,   `G = dslope (dslope F ζ) ζ` holomorphic on `s`.

This is the principal part at a pole of order at most two, in exactly the shape
`circleIntegral_deform_double_poles` consumes: `d = F ζ` is the second-order coefficient and
`b = F' ζ` is the **residue** — which is why only `F' ζ` survives the deformation.

Iterating `dslope` twice is what makes both coefficients explicit *and* the remainder holomorphic in
one step, with `Complex.differentiableOn_dslope` supplying holomorphy at each stage.  No Taylor
series and no series manipulation enter: `sub_smul_dslope` is an identity valid at every point,
including `ζ` itself, so there is no puncture to argue around. -/
theorem eq_principalPart_two {F : ℂ → ℂ} {s : Set ℂ} {ζ : ℂ} (hs : s ∈ 𝓝 ζ)
    (hF : DifferentiableOn ℂ F s) :
    DifferentiableOn ℂ (dslope (dslope F ζ) ζ) s ∧
      ∀ z ∈ s, z ≠ ζ →
        F z / (z - ζ) ^ 2
          = F ζ * ((z - ζ) ^ 2)⁻¹ + deriv F ζ / (z - ζ) + dslope (dslope F ζ) ζ z := by
  refine ⟨(Complex.differentiableOn_dslope hs).mpr
    ((Complex.differentiableOn_dslope hs).mpr hF), fun z _ hne => ?_⟩
  have hzζ : z - ζ ≠ 0 := sub_ne_zero.mpr hne
  have h1 : (z - ζ) * dslope F ζ z = F z - F ζ := by
    simpa [smul_eq_mul] using sub_smul_dslope F ζ z
  have h2 : (z - ζ) * dslope (dslope F ζ) ζ z = dslope F ζ z - dslope F ζ ζ := by
    simpa [smul_eq_mul] using sub_smul_dslope (dslope F ζ) ζ z
  rw [dslope_same F ζ] at h2
  have hFz : F z = F ζ + (z - ζ) * deriv F ζ + (z - ζ) ^ 2 * dslope (dslope F ζ) ζ z := by
    have hd : dslope F ζ z = deriv F ζ + (z - ζ) * dslope (dslope F ζ) ζ z := by
      linear_combination -h2
    linear_combination -h1 + (z - ζ) * hd
  rw [hFz]
  field_simp

/-- **The deformation formula at poles of order at most two.**  Only the residues appear: the
second-order part of each principal part contributes nothing, by `circleIntegral_sub_sq_inv`. -/
theorem circleIntegral_deform_double_poles {ι : Type*}
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) {g h : ℂ → ℂ}
    (S : Finset ι) (a : ι → ℂ) (b d : ι → ℂ)
    (hin : ∀ i ∈ S, ρ < ‖a i‖ ∧ ‖a i‖ < R)
    (hcont : ContinuousOn h (closedBall 0 R \ ball 0 ρ))
    (hdiff : ∀ z ∈ ball (0 : ℂ) R \ closedBall 0 ρ, DifferentiableAt ℂ h z)
    (hgR : EqOn g (fun z => h z + ∑ i ∈ S, (b i / (z - a i) + d i * ((z - a i) ^ 2)⁻¹))
      (sphere 0 R))
    (hgρ : EqOn g (fun z => h z + ∑ i ∈ S, (b i / (z - a i) + d i * ((z - a i) ^ 2)⁻¹))
      (sphere 0 ρ)) :
    (∮ z in C(0, R), g z) = (∮ z in C(0, ρ), g z) + 2 * π * I * ∑ i ∈ S, b i := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le hρ hρR
  -- on each sphere, the second-order tail integrates to zero, so the integral is
  -- the simple-pole one
  have key : ∀ r : ℝ, 0 < r → (∀ i ∈ S, ‖a i‖ ≠ r) →
      EqOn g (fun z => h z + ∑ i ∈ S, (b i / (z - a i) + d i * ((z - a i) ^ 2)⁻¹))
        (sphere 0 r) →
      ContinuousOn h (sphere 0 r) →
      (∮ z in C(0, r), g z)
        = (∮ z in C(0, r), (h z + ∑ i ∈ S, b i / (z - a i))) := by
    intro r hr hmiss heq hhc
    have hne : ∀ i ∈ S, ∀ z ∈ sphere (0 : ℂ) r, z - a i ≠ 0 := by
      intro i hi z hz hzero
      rw [sub_eq_zero] at hzero
      rw [mem_sphere, dist_zero_right] at hz
      exact hmiss i hi (hzero ▸ hz)
    have hsimple : ∀ i ∈ S, CircleIntegrable (fun z => b i / (z - a i)) 0 r := fun i hi =>
      ContinuousOn.circleIntegrable hr.le
        (continuousOn_const.div (continuousOn_id.sub continuousOn_const) (hne i hi))
    -- the full principal part of one pole, kept as a single lambda so the sums stay pointwise
    have hterm : ∀ i ∈ S, CircleIntegrable
        (fun z => b i / (z - a i) + d i * ((z - a i) ^ 2)⁻¹) 0 r := fun i hi =>
      ContinuousOn.circleIntegrable hr.le
        ((continuousOn_const.div (continuousOn_id.sub continuousOn_const) (hne i hi)).add
          (continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).pow 2).inv₀
            fun z hz => pow_ne_zero 2 (hne i hi z hz))))
    have hsq : ∀ i ∈ S, CircleIntegrable (fun z => d i * ((z - a i) ^ 2)⁻¹) 0 r := fun i hi =>
      ContinuousOn.circleIntegrable hr.le
        (continuousOn_const.mul (((continuousOn_id.sub continuousOn_const).pow 2).inv₀
          fun z hz => pow_ne_zero 2 (hne i hi z hz)))
    have hsumS : CircleIntegrable
        (fun z : ℂ => ∑ i ∈ S, (b i / (z - a i) + d i * ((z - a i) ^ 2)⁻¹)) 0 r := by
      have hs := CircleIntegrable.sum S hterm
      rwa [show (∑ i ∈ S, fun z : ℂ => b i / (z - a i) + d i * ((z - a i) ^ 2)⁻¹)
          = fun z : ℂ => ∑ i ∈ S, (b i / (z - a i) + d i * ((z - a i) ^ 2)⁻¹) from
        funext fun z => Finset.sum_apply z S _] at hs
    have hsumB : CircleIntegrable (fun z : ℂ => ∑ i ∈ S, b i / (z - a i)) 0 r := by
      have hs := CircleIntegrable.sum S hsimple
      rwa [show (∑ i ∈ S, fun z : ℂ => b i / (z - a i))
          = fun z : ℂ => ∑ i ∈ S, b i / (z - a i) from
        funext fun z => Finset.sum_apply z S _] at hs
    have hh : CircleIntegrable h 0 r := ContinuousOn.circleIntegrable hr.le hhc
    rw [circleIntegral.integral_congr hr.le heq, circleIntegral.integral_add hh hsumS,
      circleIntegral.integral_add hh hsumB]
    congr 1
    -- the two polar sums differ by the second-order tail, whose integral vanishes termwise
    rw [circleIntegral_finset_sum S (fun i z => b i / (z - a i) + d i * ((z - a i) ^ 2)⁻¹)
        0 r hterm,
      circleIntegral_finset_sum S (fun i z => b i / (z - a i)) 0 r hsimple]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [circleIntegral.integral_add (hsimple i hi) (hsq i hi),
      show (fun z : ℂ => d i * ((z - a i) ^ 2)⁻¹) = fun z : ℂ => d i • ((z - a i) ^ 2)⁻¹ from
        funext fun z => by rw [smul_eq_mul], circleIntegral.integral_smul,
      circleIntegral_sub_sq_inv, smul_zero, add_zero]
  have hsphereR : ContinuousOn h (sphere 0 R) := hcont.mono fun z hz => by
    rw [mem_sphere, dist_zero_right] at hz
    exact ⟨by simp [mem_closedBall, dist_zero_right, hz],
      by simp [mem_ball, dist_zero_right, hz, not_lt.mpr hρR]⟩
  have hsphereρ : ContinuousOn h (sphere 0 ρ) := hcont.mono fun z hz => by
    rw [mem_sphere, dist_zero_right] at hz
    exact ⟨by simp [mem_closedBall, dist_zero_right, hz, hρR],
      by simp [mem_ball, dist_zero_right, hz]⟩
  rw [key R hR0 (fun i hi => ne_of_lt (hin i hi).2) hgR hsphereR,
    key ρ hρ (fun i hi => ne_of_gt (hin i hi).1) hgρ hsphereρ]
  exact circleIntegral_deform_simple_poles hρ hρR S a b hin hcont hdiff
    (fun z _ => rfl) (fun z _ => rfl)

/-- Subtracting the principal part of a simple pole leaves a function that
extends holomorphically across it.  `b` is the residue, in the form
`b = lim_{z → a} (z - a) g(z)` that says exactly "simple pole with residue `b`". -/
theorem differentiableOn_update_sub_principalPart {U : Set ℂ} {a b : ℂ} {g : ℂ → ℂ}
    (hU : U ∈ 𝓝 a) (hg : DifferentiableOn ℂ g (U \ {a}))
    (hres : Tendsto (fun z => (z - a) * g z) (𝓝[≠] a) (𝓝 b)) :
    DifferentiableOn ℂ (Function.update (fun z => g z - b / (z - a)) a
      (limUnder (𝓝[≠] a) (fun z => g z - b / (z - a)))) U := by
  have hpp : DifferentiableOn ℂ (fun z : ℂ => b / (z - a)) (U \ {a}) := by
    intro z hz
    have hz' : z - a ≠ 0 := sub_ne_zero.mpr (by simpa using hz.2)
    exact ((differentiableAt_const b).div
      ((differentiableAt_id).sub (differentiableAt_const a)) hz').differentiableWithinAt
  have hdiff : DifferentiableOn ℂ (fun z => g z - b / (z - a)) (U \ {a}) := hg.sub hpp
  refine Complex.differentiableOn_update_limUnder_of_isLittleO hU hdiff ?_
  have hkey : Tendsto
      (fun z => ((fun y => g y - b / (y - a)) z - (g a - b / (a - a))) / (z - a)⁻¹)
      (𝓝[≠] a) (𝓝 0) := by
    have hrw : ∀ᶠ z in 𝓝[≠] a,
        ((fun y => g y - b / (y - a)) z - (g a - b / (a - a))) / (z - a)⁻¹
          = ((z - a) * g z - b) - (z - a) * (g a - b / (a - a)) := by
      filter_upwards [self_mem_nhdsWithin] with z hz
      have hz' : z - a ≠ 0 := sub_ne_zero.mpr hz
      field_simp
    rw [Filter.tendsto_congr' hrw]
    have h1 : Tendsto (fun z => (z - a) * g z - b) (𝓝[≠] a) (𝓝 0) := by
      simpa using hres.sub (tendsto_const_nhds (x := b))
    have h2 : Tendsto (fun z : ℂ => (z - a) * (g a - b / (a - a))) (𝓝[≠] a) (𝓝 0) := by
      have hz0 : Tendsto (fun z : ℂ => z - a) (𝓝[≠] a) (𝓝 0) := by
        have h : Tendsto (fun z : ℂ => z - a) (𝓝 a) (𝓝 0) := by
          simpa using (continuous_sub_right a).tendsto a
        exact h.mono_left nhdsWithin_le_nhds
      simpa using hz0.mul_const (g a - b / (a - a))
    simpa using h1.sub h2
  refine (Asymptotics.isLittleO_iff_tendsto' ?_).2 hkey
  filter_upwards [self_mem_nhdsWithin] with z hz
  intro hcontra
  exact absurd (inv_eq_zero.mp hcontra) (sub_ne_zero.mpr hz)

open scoped Classical in
/-- `g` minus every principal part, with the removable singularity at each pole
filled in by its limit. -/
noncomputable def regularPart {ι : Type*} (g : ℂ → ℂ) (S : Finset ι) (a b : ι → ℂ) : ℂ → ℂ :=
  fun z => if z ∈ a '' (S : Set ι)
    then limUnder (𝓝[≠] z) (fun y => g y - ∑ i ∈ S, b i / (y - a i))
    else g z - ∑ i ∈ S, b i / (z - a i)

theorem regularPart_of_notMem {ι : Type*} {g : ℂ → ℂ} {S : Finset ι} {a b : ι → ℂ} {z : ℂ}
    (hz : z ∉ a '' (S : Set ι)) :
    regularPart g S a b z = g z - ∑ i ∈ S, b i / (z - a i) := by
  simp [regularPart, hz]

theorem regularPart_at_pole {ι : Type*} {g : ℂ → ℂ} {S : Finset ι} {a b : ι → ℂ} {z : ℂ}
    (hz : z ∈ a '' (S : Set ι)) :
    regularPart g S a b z = limUnder (𝓝[≠] z) (fun y => g y - ∑ i ∈ S, b i / (y - a i)) := by
  simp [regularPart, hz]

/-- **The regular part is regular.**  On an open set carrying finitely many
distinct simple poles of `g`, `regularPart` is differentiable everywhere,
including at the poles themselves. -/
theorem differentiableAt_regularPart {ι : Type*} [DecidableEq ι] {g : ℂ → ℂ} {S : Finset ι}
    {a b : ι → ℂ} {U : Set ℂ} (hU : IsOpen U) (hinj : Set.InjOn a (S : Set ι))
    (hmem : ∀ i ∈ S, a i ∈ U)
    (hg : DifferentiableOn ℂ g (U \ a '' (S : Set ι)))
    (hres : ∀ i ∈ S, Tendsto (fun z => (z - a i) * g z) (𝓝[≠] (a i)) (𝓝 (b i)))
    {z : ℂ} (hz : z ∈ U) : DifferentiableAt ℂ (regularPart g S a b) z := by
  have hfin : (a '' (S : Set ι)).Finite := (S.finite_toSet).image a
  by_cases hpole : z ∈ a '' (S : Set ι)
  · -- At a pole: peel off its principal part and apply removability.
    obtain ⟨i, hiS, rfl⟩ := hpole
    have hiS' : i ∈ S := hiS
    set T : Finset ι := S.erase i with hT
    have hfinT : (a '' (T : Set ι)).Finite := (T.finite_toSet).image a
    set V : Set ℂ := U \ a '' (T : Set ι) with hV
    have hVopen : IsOpen V := hU.sdiff hfinT.isClosed
    have haiV : a i ∈ V := by
      refine ⟨hmem i hiS', ?_⟩
      rintro ⟨j, hj, hji⟩
      rw [hT, Finset.coe_erase] at hj
      have hjS : j ∈ (S : Set ι) := hj.1
      have : j = i := hinj hjS (by simpa using hiS') hji
      exact hj.2 this
    have hVnhds : V ∈ 𝓝 (a i) := hVopen.mem_nhds haiV
    -- the other principal parts are regular on `V`
    have hother : ∀ w ∈ V, ∀ j ∈ T, w - a j ≠ 0 := by
      intro w hw j hj hzero
      exact hw.2 ⟨j, by simpa using hj, (sub_eq_zero.mp hzero).symm⟩
    set G : ℂ → ℂ := fun y => g y - ∑ j ∈ T, b j / (y - a j) with hG
    have hppT : DifferentiableOn ℂ (fun y : ℂ => ∑ j ∈ T, b j / (y - a j)) V := by
      refine DifferentiableOn.fun_sum fun j hj => ?_
      intro w hw
      exact ((differentiableAt_const (b j)).div
        (differentiableAt_id.sub (differentiableAt_const (a j)))
        (hother w hw j hj)).differentiableWithinAt
    have hGdiff : DifferentiableOn ℂ G (V \ {a i}) := by
      refine DifferentiableOn.sub (hg.mono ?_) (hppT.mono Set.sdiff_subset)
      rintro w ⟨hwV, hwne⟩
      refine ⟨hwV.1, ?_⟩
      rintro ⟨j, hj, hjw⟩
      by_cases hji : j = i
      · exact hwne (by simpa [hji] using hjw.symm)
      · refine hwV.2 ⟨j, ?_, hjw⟩
        rw [hT, Finset.coe_erase]
        exact ⟨hj, hji⟩
    have hGres : Tendsto (fun y => (y - a i) * G y) (𝓝[≠] (a i)) (𝓝 (b i)) := by
      have hzero : Tendsto (fun y : ℂ => (y - a i) * ∑ j ∈ T, b j / (y - a j))
          (𝓝[≠] (a i)) (𝓝 0) := by
        have hc : ContinuousAt (fun y : ℂ => ∑ j ∈ T, b j / (y - a j)) (a i) :=
          (hppT.differentiableAt hVnhds).continuousAt
        have hz0 : Tendsto (fun y : ℂ => y - a i) (𝓝[≠] (a i)) (𝓝 0) := by
          have h : Tendsto (fun y : ℂ => y - a i) (𝓝 (a i)) (𝓝 0) := by
            simpa using (continuous_sub_right (a i)).tendsto (a i)
          exact h.mono_left nhdsWithin_le_nhds
        simpa using hz0.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
      have := (hres i hiS').sub hzero
      simpa [hG, mul_sub] using this
    have hupd := differentiableOn_update_sub_principalPart hVnhds hGdiff hGres
    -- `G - b i/(· - a i)` is `g` minus every principal part
    have hsplit : (fun y : ℂ => G y - b i / (y - a i))
        = fun y : ℂ => g y - ∑ j ∈ S, b j / (y - a j) := by
      funext y
      rw [hG, ← Finset.add_sum_erase S (fun j => b j / (y - a j)) hiS']
      ring
    rw [hsplit] at hupd
    -- `regularPart` agrees with that update on `V`
    have hagree : Set.EqOn (regularPart g S a b)
        (Function.update (fun y : ℂ => g y - ∑ j ∈ S, b j / (y - a j)) (a i)
          (limUnder (𝓝[≠] (a i)) (fun y : ℂ => g y - ∑ j ∈ S, b j / (y - a j)))) V := by
      intro w hw
      by_cases hwi : w = a i
      · subst hwi
        rw [regularPart_at_pole ⟨i, by simpa using hiS', rfl⟩, Function.update_self]
      · have hwnot : w ∉ a '' (S : Set ι) := by
          rintro ⟨j, hj, hjw⟩
          by_cases hji : j = i
          · exact hwi (by simpa [hji] using hjw.symm)
          · refine hw.2 ⟨j, ?_, hjw⟩
            rw [hT, Finset.coe_erase]
            exact ⟨hj, hji⟩
        rw [regularPart_of_notMem hwnot, Function.update_of_ne hwi]
    exact ((hupd.differentiableAt hVnhds).congr_of_eventuallyEq
      (Filter.eventuallyEq_of_mem hVnhds hagree)).congr_of_eventuallyEq
      (Filter.EventuallyEq.refl _ _) |>.congr_of_eventuallyEq (Filter.EventuallyEq.refl _ _)
  · -- Away from the poles `regularPart` is `g` minus the principal parts.
    set W : Set ℂ := U \ a '' (S : Set ι) with hW
    have hWopen : IsOpen W := hU.sdiff hfin.isClosed
    have hzW : z ∈ W := ⟨hz, hpole⟩
    have hWnhds : W ∈ 𝓝 z := hWopen.mem_nhds hzW
    have hne : ∀ w ∈ W, ∀ j ∈ S, w - a j ≠ 0 := by
      intro w hw j hj hzero
      exact hw.2 ⟨j, by simpa using hj, (sub_eq_zero.mp hzero).symm⟩
    have hpp : DifferentiableOn ℂ (fun y : ℂ => ∑ j ∈ S, b j / (y - a j)) W := by
      refine DifferentiableOn.fun_sum fun j hj => ?_
      intro w hw
      exact ((differentiableAt_const (b j)).div
        (differentiableAt_id.sub (differentiableAt_const (a j)))
        (hne w hw j hj)).differentiableWithinAt
    have hdiff : DifferentiableOn ℂ (fun y : ℂ => g y - ∑ j ∈ S, b j / (y - a j)) W :=
      (hg.mono (by rw [hW])).sub hpp
    refine (hdiff.differentiableAt hWnhds).congr_of_eventuallyEq ?_
    filter_upwards [hWnhds] with w hw
    exact regularPart_of_notMem hw.2

/-- **Deforming past a cluster of simple poles**, in the form a caller can actually discharge: `g`
is regular on the closed annulus apart from finitely
many distinct simple poles `a_i` lying strictly inside it, with residues `b_i`
in the form `b_i = lim_{z → a_i} (z - a_i) g(z)`.  Then
\[
  \oint_{|z|=R}g-\oint_{|z|=\rho}g=2\pi i\sum_i b_i .
\]
The regular part is built here rather than assumed: `regularPart` subtracts every
principal part and fills in the removable singularities. -/
theorem circleIntegral_deform_of_simplePoles {ι : Type*} [DecidableEq ι]
    {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R) {g : ℂ → ℂ}
    (S : Finset ι) (a b : ι → ℂ) (hinj : Set.InjOn a (S : Set ι))
    (hin : ∀ i ∈ S, ρ < ‖a i‖ ∧ ‖a i‖ < R)
    (hcont : ContinuousOn g ((closedBall 0 R \ ball 0 ρ) \ a '' (S : Set ι)))
    (hdiff : DifferentiableOn ℂ g ((ball 0 R \ closedBall 0 ρ) \ a '' (S : Set ι)))
    (hres : ∀ i ∈ S, Tendsto (fun z => (z - a i) * g z) (𝓝[≠] (a i)) (𝓝 (b i))) :
    (∮ z in C(0, R), g z) = (∮ z in C(0, ρ), g z) + 2 * π * I * ∑ i ∈ S, b i := by
  set P : Set ℂ := a '' (S : Set ι) with hP
  have hPfin : P.Finite := (S.finite_toSet).image a
  set U : Set ℂ := ball 0 R \ closedBall 0 ρ with hU
  have hUopen : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  have hmemU : ∀ i ∈ S, a i ∈ U := by
    intro i hi
    refine ⟨?_, ?_⟩
    · simpa [mem_ball, dist_zero_right] using (hin i hi).2
    · simpa [mem_closedBall, dist_zero_right] using not_le.mpr (hin i hi).1
  have hPU : P ⊆ U := by rintro _ ⟨i, hi, rfl⟩; exact hmemU i (by simpa using hi)
  -- the principal parts are continuous away from the poles
  have hppAt : ∀ z ∉ P, ContinuousAt (fun w : ℂ => ∑ i ∈ S, b i / (w - a i)) z := by
    intro z hz
    refine tendsto_finsetSum S fun i hi => ?_
    have hne : z - a i ≠ 0 := fun hzero => hz ⟨i, by simpa using hi, (sub_eq_zero.mp hzero).symm⟩
    exact continuousAt_const.div (continuousAt_id.sub continuousAt_const) hne
  -- the regular part is continuous on the closed annulus
  have hHcont : ContinuousOn (regularPart g S a b) (closedBall 0 R \ ball 0 ρ) := by
    intro z hz
    by_cases hzU : z ∈ U
    · exact (differentiableAt_regularPart hUopen hinj hmemU hdiff hres hzU).continuousAt
        |>.continuousWithinAt
    · have hzP : z ∉ P := fun h => hzU (hPU h)
      have hnb : (closedBall (0 : ℂ) R \ ball 0 ρ) \ P ∈ 𝓝[closedBall (0 : ℂ) R \ ball 0 ρ] z :=
        Filter.inter_mem self_mem_nhdsWithin
          (mem_nhdsWithin_of_mem_nhds (hPfin.isClosed.isOpen_compl.mem_nhds hzP))
      have hbase : ContinuousWithinAt (fun w : ℂ => g w - ∑ i ∈ S, b i / (w - a i))
          ((closedBall 0 R \ ball 0 ρ) \ P) z :=
        (hcont z ⟨hz, hzP⟩).sub (hppAt z hzP).continuousWithinAt
      have hcongr : ContinuousWithinAt (regularPart g S a b)
          ((closedBall 0 R \ ball 0 ρ) \ P) z :=
        hbase.congr (fun w hw => regularPart_of_notMem hw.2) (regularPart_of_notMem hzP)
      exact hcongr.mono_of_mem_nhdsWithin hnb
  -- and differentiable in the interior
  have hHdiff : ∀ z ∈ ball (0 : ℂ) R \ closedBall 0 ρ,
      DifferentiableAt ℂ (regularPart g S a b) z :=
    fun z hz => differentiableAt_regularPart hUopen hinj hmemU hdiff hres hz
  -- on either circle the poles are absent, so the split is an identity
  have hsphere : ∀ r : ℝ, (∀ i ∈ S, ‖a i‖ ≠ r) →
      EqOn g (fun z => regularPart g S a b z + ∑ i ∈ S, b i / (z - a i)) (sphere 0 r) := by
    intro r hr z hz
    have hzn : ‖z‖ = r := by simpa [Complex.dist_eq] using hz
    have hzP : z ∉ P := by
      rintro ⟨i, hi, rfl⟩
      exact hr i (by simpa using hi) hzn
    change g z = regularPart g S a b z + ∑ i ∈ S, b i / (z - a i)
    rw [regularPart_of_notMem hzP]
    ring
  exact circleIntegral_deform_simple_poles hρ hρR S a b hin hHcont hHdiff
    (hsphere R fun i hi => ne_of_lt (hin i hi).2)
    (hsphere ρ fun i hi => ne_of_gt (hin i hi).1)

/-- **Deforming past a single pole of order at most two, presented as a quotient.**  Near `ζ` the
integrand is `F z / (z - ζ)^2` with `F` holomorphic; elsewhere in the annulus it is holomorphic.
Then the deformation picks up `2πi F'(ζ)`.

This is the order-two counterpart of `circleIntegral_deform_of_simplePoles`, and it is shorter for
a reason worth stating: the regular part is not *searched for* as a removable-singularity limit but
*given*, as the twice-iterated `dslope` of `eq_principalPart_two`.  The only patching left is at
`ζ` itself, and `Function.update` does it in one step.

A simple pole is the case `F ζ = 0`: then `F z / (z - ζ)^2 = (F z / (z - ζ)) / (z - ζ)` has
residue `F'(ζ)` all the same, so the hypothesis covers both orders without a case split.  That is
what makes this the form a cluster of poles with one merged pair is read through. -/
theorem circleIntegral_deform_double_pole_of_quotient {ρ R : ℝ} (hρ : 0 < ρ) (hρR : ρ ≤ R)
    {g F : ℂ → ℂ} {ζ : ℂ} {s : Set ℂ} (hso : IsOpen s) (hζs : ζ ∈ s)
    (hin : ρ < ‖ζ‖) (hout : ‖ζ‖ < R)
    (hF : DifferentiableOn ℂ F s)
    (hgs : ∀ t ∈ s, t ≠ ζ → g t = F t / (t - ζ) ^ 2)
    (hcont : ContinuousOn g ((closedBall 0 R \ ball 0 ρ) \ {ζ}))
    (hdiff : ∀ t ∈ ball (0 : ℂ) R \ closedBall (0 : ℂ) ρ, t ≠ ζ → DifferentiableAt ℂ g t) :
    (∮ z in C(0, R), g z) = (∮ z in C(0, ρ), g z) + 2 * π * I * deriv F ζ := by
  set b : ℂ := deriv F ζ with hb
  set d : ℂ := F ζ with hd
  set G : ℂ → ℂ := dslope (dslope F ζ) ζ with hG
  set P : ℂ → ℂ := fun t => b / (t - ζ) + d * ((t - ζ) ^ 2)⁻¹ with hP
  obtain ⟨hGdiff, hsplit⟩ := eq_principalPart_two (hso.mem_nhds hζs) hF
  set h : ℂ → ℂ := Function.update (fun t => g t - P t) ζ (G ζ) with hh
  -- `h` is the regular part: it agrees with `G` on `s` and with `g - P` off `ζ`.
  have hhne : ∀ t : ℂ, t ≠ ζ → h t = g t - P t := fun t ht => Function.update_of_ne ht _ _
  have hhs : ∀ t ∈ s, h t = G t := by
    intro t ht
    rcases eq_or_ne t ζ with rfl | hne
    · rw [hh, Function.update_self]
    · rw [hhne t hne, hgs t ht hne, hsplit t ht hne, hP]; ring
  have hGcont : ∀ t ∈ s, ContinuousAt G t := fun t ht =>
    (hGdiff.differentiableAt (hso.mem_nhds ht)).continuousAt
  have hPdiff : ∀ t : ℂ, t ≠ ζ → DifferentiableAt ℂ P t := by
    intro t ht
    have htζ : t - ζ ≠ 0 := sub_ne_zero.mpr ht
    exact ((differentiableAt_const b).div
      (differentiableAt_id.sub (differentiableAt_const ζ)) htζ).add
      ((differentiableAt_const d).mul
        (((differentiableAt_id.sub (differentiableAt_const ζ)).pow 2).inv
          (pow_ne_zero 2 htζ)))
  -- Off `s` the point is not `ζ`, so `h` is `g - P` on a whole neighborhood.
  have hEqOff : ∀ t : ℂ, t ∉ s → h =ᶠ[𝓝 t] fun y => g y - P y := by
    intro t hts
    have htζ : t ≠ ζ := fun hc => hts (hc ▸ hζs)
    filter_upwards [isOpen_compl_singleton.mem_nhds (by simpa using htζ)] with y hy
    exact hhne y (by simpa using hy)
  have hEqOn : ∀ t ∈ s, h =ᶠ[𝓝 t] G :=
    fun t ht => Filter.eventuallyEq_of_mem (hso.mem_nhds ht) hhs
  have hhcont : ContinuousOn h (closedBall 0 R \ ball 0 ρ) := by
    intro z hz
    by_cases hzs : z ∈ s
    · exact ((hGcont z hzs).congr (hEqOn z hzs).symm).continuousWithinAt
    · have hzζ : z ≠ ζ := fun hc => hzs (hc ▸ hζs)
      have hmem : (closedBall (0 : ℂ) R \ ball 0 ρ) \ {ζ} ∈ 𝓝[closedBall 0 R \ ball 0 ρ] z :=
        inter_mem_nhdsWithin _ (isOpen_compl_singleton.mem_nhds (by simpa using hzζ))
      refine ContinuousWithinAt.mono_of_mem_nhdsWithin ?_ hmem
      refine ContinuousWithinAt.congr
        ((hcont z ⟨hz, by simpa using hzζ⟩).sub
          ((hPdiff z hzζ).continuousAt.continuousWithinAt))
        (fun y hy => hhne y (by simpa using hy.2)) (hhne z hzζ)
  have hhdiff : ∀ z ∈ ball (0 : ℂ) R \ closedBall (0 : ℂ) ρ, DifferentiableAt ℂ h z := by
    intro z hz
    by_cases hzs : z ∈ s
    · exact ((hGdiff.differentiableAt (hso.mem_nhds hzs)).congr_of_eventuallyEq
        (hEqOn z hzs))
    · have hzζ : z ≠ ζ := fun hc => hzs (hc ▸ hζs)
      exact (((hdiff z hz hzζ).sub (hPdiff z hzζ)).congr_of_eventuallyEq (hEqOff z hzs))
  have hsphere : ∀ r : ℝ, ‖ζ‖ ≠ r →
      EqOn g (fun z => h z + ∑ _i ∈ ({()} : Finset Unit),
        (b / (z - ζ) + d * ((z - ζ) ^ 2)⁻¹)) (sphere 0 r) := by
    intro r hr z hz
    rw [mem_sphere, dist_zero_right] at hz
    have hzζ : z ≠ ζ := fun hc => hr (by rw [← hc]; exact hz)
    change g z = h z + ∑ _i ∈ ({()} : Finset Unit), (b / (z - ζ) + d * ((z - ζ) ^ 2)⁻¹)
    rw [Finset.sum_const, Finset.card_singleton, one_smul, hhne z hzζ, hP]
    ring
  have hkey := circleIntegral_deform_double_poles (ι := Unit) hρ hρR ({()} : Finset Unit)
    (fun _ => ζ) (fun _ => b) (fun _ => d) (fun _ _ => ⟨hin, hout⟩) hhcont hhdiff
    (hsphere R (ne_of_lt hout)) (hsphere ρ (ne_of_gt hin))
  rw [hkey, Finset.sum_const, Finset.card_singleton, one_smul]

/-! ### Axiom footprint -/

/-- info: 'Shields.eq_principalPart_two' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms eq_principalPart_two

/-- info: 'Shields.circleIntegral_deform_double_pole_of_quotient' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms circleIntegral_deform_double_pole_of_quotient

end Shields
