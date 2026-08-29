/-
Copyright (c) 2026 Johnny Shields. All rights reserved.
Released under the MIT license as described in the file LICENSE.txt.
Authors: Johnny Shields
-/
import Shields.Analysis.Complex.GreenAnnulus
import Shields.Analysis.SpecialFunctions.PolarCoordAnnulus
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Group.Integral

/-!
# The delta at the pole of the logarithmic kernel

`CircleFlux.green_annulus_log` states Green's identity on an annulus tested against `log r`:
\[
  \int_\varepsilon^R \log s\Bigl(s\!\int_0^{2\pi}\!\Delta\varphi\,d\theta\Bigr)ds
    = \log R\,\Phi(R)-\log\varepsilon\,\Phi(\varepsilon)-2\pi\bigl(M(R)-M(\varepsilon)\bigr).
\]
This module takes the two limits: the logarithmic kernel has a point mass of weight `2π` at its
pole.

Both boundary terms are elementary once the identity is in hand.

* **Outside the support** the test function and its differential vanish identically, so `Φ(R)` and
  `M(R)` are zero for any `R` past it — the outer boundary contributes nothing, and no decay
  hypothesis is needed.
* **`log ε·Φ(ε) → 0`**, because `Φ(ε) = ε∫Dφ[e^{iθ}]dθ` carries a factor of the radius: the
  product is `(ε\log ε)` times a factor continuous at `0`, and `ε\log ε → 0`.  This is the only
  place the pole's strength enters, and it is why the logarithm is exactly the borderline kernel
  for which the mass is finite.
* **`M(ε) → φ(a)`**, because the circle average is differentiable in the radius, hence continuous,
  and its value at radius zero is the center value.

What is left is `2π M(ε) → 2π φ(a)`, which is the delta.

## Main results

* `fderiv_eq_zero_of_supp`, `circleFlux_eq_zero_of_supp`, `circleAverage_eq_zero_of_supp` — the
  outer boundary contributes nothing.
* `circleAverage_zero_radius` — the average at radius zero is the center value.
* `tendsto_log_mul_circleFlux` — **the inner boundary term vanishes**.
* `tendsto_circleAverage_nhdsGT` — the inner average converges to the center value.
* `riesz_delta_polar` — **the delta**, in the polar form `green_annulus_log` delivers.
* `integral_annulus_polar` — the annulus integral in polar form.
* `riesz_delta` — **the delta**, as an area integral.

## Tags

riesz measure, logarithmic potential, dirac delta, green identity, polar coordinates
-/

open scoped Real
open InnerProductSpace Complex Laplacian Filter Topology Real MeasureTheory Set

namespace Shields

variable {φ : ℂ → ℝ} {a : ℂ}

/-! ### Outside the support -/

/-- A function vanishing on a closed exterior has vanishing differential on the open one. -/
theorem fderiv_eq_zero_of_supp {S : ℝ} (hsupp : ∀ z : ℂ, S ≤ ‖z - a‖ → φ z = 0) {z : ℂ}
    (hz : S < ‖z - a‖) : fderiv ℝ φ z = 0 := by
  have hloc : φ =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
    filter_upwards [Metric.ball_mem_nhds z (sub_pos.mpr hz)] with w hw
    refine hsupp w ?_
    have hd : ‖z - w‖ < ‖z - a‖ - S := by
      rw [Metric.mem_ball, Complex.dist_eq] at hw
      rw [show z - w = -(w - z) from by ring, norm_neg]
      exact hw
    have : ‖z - a‖ ≤ ‖z - w‖ + ‖w - a‖ := by
      simpa using norm_sub_le_norm_sub_add_norm_sub z w a
    linarith
  rw [hloc.fderiv_eq]
  simp

theorem circleFlux_eq_zero_of_supp {S : ℝ} (hS : 0 < S)
    (hsupp : ∀ z : ℂ, S ≤ ‖z - a‖ → φ z = 0) {R : ℝ} (hR : S < R) : circleFlux φ a R = 0 := by
  have hz : ∀ θ : ℝ, fderiv ℝ φ (circleMap a R θ) (circleDir θ) = 0 := by
    intro θ
    have : S < ‖circleMap a R θ - a‖ := by
      rw [norm_circleMap_sub_center, abs_of_pos (lt_trans hS hR)]
      exact hR
    rw [fderiv_eq_zero_of_supp hsupp this]
    rfl
  simp [circleFlux, hz]

theorem circleAverage_eq_zero_of_supp {S : ℝ} (hS : 0 < S)
    (hsupp : ∀ z : ℂ, S ≤ ‖z - a‖ → φ z = 0) {R : ℝ} (hR : S < R) : circleAverage φ a R = 0 := by
  have hz : ∀ θ : ℝ, φ (circleMap a R θ) = 0 := by
    intro θ
    refine hsupp _ ?_
    rw [norm_circleMap_sub_center, abs_of_pos (lt_trans hS hR)]
    exact hR.le
  simp [circleAverage_def, hz]

/-! ### At radius zero -/

theorem circleAverage_zero_radius (φ : ℂ → ℝ) (a : ℂ) : circleAverage φ a 0 = φ a := by
  have h : ∀ θ : ℝ, φ (circleMap a 0 θ) = φ a := by
    intro θ
    rw [circleMap_eq_circleDir]
    norm_num
  rw [circleAverage_def, intervalIntegral.integral_congr (g := fun _ => φ a) fun θ _ => h θ]
  rw [intervalIntegral.integral_const, smul_eq_mul, smul_eq_mul]
  field

/-! ### The two limits -/

/-- **The inner boundary term vanishes.**  The flux carries a factor of the radius, so the product
with `log ε` is `ε\log ε` times a factor continuous at the origin. -/
theorem tendsto_log_mul_circleFlux (hφ : ContDiff ℝ 2 φ) (a : ℂ) :
    Tendsto (fun ε : ℝ => Real.log ε * circleFlux φ a ε) (𝓝[>] 0) (𝓝 0) := by
  have hfl : (fun ε : ℝ => Real.log ε * circleFlux φ a ε)
      = fun ε : ℝ => (ε * Real.log ε) *
          ∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ φ (circleMap a ε θ) (circleDir θ) := by
    funext ε
    rw [circleFlux]
    ring
  rw [hfl]
  have h1 : Tendsto (fun ε : ℝ => ε * Real.log ε) (𝓝[>] 0) (𝓝 0) := by
    have h := Real.continuous_mul_log.tendsto (0 : ℝ)
    simpa using h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun ε : ℝ => ∫ θ in (0 : ℝ)..(2 * π),
        fderiv ℝ φ (circleMap a ε θ) (circleDir θ)) (𝓝[>] 0)
      (𝓝 (∫ θ in (0 : ℝ)..(2 * π), fderiv ℝ φ (circleMap a 0 θ) (circleDir θ))) :=
    ((continuous_radialIntegral hφ a).tendsto 0).mono_left nhdsWithin_le_nhds
  simpa using h1.mul h2

/-- The circle average converges to the center value, being differentiable in the radius. -/
theorem tendsto_circleAverage_nhdsGT (hφ : ContDiff ℝ 2 φ) (a : ℂ) :
    Tendsto (fun ε : ℝ => circleAverage φ a ε) (𝓝[>] 0) (𝓝 (φ a)) := by
  have hcont : Continuous fun s : ℝ => circleAverage φ a s :=
    Differentiable.continuous fun s => (hasDerivAt_circleAverage hφ a s).differentiableAt
  have ht : Tendsto (fun s : ℝ => circleAverage φ a s) (𝓝 0)
      (𝓝 (circleAverage φ a 0)) := hcont.tendsto 0
  rw [circleAverage_zero_radius] at ht
  exact ht.mono_left nhdsWithin_le_nhds

/-! ### The delta -/

/-- **The logarithmic kernel has a point mass of weight `2π` at its pole.**  For a `C²` test
function vanishing outside a disk about `a`, the Laplacian integrated against `log` over the
annulus converges, as the inner radius shrinks, to `2π φ(a)`.

This is the identity `μ = (2π)^{-1}Δ𝒰` at a single pole, in the polar form
`green_annulus_log` delivers: the outer boundary contributes nothing because the
test function vanishes there, the inner flux term dies like `ε\log ε`, and what survives is the
circle average's limit, which is the center value. -/
theorem riesz_delta_polar (hφ : ContDiff ℝ 2 φ) (a : ℂ) {S : ℝ}
    (hsupp : ∀ z : ℂ, S ≤ ‖z - a‖ → φ z = 0) {R : ℝ} (hS : 0 < S) (hR : S < R) :
    Tendsto (fun ε : ℝ =>
        ∫ s in ε..R, Real.log s * (s * ∫ θ in (0 : ℝ)..(2 * π), Δ φ (circleMap a s θ)))
      (𝓝[>] 0) (𝓝 (2 * π * φ a)) := by
  have hRpos : (0 : ℝ) < R := lt_trans hS hR
  have hflux : circleFlux φ a R = 0 := circleFlux_eq_zero_of_supp hS hsupp hR
  have havg : circleAverage φ a R = 0 := circleAverage_eq_zero_of_supp hS hsupp hR
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (fun ε : ℝ => -(Real.log ε * circleFlux φ a ε) + 2 * π * circleAverage φ a ε) ε
        = ∫ s in ε..R, Real.log s * (s * ∫ θ in (0 : ℝ)..(2 * π), Δ φ (circleMap a s θ)) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hRpos)] with ε hε1 hε2
    rw [green_annulus_log hφ a hε1 (le_of_lt hε2), hflux, havg]
    ring
  refine Tendsto.congr' hev ?_
  have hA := tendsto_log_mul_circleFlux hφ a
  have hB := tendsto_circleAverage_nhdsGT hφ a
  simpa using hA.neg.add (hB.const_mul (2 * π))

/-! ### The change of variables -/

/-- **The area integral over an annulus, in polar form.**  Mathlib's polar change of variables
carries the Jacobian; what is added is the centering, the radius cut, and the `2π`-periodic shift
from the chart's angular range `(-π, π)` to the circle average's `(0, 2π)`. -/
theorem integral_annulus_polar {g : ℂ → ℝ} {a : ℂ} (hg : ContinuousOn g {z : ℂ | z ≠ a})
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ z in {z : ℂ | ε < ‖z - a‖ ∧ ‖z - a‖ < R}, g z)
      = ∫ s in ε..R, s * ∫ θ in (0 : ℝ)..(2 * π), g (circleMap a s θ) := by
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => a + Complex.polarCoord.symm p)
      ((Set.Icc ε R) ×ˢ (Set.Icc (-π) π)) {z : ℂ | z ≠ a} := by
    rintro ⟨r, θ⟩ ⟨hr, -⟩
    have hr0 : 0 < r := lt_of_lt_of_le hε hr.1
    have hn : ‖Complex.polarCoord.symm ((r, θ) : ℝ × ℝ)‖ = r :=
      norm_polarCoord_symm_of_pos hr0 θ
    refine fun hc => absurd hn ?_
    rw [show Complex.polarCoord.symm ((r, θ) : ℝ × ℝ) = 0 from by linear_combination hc]
    rw [norm_zero]
    exact ne_of_lt hr0
  have hcontF : ContinuousOn (fun p : ℝ × ℝ => p.1 • g (a + Complex.polarCoord.symm p))
      ((Set.Icc ε R) ×ˢ (Set.Icc (-π) π)) :=
    continuous_fst.continuousOn.smul
      (hg.comp (continuous_const.add continuous_polarCoord_symm_complex).continuousOn hmaps)
  have hint : IntegrableOn (fun p : ℝ × ℝ => p.1 • g (a + Complex.polarCoord.symm p))
      ((Set.Ioo ε R) ×ˢ (Set.Ioo (-π) π)) (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (hcontF.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.Ioo_subset_Icc_self Set.Ioo_subset_Icc_self)
  have hfubini : (∫ p in (Set.Ioo ε R) ×ˢ (Set.Ioo (-π) π),
        p.1 • g (a + Complex.polarCoord.symm p))
      = ∫ r in Set.Ioo ε R, ∫ θ in Set.Ioo (-π) π,
          r • g (a + Complex.polarCoord.symm ((r, θ) : ℝ × ℝ)) := by
    rw [Measure.volume_eq_prod]
    exact setIntegral_prod _ hint
  have hinner : ∀ r : ℝ, (∫ θ in Set.Ioo (-π) π,
        r • g (a + Complex.polarCoord.symm ((r, θ) : ℝ × ℝ)))
      = r * ∫ θ in (0 : ℝ)..(2 * π), g (circleMap a r θ) := fun r => by
    rw [integral_smul, integral_Ioo_polarCoord_symm_eq_circleMap, smul_eq_mul]
  rw [setIntegral_annulus_polarCoord_symm g a hε, hfubini,
    setIntegral_congr_fun measurableSet_Ioo fun r _ => hinner r,
    intervalIntegral.integral_of_le hεR, integral_Ioc_eq_integral_Ioo]

/-! ### The delta as an area integral -/

/-- **The Riesz delta.**  For a `C²` test function vanishing outside a disk about `a`, the
Laplacian integrated against the logarithmic kernel over the annulus `ε < ‖z-a‖ < R` converges,
as the inner radius shrinks, to `2π φ(a)`.

This is `μ = (2π)^{-1}Δ𝒰` at a single pole, now stated as an area integral: the annulus is the
region on which the kernel is regular, and the mass it misses is exactly the point mass at the
pole. -/
theorem riesz_delta {φ : ℂ → ℝ} (hφ : ContDiff ℝ 2 φ) (a : ℂ) {S : ℝ}
    (hsupp : ∀ z : ℂ, S ≤ ‖z - a‖ → φ z = 0) {R : ℝ} (hS : 0 < S) (hR : S < R) :
    Tendsto (fun ε : ℝ =>
        ∫ z in {z : ℂ | ε < ‖z - a‖ ∧ ‖z - a‖ < R}, Real.log ‖z - a‖ * Δ φ z)
      (𝓝[>] 0) (𝓝 (2 * π * φ a)) := by
  have hRpos : (0 : ℝ) < R := lt_trans hS hR
  have hker : ContinuousOn (fun z : ℂ => Real.log ‖z - a‖ * Δ φ z) {z : ℂ | z ≠ a} := by
    refine ContinuousOn.mul ?_ (continuous_laplacian hφ).continuousOn
    refine Real.continuousOn_log.comp
      (continuous_id.sub continuous_const).norm.continuousOn fun z hz => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, norm_ne_zero_iff, ne_eq,
      sub_eq_zero]
    exact hz
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (fun ε : ℝ => ∫ s in ε..R,
          Real.log s * (s * ∫ θ in (0 : ℝ)..(2 * π), Δ φ (circleMap a s θ))) ε
        = ∫ z in {z : ℂ | ε < ‖z - a‖ ∧ ‖z - a‖ < R}, Real.log ‖z - a‖ * Δ φ z := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (gt_mem_nhds hRpos)] with ε hε1 hε2
    rw [integral_annulus_polar hker hε1 (le_of_lt hε2)]
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [Set.uIcc_of_le (le_of_lt hε2)] at hs
    have hs0 : 0 < s := lt_of_lt_of_le hε1 hs.1
    have hpt : ∀ θ : ℝ, Real.log ‖circleMap a s θ - a‖ * Δ φ (circleMap a s θ)
        = Real.log s * Δ φ (circleMap a s θ) := by
      intro θ
      rw [norm_circleMap_sub_center, abs_of_pos hs0]
    rw [intervalIntegral.integral_congr fun θ _ => hpt θ,
      intervalIntegral.integral_const_mul]
    ring
  exact Tendsto.congr' hev (riesz_delta_polar hφ a hsupp hS hR)


/-! ### Axiom footprint -/

/-- info: 'Shields.riesz_delta' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms riesz_delta

end Shields
